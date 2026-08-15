use crate::common::common::parse_query;
use crate::common::structs::custom_error::CustomError;
use crate::config::enums::cluster_mode::ClusterMode;
use crate::config::structs::http_trackers_config::HttpTrackersConfig;
use crate::http::structs::http_service_data::HttpServiceData;
use crate::http::types::{
    HttpServiceQueryHashingMapErr,
    HttpServiceQueryHashingMapOk
};
use crate::security::security::{
    validate_info_hash_hex,
    validate_peer_id_hex,
    validate_remote_ip
};
use crate::ssl::enums::server_identifier::ServerIdentifier;
use crate::ssl::structs::dynamic_certificate_resolver::DynamicCertificateResolver;
use crate::stats::enums::stats_event::StatsEvent;
use crate::tracker::enums::torrent_peers_type::TorrentPeersType;
use crate::tracker::structs::info_hash::InfoHash;
use crate::tracker::structs::torrent_tracker::TorrentTracker;
use crate::tracker::structs::user_id::UserId;
use crate::websocket::enums::protocol_type::ProtocolType;
use crate::websocket::enums::request_type::RequestType;
use crate::websocket::websocket::{
    create_cluster_error_response,
    forward_request
};
use actix_cors::Cors;
use actix_web::dev::ServerHandle;
use actix_web::http::header::ContentType;
use actix_web::web::{
    Data,
    ServiceConfig
};
use actix_web::{
    middleware::Compress,
    web,
    App,
    HttpRequest,
    HttpResponse,
    HttpServer
};
use bip_bencode::{
    ben_bytes,
    ben_int,
    ben_list,
    ben_map,
    BMutAccess
};
use log::{
    debug,
    error,
    info
};
use std::borrow::Cow;
use std::future::Future;
use std::net::{
    IpAddr,
    SocketAddr
};
use std::process::exit;
use std::str::FromStr;
use std::sync::{
    Arc,
    LazyLock
};
use std::time::Duration;

static ERR_MISSING_KEY: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Missing Key. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNKNOWN_INFO_HASH: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unknown info_hash. Thanks for DLing. By TBMovies.") }.encode());
static ERR_FORBIDDEN_INFO_HASH: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Forbidden info_hash. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNKNOWN_REQUEST: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unknown Request. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNABLE_DECODE_HEX: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unable to Decode HEX String. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNKNOWN_ORIGIN_IP: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unknown Origin IP. Thanks for DLing. By TBMovies.") }.encode());
static ERR_INVALID_KEY: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Invalid Key. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNKNOWN_KEY: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unknown Key. Thanks for DLing. By TBMovies.") }.encode());
static ERR_INVALID_USER_KEY: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Invalid User Key. Thanks for DLing. By TBMovies.") }.encode());
static ERR_UNKNOWN_USER_KEY: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Unknown User Key. Thanks for DLing. By TBMovies.") }.encode());
static ERR_CLIENT_BANNED: LazyLock<Vec<u8>> = LazyLock::new(|| ben_map!{ "failure reason" => ben_bytes!("Leeching-Only clients are banned. By TBMovies") }.encode());

/// Azureus-style peer_id client codes for leech-only / never-seed clients (Xunlei/Thunder,
/// QQDownload, BaiduNetdisk, Xfplay, Dalili, Toshare, Datatorrent, Happyplaylist). Matched as
/// the two bytes after the leading '-' in a `-XX####-` peer_id.
const BANNED_CLIENT_CODES: [&[u8; 2]; 9] = [b"XL", b"SD", b"XF", b"QD", b"BN", b"DL", b"TS", b"DT", b"HP"];

/// Lowercased User-Agent substrings for leech clients that spoof or omit a bannable peer_id.
const BANNED_USER_AGENTS: [&str; 7] = ["cacao_torrent", "gopeed dev", "rain 0.0.0", "taipei-torrent", "dt/torrent", "hp/torrent", "xm/torrent"];

/// Well-known, swarm-participating clients. Used ONLY to choose the announce warning message
/// (recognised clients get the seeding reminder; anything else gets the switch-client nudge).
/// It never rejects anyone — the default for unlisted clients is allow.
const WHITELISTED_CLIENT_CODES: [&[u8; 2]; 18] = [
    b"qB", b"TR", b"DE", b"lt", b"LT", b"KT", b"UT", b"UM", b"BT", b"TX",
    b"AZ", b"VZ", b"BI", b"WW", b"WD", b"FD", b"BC", b"BL",
];

/// True if the peer_id's Azureus-style client code is on the leech-only blacklist.
fn client_peer_id_is_banned(peer_id: &[u8]) -> bool {
    if peer_id.len() < 3 || peer_id[0] != b'-' { return false; }
    let code = &peer_id[1..3];
    BANNED_CLIENT_CODES.iter().any(|banned| banned.as_slice() == code)
}

/// True if the entire User-Agent is a bare version like `0.0.0.0` (Xunlei masquerading).
/// Anchored to the whole string so it can't match a version embedded in a normal UA
/// (e.g. `uTorrent/3.5.5.46206`).
fn user_agent_is_bare_version(ua: &str) -> bool {
    let parts: Vec<&str> = ua.trim().split('.').collect();
    parts.len() == 4 && parts.iter().all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
}

/// True if the User-Agent identifies a known leech client, or is a bare version string.
fn client_user_agent_is_banned(ua: &str) -> bool {
    if user_agent_is_bare_version(ua) { return true; }
    let ua_lower = ua.to_ascii_lowercase();
    BANNED_USER_AGENTS.iter().any(|&pattern| ua_lower.contains(pattern))
}

/// Blacklist gate. Banned if the announce peer_id prefix matches the leech-only set, OR the
/// User-Agent does. Checked before key/announce validation so a banned client always receives
/// the ban notice and nothing else. Fails open: an absent/unparseable peer_id together with an
/// unknown User-Agent is treated as not banned (consistent with the default-allow policy).
fn http_service_client_banned(request: &HttpRequest) -> bool {
    let peer_id_banned = parse_query(Some(request.query_string()))
        .ok()
        .and_then(|query| query.get("peer_id").and_then(|values| values.first()).map(|value| value.to_vec()))
        .is_some_and(|peer_id| client_peer_id_is_banned(&peer_id));
    if peer_id_banned {
        return true;
    }
    request.headers()
        .get("User-Agent")
        .and_then(|value| value.to_str().ok())
        .is_some_and(client_user_agent_is_banned)
}

/// True if the peer_id's client code is a well-known client. Message selection only.
fn client_peer_id_is_whitelisted(peer_id: &[u8]) -> bool {
    if peer_id.len() < 3 || peer_id[0] != b'-' { return false; }
    let code = &peer_id[1..3];
    WHITELISTED_CLIENT_CODES.iter().any(|allowed| allowed.as_slice() == code)
}

/// Builds the permissive CORS policy used by the HTTP tracker endpoints (any origin, GET only).
pub fn http_service_cors() -> Cors
{
    Cors::default()
        .allow_any_origin()
        .send_wildcard()
        .allowed_methods(vec!["GET", "OPTIONS"])
        .allow_any_header()
        .max_age(3600)
}

/// Returns the Actix route configuration for the tracker: `/announce`, `/scrape`, their
/// key/user-key variants, and a catch-all 404 handler.
pub fn http_service_routes(data: Arc<HttpServiceData>) -> Box<dyn Fn(&mut ServiceConfig)>
{
    Box::new(move |cfg: &mut ServiceConfig| {
        cfg.app_data(Data::new(data.clone()));
        cfg.service(web::resource("/announce")
            .route(web::get().to(http_service_announce))
        );
        cfg.service(web::resource("/{key}/announce")
            .route(web::get().to(http_service_announce_key))
        );
        cfg.service(web::resource("/{key}/{userkey}/announce")
            .route(web::get().to(http_service_announce_userkey))
        );
        // Slash-less variant kept for clients built against earlier releases.
        cfg.service(web::resource("/{key}/{userkey}announce")
            .route(web::get().to(http_service_announce_userkey))
        );
        cfg.service(web::resource("/scrape")
            .route(web::get().to(http_service_scrape))
        );
        cfg.service(web::resource("/{key}/scrape")
            .route(web::get().to(http_service_scrape_key))
        );
        cfg.default_service(web::route().to(http_service_not_found));
    })
}

/// Starts an HTTP (or HTTPS, when `ssl` is set) tracker listener on `addr`.
///
/// Returns the Actix [`ServerHandle`] for shutdown plus the server future to await.
///
/// # Panics / exit
///
/// Exits the process when the address cannot be bound or the TLS material is missing;
/// panics when the certificate cannot be loaded.
pub async fn http_service(
    addr: SocketAddr,
    data: Arc<TorrentTracker>,
    http_server_object: HttpTrackersConfig,
) -> (ServerHandle, impl Future<Output=Result<(), std::io::Error>>)
{
    let keep_alive = http_server_object.keep_alive;
    let request_timeout = http_server_object.request_timeout;
    let disconnect_timeout = http_server_object.disconnect_timeout;
    let worker_threads = http_server_object.threads as usize;
    if http_server_object.ssl {
        info!("[HTTPS] Starting server listener with SSL on {addr}");
        if http_server_object.ssl_key.is_empty() || http_server_object.ssl_cert.is_empty() {
            error!("[HTTPS] No SSL key or SSL certificate given, exiting...");
            exit(1);
        }
        let server_id = ServerIdentifier::HttpTracker(addr.to_string());
        if let Err(e) = data.certificate_store.load_certificate(
            server_id.clone(),
            &http_server_object.ssl_cert,
            &http_server_object.ssl_key,
        ) {
            panic!("[HTTPS] Failed to load SSL certificate: {e}");
        }
        let resolver = match DynamicCertificateResolver::new(
            Arc::clone(&data.certificate_store),
            server_id,
        ) {
            Ok(resolver) => Arc::new(resolver),
            Err(e) => panic!("[HTTPS] Failed to create certificate resolver: {e}"),
        };
        let tls_config = rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_cert_resolver(resolver);
        let service_data = Arc::new(HttpServiceData {
            torrent_tracker: data.clone(),
            http_trackers_config: Arc::new(http_server_object.clone())
        });
        let sentry_enabled = data.config.sentry_config.enabled;
        let server = if sentry_enabled {
            HttpServer::new(move || {
                App::new()
                    .wrap(Compress::default())
                    .wrap(sentry_actix::Sentry::new())
                    .wrap(http_service_cors())
                    .configure(http_service_routes(service_data.clone()))
            })
                .keep_alive(Duration::from_secs(keep_alive))
                .client_request_timeout(Duration::from_secs(request_timeout))
                .client_disconnect_timeout(Duration::from_secs(disconnect_timeout))
                .workers(worker_threads)
                .bind_rustls_0_23((addr.ip(), addr.port()), tls_config)
                .unwrap_or_else(|e| {
                    error!("[HTTPS] Unable to bind to {addr}: {e}");
                    exit(1);
                })
                .disable_signals()
                .run()
        } else {
            HttpServer::new(move || {
                App::new()
                    .wrap(Compress::default())
                    .wrap(http_service_cors())
                    .configure(http_service_routes(service_data.clone()))
            })
                .keep_alive(Duration::from_secs(keep_alive))
                .client_request_timeout(Duration::from_secs(request_timeout))
                .client_disconnect_timeout(Duration::from_secs(disconnect_timeout))
                .workers(worker_threads)
                .bind_rustls_0_23((addr.ip(), addr.port()), tls_config)
                .unwrap_or_else(|e| {
                    error!("[HTTPS] Unable to bind to {addr}: {e}");
                    exit(1);
                })
                .disable_signals()
                .run()
        };
        return (server.handle(), server);
    }
    info!("[HTTP] Starting server listener on {addr}");
    let service_data = Arc::new(HttpServiceData {
        torrent_tracker: data.clone(),
        http_trackers_config: Arc::new(http_server_object.clone())
    });
    let sentry_enabled = data.config.sentry_config.enabled;
    let server = if sentry_enabled {
        HttpServer::new(move || {
            App::new()
                .wrap(Compress::default())
                .wrap(sentry_actix::Sentry::new())
                .wrap(http_service_cors())
                .configure(http_service_routes(service_data.clone()))
        })
            .keep_alive(Duration::from_secs(keep_alive))
            .client_request_timeout(Duration::from_secs(request_timeout))
            .client_disconnect_timeout(Duration::from_secs(disconnect_timeout))
            .workers(worker_threads)
            .bind((addr.ip(), addr.port()))
            .unwrap_or_else(|e| {
                error!("[HTTP] Unable to bind to {addr}: {e}");
                exit(1);
            })
            .disable_signals()
            .run()
    } else {
        HttpServer::new(move || {
            App::new()
                .wrap(Compress::default())
                .wrap(http_service_cors())
                .configure(http_service_routes(service_data.clone()))
        })
            .keep_alive(Duration::from_secs(keep_alive))
            .client_request_timeout(Duration::from_secs(request_timeout))
            .client_disconnect_timeout(Duration::from_secs(disconnect_timeout))
            .workers(worker_threads)
            .bind((addr.ip(), addr.port()))
            .unwrap_or_else(|e| {
                error!("[HTTP] Unable to bind to {addr}: {e}");
                exit(1);
            })
            .disable_signals()
            .run()
    };
    (server.handle(), server)
}

/// `GET /{key}/announce` — announce with an access key (and, when keys are disabled but
/// users are enabled, a user key) in the path.
///
/// Validates the key before delegating to [`http_service_announce_handler`].
pub async fn http_service_announce_key(request: HttpRequest, path: web::Path<String>, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4AnnouncesHandled, StatsEvent::Tcp6AnnouncesHandled, 1);
            ip
        },
        Err(result) => { return result; }
    };
    if http_service_client_banned(&request) {
        http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_CLIENT_BANNED.clone());
    }
    let tracker_config = &data.torrent_tracker.config.tracker_config;
    if tracker_config.keys_enabled {
        let key = path.clone();
        let key_check = http_service_check_key_validation(data.torrent_tracker.clone(), key).await;
        if let Some(value) = key_check {
            http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            return value;
        }
    }
    if tracker_config.users_enabled && !tracker_config.keys_enabled {
        let user_key = path.clone();
        match http_service_check_user_key_validation(data.torrent_tracker.clone(), user_key).await {
            Ok(user_id) => {
                return http_service_announce_handler(request, ip, data.torrent_tracker.clone(), Some(user_id), data.http_trackers_config.rtctorrent).await;
            }
            Err(response) => {
                http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
                return response;
            }
        }
    }
    http_service_announce_handler(request, ip, data.torrent_tracker.clone(), None, data.http_trackers_config.rtctorrent).await
}

/// `GET /{key}/{userkey}announce` — announce carrying both an access key and a user key.
///
/// Validates both before delegating to [`http_service_announce_handler`].
pub async fn http_service_announce_userkey(request: HttpRequest, path: web::Path<(String, String)>, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4AnnouncesHandled, StatsEvent::Tcp6AnnouncesHandled, 1);
            ip
        },
        Err(result) => { return result; }
    };
    if http_service_client_banned(&request) {
        http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_CLIENT_BANNED.clone());
    }
    let tracker_config = &data.torrent_tracker.config.tracker_config;
    if tracker_config.keys_enabled {
        let key = path.clone().0;
        let key_check = http_service_check_key_validation(data.torrent_tracker.clone(), key).await;
        if let Some(value) = key_check {
            http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            return value;
        }
    }
    if tracker_config.users_enabled {
        let user_key = path.clone().1;
        match http_service_check_user_key_validation(data.torrent_tracker.clone(), user_key).await {
            Ok(user_id) => {
                return http_service_announce_handler(request, ip, data.torrent_tracker.clone(), Some(user_id), data.http_trackers_config.rtctorrent).await;
            }
            Err(response) => {
                http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
                return response;
            }
        }
    }
    http_service_announce_handler(request, ip, data.torrent_tracker.clone(), None, data.http_trackers_config.rtctorrent).await
}

/// `GET /announce` — plain announce without any key.
///
/// Rejected with `missing key` when the tracker runs in keys-required mode.
pub async fn http_service_announce(request: HttpRequest, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4AnnouncesHandled, StatsEvent::Tcp6AnnouncesHandled, 1);
            ip
        },
        Err(result) => {
            return result;
        }
    };
    if http_service_client_banned(&request) {
        http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_CLIENT_BANNED.clone());
    }
    if data.torrent_tracker.config.tracker_config.keys_enabled {
        http_stat_update(ip, &data.torrent_tracker, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_MISSING_KEY.clone());
    }
    http_service_announce_handler(request, ip, data.torrent_tracker.clone(), None, data.http_trackers_config.rtctorrent).await
}

/// Core announce logic shared by all announce routes.
///
/// In slave cluster mode the request is forwarded to the master. Otherwise the query is
/// parsed and validated, whitelist/blacklist rules applied, the swarm updated via
/// [`TorrentTracker::handle_announce`], and a bencoded response built: compact peer
/// strings, a dictionary peer list, or an RtcTorrent offer/answer exchange.
pub async fn http_service_announce_handler(request: HttpRequest, ip: IpAddr, data: Arc<TorrentTracker>, user_key: Option<UserId>, rtctorrent_enabled: bool) -> HttpResponse
{
    if data.config.tracker_config.cluster == ClusterMode::slave {
        let query_string = request.query_string().to_string();
        let protocol = if request.connection_info().scheme() == "https" {
            ProtocolType::Https
        } else {
            ProtocolType::Http
        };
        let client_port = request.peer_addr().map_or(0, |a| a.port());
        match forward_request(
            &data,
            protocol,
            RequestType::Announce,
            ip,
            client_port,
            query_string.into_bytes(),
        ).await {
            Ok(response) => {
                return HttpResponse::Ok()
                    .content_type(ContentType::plaintext())
                    .body(response.payload);
            }
            Err(e) => {
                http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
                return HttpResponse::Ok()
                    .content_type(ContentType::plaintext())
                    .body(create_cluster_error_response(&e));
            }
        }
    }
    let query_map_result = parse_query(Some(request.query_string()));
    let query_map = match http_service_query_hashing(query_map_result) {
        Ok(result) => { result }
        Err(err) => {
            http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            return err;
        }
    };
    let announce = data.validate_announce(ip, query_map).await;
    let announce_unwrapped = match announce {
        Ok(result) => { result }
        Err(e) => {
            return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "failure reason" => ben_bytes!(e.to_string())
            }.encode());
        }
    };
    let is_rtc_request = announce_unwrapped.rtctorrent.unwrap_or(false);
    // Must precede `handle_announce`, which stores the client's SDP offer/answer.
    if is_rtc_request && !rtctorrent_enabled {
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
            "failure reason" => ben_bytes!(b"rtctorrent not enabled" as &[u8])
        }.encode());
    }
    let tracker_config = &data.config.tracker_config;
    if tracker_config.whitelist_enabled && !data.check_whitelist(announce_unwrapped.info_hash) {
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_UNKNOWN_INFO_HASH.clone());
    }
    if tracker_config.blacklist_enabled && data.check_blacklist(announce_unwrapped.info_hash) {
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_FORBIDDEN_INFO_HASH.clone());
    }
    let torrent_entry = match data.handle_announce(&announce_unwrapped, user_key).await {
        Ok(result) => { result }
        Err(e) => {
            http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "failure reason" => ben_bytes!(e.to_string())
            }.encode());
        }
    };
    let request_interval = tracker_config.request_interval as i64;
    let request_interval_minimum = tracker_config.request_interval_minimum as i64;
    let rtc_interval = tracker_config.rtc_interval as i64;
    // Counts come from `counts`, never from the peer maps: those are bounded copies.
    let seeds_count = if is_rtc_request {
        torrent_entry.counts.rtc_seeds as i64
    } else {
        torrent_entry.counts.total_seeds() as i64
    };
    let peers_count = if is_rtc_request {
        torrent_entry.counts.rtc_peers as i64
    } else {
        torrent_entry.counts.total_peers() as i64
    };
    let completed_count = torrent_entry.completed as i64;
    // Announce warning message: recognised (whitelisted) clients get the seeding reminder;
    // every other allowed client (default-allow) gets a nudge to switch to a well-known one.
    let warning_message: &str = if client_peer_id_is_whitelisted(&announce_unwrapped.peer_id.0) {
        "Thanks for DLing. Plz remember to seed as long as you can. By TBMovies."
    } else {
        "Thanks for DLing. It's recommended to switch to any well-known client. By TBMovies."
    };
    if is_rtc_request {
        let mut rtc_peers_list = ben_list!();
        {
            let rtc_peers_list_mut = rtc_peers_list.list_mut().unwrap();
            for (peer_id, peer) in &torrent_entry.rtc_seeds {
                if *peer_id == announce_unwrapped.peer_id { continue; }
                if let Some(offer) = peer.rtc_sdp_offer()
                    && !offer.is_empty() {
                    rtc_peers_list_mut.push(ben_map! {
                        "peer_id" => ben_bytes!(peer_id.0.to_vec()),
                        "sdp_offer" => ben_bytes!(offer.into_bytes())
                    });
                }
            }
        }
        let pending_answers = data.take_rtc_pending_answers(announce_unwrapped.info_hash, announce_unwrapped.peer_id);
        let mut rtc_answers_list = ben_list!();
        {
            let rtc_answers_list_mut = rtc_answers_list.list_mut().unwrap();
            for (answerer_peer_id, sdp_answer) in &pending_answers {
                rtc_answers_list_mut.push(ben_map! {
                    "peer_id" => ben_bytes!(answerer_peer_id.0.to_vec()),
                    "sdp_answer" => ben_bytes!(sdp_answer.as_bytes().to_vec())
                });
            }
        }

        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
            "rtc interval" => ben_int!(rtc_interval),
            "complete" => ben_int!(seeds_count),
            "incomplete" => ben_int!(peers_count),
            "rtc_peers" => rtc_peers_list,
            "rtc_answers" => rtc_answers_list
        }.encode());
    }

    // Already clamped to 1..=72 by `validate_announce`, so it is safe to size buffers with.
    let want = announce_unwrapped.numwant as usize;
    if announce_unwrapped.compact {
        let mut peers_list: Vec<u8> = Vec::with_capacity(if ip.is_ipv4() { want * 6 } else { want * 18 });
        return match ip {
            IpAddr::V4(_) => {
                if announce_unwrapped.left != 0 {
                    let peers_to_use = if is_rtc_request { &torrent_entry.rtc_seeds } else { &torrent_entry.seeds };
                    let seeds = data.get_peers_ref(
                        peers_to_use,
                        TorrentPeersType::IPv4,
                        Some(announce_unwrapped.peer_id),
                        want
                    );
                    for &(_, torrent_peer) in &seeds {

                        if let IpAddr::V4(ipv4) = torrent_peer.peer_addr.ip() {
                            peers_list.extend_from_slice(&ipv4.octets());
                            peers_list.extend_from_slice(&torrent_peer.peer_addr.port().to_be_bytes());
                        }
                    }
                }
                if peers_list.len() < want * 6 {
                    let peers_to_use = if is_rtc_request { &torrent_entry.rtc_peers } else { &torrent_entry.peers };
                    let peers = data.get_peers_ref(
                        peers_to_use,
                        TorrentPeersType::IPv4,
                        Some(announce_unwrapped.peer_id),
                        want
                    );
                    for &(_, torrent_peer) in &peers {
                        if peers_list.len() >= want * 6 {
                            break;
                        }

                        if let IpAddr::V4(ipv4) = torrent_peer.peer_addr.ip() {
                            peers_list.extend_from_slice(&ipv4.octets());
                            peers_list.extend_from_slice(&torrent_peer.peer_addr.port().to_be_bytes());
                        }
                    }
                }
                HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                    "interval" => ben_int!(request_interval),
                    "min interval" => ben_int!(request_interval_minimum),
                    "rtc interval" => ben_int!(rtc_interval),
                    "complete" => ben_int!(seeds_count),
                    "incomplete" => ben_int!(peers_count),
                    "downloaded" => ben_int!(completed_count),
                    "warning message" => ben_bytes!(warning_message),
                    "peers" => ben_bytes!(peers_list)
                }.encode())
            }
            IpAddr::V6(_) => {
                if announce_unwrapped.left != 0 {
                    let peers_to_use = if is_rtc_request { &torrent_entry.rtc_seeds } else { &torrent_entry.seeds_ipv6 };
                    let seeds = data.get_peers_ref(
                        peers_to_use,
                        TorrentPeersType::IPv6,
                        Some(announce_unwrapped.peer_id),
                        want
                    );
                    for &(_, torrent_peer) in &seeds {
                        if let IpAddr::V6(ipv6) = torrent_peer.peer_addr.ip() {
                            peers_list.extend_from_slice(&ipv6.octets());
                            peers_list.extend_from_slice(&torrent_peer.peer_addr.port().to_be_bytes());
                        }
                    }
                }
                if peers_list.len() < want * 18 {
                    let peers_to_use = if is_rtc_request { &torrent_entry.rtc_peers } else { &torrent_entry.peers_ipv6 };
                    let peers = data.get_peers_ref(
                        peers_to_use,
                        TorrentPeersType::IPv6,
                        Some(announce_unwrapped.peer_id),
                        want
                    );
                    for &(_, torrent_peer) in &peers {
                        if peers_list.len() >= want * 18 {
                            break;
                        }
                        if let IpAddr::V6(ipv6) = torrent_peer.peer_addr.ip() {
                            peers_list.extend_from_slice(&ipv6.octets());
                            peers_list.extend_from_slice(&torrent_peer.peer_addr.port().to_be_bytes());
                        }
                    }
                }
                HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                    "interval" => ben_int!(request_interval),
                    "min interval" => ben_int!(request_interval_minimum),
                    "rtc interval" => ben_int!(rtc_interval),
                    "complete" => ben_int!(seeds_count),
                    "incomplete" => ben_int!(peers_count),
                    "downloaded" => ben_int!(completed_count),
                    "warning message" => ben_bytes!(warning_message),
                    "peers6" => ben_bytes!(peers_list)
                }.encode())
            }
        }
    }
    let mut peers_list = ben_list!();
    let peers_list_mut = peers_list.list_mut().unwrap();
    match ip {
        IpAddr::V4(_) => {
            if announce_unwrapped.left != 0 {
                let peers_to_use = if is_rtc_request { &torrent_entry.rtc_seeds } else { &torrent_entry.seeds };
                let seeds = data.get_peers_ref(
                    peers_to_use,
                    TorrentPeersType::IPv4,
                    Some(announce_unwrapped.peer_id),
                    want
                );
                for &(peer_id, torrent_peer) in &seeds {
                    peers_list_mut.push(ben_map! {
                        "peer id" => ben_bytes!(peer_id.to_string()),
                        "ip" => ben_bytes!(torrent_peer.peer_addr.ip().to_string()),
                        "port" => ben_int!(i64::from(torrent_peer.peer_addr.port()))
                    });
                }
            }
            if peers_list_mut.len() < want {
                let peers_to_use = if is_rtc_request { &torrent_entry.rtc_peers } else { &torrent_entry.peers };
                let peers = data.get_peers_ref(
                    peers_to_use,
                    TorrentPeersType::IPv4,
                    Some(announce_unwrapped.peer_id),
                    want
                );
                for &(peer_id, torrent_peer) in &peers {
                    if peers_list_mut.len() >= want {
                        break;
                    }
                    peers_list_mut.push(ben_map! {
                        "peer id" => ben_bytes!(peer_id.to_string()),
                        "ip" => ben_bytes!(torrent_peer.peer_addr.ip().to_string()),
                        "port" => ben_int!(i64::from(torrent_peer.peer_addr.port()))
                    });
                }
            }
            HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "interval" => ben_int!(request_interval),
                "min interval" => ben_int!(request_interval_minimum),
                "rtc interval" => ben_int!(rtc_interval),
                "complete" => ben_int!(seeds_count),
                "incomplete" => ben_int!(peers_count),
                "downloaded" => ben_int!(completed_count),
                "warning message" => ben_bytes!(warning_message),
                "peers" => peers_list
            }.encode())
        }
        IpAddr::V6(_) => {
            if announce_unwrapped.left != 0 {
                let peers_to_use = if is_rtc_request { &torrent_entry.rtc_seeds } else { &torrent_entry.seeds_ipv6 };
                let seeds = data.get_peers_ref(
                    peers_to_use,
                    TorrentPeersType::IPv6,
                    Some(announce_unwrapped.peer_id),
                    want
                );
                for &(peer_id, torrent_peer) in &seeds {
                    peers_list_mut.push(ben_map! {
                        "peer id" => ben_bytes!(peer_id.to_string()),
                        "ip" => ben_bytes!(torrent_peer.peer_addr.ip().to_string()),
                        "port" => ben_int!(i64::from(torrent_peer.peer_addr.port()))
                    });
                }
            }
            if peers_list_mut.len() < want {
                let peers_to_use = if is_rtc_request { &torrent_entry.rtc_peers } else { &torrent_entry.peers_ipv6 };
                let peers = data.get_peers_ref(
                    peers_to_use,
                    TorrentPeersType::IPv6,
                    Some(announce_unwrapped.peer_id),
                    want
                );
                for &(peer_id, torrent_peer) in &peers {
                    if peers_list_mut.len() >= want {
                        break;
                    }
                    peers_list_mut.push(ben_map! {
                        "peer id" => ben_bytes!(peer_id.to_string()),
                        "ip" => ben_bytes!(torrent_peer.peer_addr.ip().to_string()),
                        "port" => ben_int!(i64::from(torrent_peer.peer_addr.port()))
                    });
                }
            }
            HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "interval" => ben_int!(request_interval),
                "min interval" => ben_int!(request_interval_minimum),
                "rtc interval" => ben_int!(rtc_interval),
                "complete" => ben_int!(seeds_count),
                "incomplete" => ben_int!(peers_count),
                "downloaded" => ben_int!(completed_count),
                "warning message" => ben_bytes!(warning_message),
                "peers6" => peers_list
            }.encode())
        }
    }
}

/// `GET /{key}/scrape` — scrape with an access key in the path.
///
/// Validates the key before delegating to [`http_service_scrape_handler`].
pub async fn http_service_scrape_key(request: HttpRequest, path: web::Path<String>, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            if ip.is_ipv4() {
                data.torrent_tracker.update_stats(StatsEvent::Tcp4ScrapesHandled, 1);
            } else {
                data.torrent_tracker.update_stats(StatsEvent::Tcp6ScrapesHandled, 1);
            }
            ip
        },
        Err(result) => {
            return result;
        }
    };
    debug!("[DEBUG] Request from {ip}: Scrape with Key");
    if data.torrent_tracker.config.tracker_config.keys_enabled {
        let key = path.into_inner();
        let key_check = http_service_check_key_validation(data.torrent_tracker.clone(), key).await;
        if let Some(value) = key_check { return value; }
    }
    http_service_scrape_handler(request, ip, data.torrent_tracker.clone()).await
}

/// Core scrape logic shared by the scrape routes.
///
/// In slave cluster mode the request is forwarded to the master; otherwise returns the
/// bencoded `files` dictionary with seed/completed/leech counts per requested info-hash.
pub async fn http_service_scrape_handler(request: HttpRequest, ip: IpAddr, data: Arc<TorrentTracker>) -> HttpResponse
{
    if data.config.tracker_config.cluster == ClusterMode::slave {
        let query_string = request.query_string().to_string();
        let protocol = if request.connection_info().scheme() == "https" {
            ProtocolType::Https
        } else {
            ProtocolType::Http
        };
        let client_port = request.peer_addr().map_or(0, |a| a.port());
        match forward_request(
            &data,
            protocol,
            RequestType::Scrape,
            ip,
            client_port,
            query_string.into_bytes(),
        ).await {
            Ok(response) => {
                return HttpResponse::Ok()
                    .content_type(ContentType::plaintext())
                    .body(response.payload);
            }
            Err(e) => {
                http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
                return HttpResponse::Ok()
                    .content_type(ContentType::plaintext())
                    .body(create_cluster_error_response(&e));
            }
        }
    }
    let query_map_result = parse_query(Some(request.query_string()));
    let query_map = match http_service_query_hashing(query_map_result) {
        Ok(result) => { result }
        Err(err) => {
            http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            return err;
        }
    };
    let scrape = data.validate_scrape(query_map).await;
    if let Err(scrape) = scrape {
        http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
        return HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
            "failure reason" => ben_bytes!(scrape.to_string())
        }.encode());
    }
    let tracker_config = &data.config.tracker_config;
    let request_interval = tracker_config.request_interval as i64;
    let request_interval_minimum = tracker_config.request_interval_minimum as i64;
    match scrape.as_ref() {
        Ok(e) => {
            let data_scrape = data.handle_scrape(data.clone(), e).await;
            let mut scrape_list = ben_map!();
            let scrape_list_mut = scrape_list.dict_mut().unwrap();
            for (info_hash, counts) in &data_scrape {
                scrape_list_mut.insert(Cow::from(info_hash.0.to_vec()), ben_map! {
                    "complete" => ben_int!(counts.total_seeds() as i64),
                    "downloaded" => ben_int!(counts.completed as i64),
                    "incomplete" => ben_int!(counts.total_peers() as i64)
                });
            }
            HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "interval" => ben_int!(request_interval),
                "min interval" => ben_int!(request_interval_minimum),
                "files" => scrape_list
            }.encode())
        }
        Err(e) => {
            http_stat_update(ip, &data, StatsEvent::Tcp4Failure, StatsEvent::Tcp6Failure, 1);
            HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "failure reason" => ben_bytes!(e.to_string())
            }.encode())
        }
    }
}

/// `GET /scrape` — scrape without an access key.
pub async fn http_service_scrape(request: HttpRequest, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            if ip.is_ipv4() {
                data.torrent_tracker.update_stats(StatsEvent::Tcp4ScrapesHandled, 1);
            } else {
                data.torrent_tracker.update_stats(StatsEvent::Tcp6ScrapesHandled, 1);
            }
            ip
        },
        Err(result) => {
            return result;
        }
    };
    debug!("[DEBUG] Request from {ip}: Scrape");
    http_service_scrape_handler(request, ip, data.torrent_tracker.clone()).await
}

/// Catch-all handler returning a bencoded `unknown request` failure with HTTP 404.
pub async fn http_service_not_found(request: HttpRequest, data: Data<Arc<HttpServiceData>>) -> HttpResponse
{
    let ip = match http_validate_ip(request.clone(), data.clone()).await {
        Ok(ip) => {
            if ip.is_ipv4() {
                data.torrent_tracker.update_stats(StatsEvent::Tcp4NotFound, 1);
            } else {
                data.torrent_tracker.update_stats(StatsEvent::Tcp6NotFound, 1);
            }
            ip
        },
        Err(result) => {
            return result;
        }
    };
    debug!("[DEBUG] Request from {ip}: 404 Not Found");
    HttpResponse::NotFound().content_type(ContentType::plaintext()).body(ERR_UNKNOWN_REQUEST.clone())
}

/// Increments the TCP connections-handled statistic for the request's IP family.
#[inline]
pub fn http_service_stats_log(ip: IpAddr, tracker: &TorrentTracker)
{
    if ip.is_ipv4() {
        tracker.update_stats(StatsEvent::Tcp4ConnectionsHandled, 1);
    } else {
        tracker.update_stats(StatsEvent::Tcp6ConnectionsHandled, 1);
    }
}

/// Decodes a 40-character hex string into an [`InfoHash`].
///
/// # Errors
///
/// Returns a ready-made bencoded error response when the string is not valid hex.
#[inline]
pub async fn http_service_decode_hex_hash(hash: String) -> Result<InfoHash, HttpResponse>
{
    hex::decode(&hash)
        .ok()
        .and_then(|bytes| bytes.get(..20).and_then(|slice| <[u8; 20]>::try_from(slice).ok()))
        .map(InfoHash)
        .ok_or_else(|| HttpResponse::InternalServerError().content_type(ContentType::plaintext()).body(ERR_UNABLE_DECODE_HEX.clone()))
}

/// Decodes a 40-character hex string into a [`UserId`].
///
/// # Errors
///
/// Returns a ready-made bencoded error response when the string is not valid hex.
#[inline]
pub async fn http_service_decode_hex_user_id(hash: String) -> Result<UserId, HttpResponse>
{
    hex::decode(&hash)
        .ok()
        .and_then(|bytes| bytes.get(..20).and_then(|slice| <[u8; 20]>::try_from(slice).ok()))
        .map(UserId)
        .ok_or_else(|| HttpResponse::InternalServerError().content_type(ContentType::plaintext()).body(ERR_UNABLE_DECODE_HEX.clone()))
}

/// Determines the client IP, honouring the configured `real_ip` header when trusted
/// proxies are enabled and the request came from a configured proxy; falls back to the
/// socket peer address.
///
/// # Errors
///
/// Returns `Err(())` when no peer address is available.
pub async fn http_service_retrieve_remote_ip(request: HttpRequest, data: Arc<HttpTrackersConfig>) -> Result<IpAddr, ()>
{
    let origin_ip = request.peer_addr().map(|addr| addr.ip()).ok_or(())?;

    // Direct-facing (no reverse proxy): trust ONLY the connecting socket address. Forwarded
    // headers such as CF-Connecting-IP are ignored here, so a client cannot spoof its announced
    // IP. This path is identical for IPv4 and IPv6 — no address classification is involved.
    // Enable `trusted_proxies` only when the tracker actually sits behind a proxy (cloudflared).
    if !data.trusted_proxies {
        return Ok(origin_ip);
    }

    // Behind a proxy. If a proxy allowlist is configured, only honour forwarded headers when
    // the connection actually came from one of those proxy addresses; otherwise use the socket.
    let explicit_proxies = !data.trusted_proxy_addrs.is_empty();
    if explicit_proxies && !data.trusted_proxy_addrs.contains(&origin_ip) {
        return Ok(origin_ip);
    }

    // Behind Cloudflare (cloudflared tunnel): the real client IP is carried in CF-Connecting-IP.
    // Use it so peers and leechers are announced with their real IP instead of the tunnel
    // address (e.g. 172.28.0.3). Works for both IPv4 and IPv6 client addresses.
    if let Some(real_ip) = request.headers()
        .get("CF-Connecting-IP")
        .and_then(|header| header.to_str().ok())
        .and_then(|ip_str| IpAddr::from_str(ip_str.trim()).ok())
    {
        return Ok(real_ip);
    }

    // Fall back to the configured real_ip header for any non-Cloudflare proxy.
    request.headers()
        .get(&data.real_ip)
        .and_then(|header| header.to_str().ok())
        .and_then(|ip_str| {
            // Without an allowlist a proxy is indistinguishable from a client, so private
            // address claims are refused; a configured proxy may legitimately forward them.
            validate_remote_ip(ip_str, explicit_proxies).ok()?;
            IpAddr::from_str(ip_str).ok()
        })
        .map_or(Ok(origin_ip), Ok)
}

/// Resolves and validates the client IP and logs the connection statistic.
///
/// # Errors
///
/// Returns a bencoded `unknown origin ip` response when the IP cannot be determined.
pub async fn http_validate_ip(request: HttpRequest, data: Data<Arc<HttpServiceData>>) -> Result<IpAddr, HttpResponse>
{
    match http_service_retrieve_remote_ip(request.clone(), data.http_trackers_config.clone()).await {
        Ok(ip) => {
            http_service_stats_log(ip, &data.torrent_tracker);
            Ok(ip)
        }
        Err(()) => {
            Err(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_UNKNOWN_ORIGIN_IP.clone()))
        }
    }
}

/// Maps a query-string parse error into a bencoded `failure reason` response.
pub fn http_service_query_hashing(query_map_result: Result<HttpServiceQueryHashingMapOk, CustomError>) -> Result<HttpServiceQueryHashingMapOk, HttpServiceQueryHashingMapErr>
{
    match query_map_result {
        Ok(e) => { Ok(e) }
        Err(e) => {
            Err(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ben_map! {
                "failure reason" => ben_bytes!(e.to_string())
            }.encode()))
        }
    }
}

/// Validates a 40-character hex access key against the key table.
///
/// Returns `None` when the key is valid, or `Some(response)` with the bencoded error to send.
pub async fn http_service_check_key_validation(data: Arc<TorrentTracker>, key: String) -> Option<HttpResponse>
{
    if validate_info_hash_hex(&key).is_err() {
        return Some(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_INVALID_KEY.clone()));
    }
    let key_decoded: InfoHash = match http_service_decode_hex_hash(key).await {
        Ok(result) => { result }
        Err(error) => { return Some(error) }
    };
    if !data.check_key(key_decoded) {
        return Some(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_UNKNOWN_KEY.clone()));
    }
    None
}

/// Validates a 40-character hex user key and resolves it to a [`UserId`].
///
/// # Errors
///
/// Returns the bencoded error response when the key is malformed or unknown.
pub async fn http_service_check_user_key_validation(data: Arc<TorrentTracker>, user_key: String) -> Result<UserId, HttpResponse>
{
    if validate_peer_id_hex(&user_key).is_err() {
        return Err(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_INVALID_USER_KEY.clone()));
    }
    let user_key_decoded: UserId = http_service_decode_hex_user_id(user_key).await?;
    if data.check_user_key(user_key_decoded).is_none() {
        return Err(HttpResponse::Ok().content_type(ContentType::plaintext()).body(ERR_UNKNOWN_USER_KEY.clone()));
    }
    Ok(user_key_decoded)
}

/// Windows-only sanity check that a TCP bind address is available before spawning the server.
///
/// # Errors
///
/// Returns the bind error when the address is already in use.
pub fn http_check_host_and_port_used(bind_address: &str) -> std::io::Result<()> {
    if cfg!(target_os = "windows")
        && let Err(e) = std::net::TcpListener::bind(bind_address)
    {
        log::error!("Unable to bind TCP listener to {bind_address}: {e}");
        return Err(e);
    }
    Ok(())
}

/// Increments the IPv4 or IPv6 variant of a statistics event depending on the client IP.
#[inline]
pub fn http_stat_update(ip: IpAddr, data: &TorrentTracker, stats_ipv4: StatsEvent, stat_ipv6: StatsEvent, count: i64)
{
    match ip {
        IpAddr::V4(_) => {
            data.update_stats(stats_ipv4, count);
        }
        IpAddr::V6(_) => {
            data.update_stats(stat_ipv6, count);
        }
    }
}
