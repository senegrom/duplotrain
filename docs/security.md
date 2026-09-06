# Local editor and build security

## Local editor

`duplotrain gui` is a single-user local tool, not an authenticated network service.
It continues to bind only to `127.0.0.1`. Use the printed URL, or `localhost` with
that same port. Do not expose it through a reverse proxy or public interface.

The HTTP layer requires a single, exact loopback Host header on the listening
port, rejects foreign/null/duplicate Origins and cross-site Fetch Metadata, and
requires `application/json` for every POST (even an empty body). It never grants
CORS/preflight access. The JSON-only requirement is intentional CSRF protection
for browsers without Origin or Fetch Metadata: forms and no-cors requests cannot
send this non-simple media type. Local programmatic clients can continue using
JSON without browser-only headers. These protections do not authenticate other
processes already running on the local machine.

Ambiguous/chunked framing, oversized or truncated bodies, and malformed JSON are
rejected before dispatch. Body reads have a timeout. Responses prohibit framing
and MIME sniffing. A rejected request must leave the entire session unchanged;
`tests/test_http_security.py` verifies this using real local sockets.

The static Pyodide application uses the shared in-process dispatcher instead of
this HTTP listener; its transport and engine rules have not changed.

## Reproducible dependency downloads

Both workflows use read-only repository tokens, disable checkout credential
persistence, and pin actions to upstream commit SHAs. Version comments allow
Dependabot to maintain those pins. The Lean workflow downloads the versioned
elan Linux release archive, checks its reviewed SHA-256 before extracting or
executing it, and keeps the existing `lean-toolchain` version and axiom audit.

The static builder verifies the Pyodide release archive against the reviewed
`PYODIDE_SHA256` map in `webapp/build.py` before touching the deployment output.
It checks cached archives on every build and regenerates loose runtime files
from verified bytes. Old loose-file-only caches are not trusted. Downloads and
extraction are size-bounded, and downloads have a timeout.

A checksum failure stops the build; it is never silently accepted. Remove the
reported archive from `webapp/vendor/` and retry to recover from corruption.
Before upgrading Pyodide, review the upstream release and add its asset digest
to `PYODIDE_SHA256`, then run the build and Chromium/WebKit tests. Do not generate
an expected checksum from an untrusted download during the build itself.

`tests/test_build_security.py` checks tampered downloads/caches, unsafe archive
members, unknown versions, and the workflow hardening invariants without network
access. The browser CI jobs additionally build and test the actual pinned runtime.

## Editor consistency and recoverable saves

Every mutating API route (including solve and restore) requires an integer
`revision` copied from the state the client actually displayed. The HTTP server
checks it under the same session lock as the mutation. Missing, malformed or
stale revisions receive HTTP 409 with `code: "stale_revision"` and the current
`state`, without changing the session. Read-only state/export requests do not
require a revision. Non-browser JSON clients must follow this contract too.

The editor refreshes from a conflict response and clears old tools/previews,
but never automatically retries the rejected action against newly indexed
pieces. The shared Pyodide dispatcher uses the same revision check. Each new
search also advances the revision because candidate indices can change even
when the layout does not. Revisions prevent stale edits; they are not credentials.

Before committing an edit, the session validates its proposed snapshot with the
same layout limits as import/recovery (1,500 pieces and 200 action stones), plus
a byte budget with room for the save/request envelope. This applies to manual
placement, solver candidate application and restore, as well as inventory
changes. An edit that crosses a limit is rejected without changing history,
revision, inventory or saved state. Unlimited inventory does not bypass these
recovery limits. Exporting, removing pieces/stones and undoing remain available.

Request bodies use an absolute 10-second read deadline. Rejected-body cleanup
has a separate absolute 0.25-second deadline and 64 KiB cap, and skips bytes
already consumed. Single-read buffering lets the deadline be rechecked even
when a client continually trickles bytes; timeouts do not restart per chunk.

Open-end mate discovery indexes exact positions and opposite headings once per
endpoint, instead of comparing every pair. Elevation and the exact algebraic
coordinates remain part of the key; there is no approximate snapping tolerance.
