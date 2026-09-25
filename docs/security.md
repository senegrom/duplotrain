# Local editor and build security

## Local editor

`duplotrain gui` is a single-user local tool, not an authenticated network service.
It binds only to `127.0.0.1`. Use the printed URL, or `localhost` with
that same port. Do not expose it through a reverse proxy or public interface.

The HTTP layer requires a single, exact loopback Host header on the listening
port, rejects foreign/null/duplicate Origins and cross-site Fetch Metadata, and
requires `application/json` for every POST (even an empty body). It never grants
CORS/preflight access. The JSON-only requirement is intentional CSRF protection
for browsers without Origin or Fetch Metadata: forms and no-cors requests cannot
send this non-simple media type. Local programmatic clients can use JSON
without browser-only headers. These protections do not authenticate other
processes already running on the local machine.

Ambiguous/chunked framing, oversized or truncated bodies, malformed JSON and
JSON nested more than 64 levels deep are rejected before dispatch; the browser
engine applies the same depth limit before parsing, since its WebAssembly stack
overflows long before Python's recursion limit.
Every response, the server's own error pages included, prohibits framing and
MIME sniffing. A rejected request must leave the entire session unchanged;
`tests/test_http_security.py` verifies this using real local sockets.

Request bodies have an absolute 10-second read deadline that a client trickling
bytes cannot extend. A rejected body is drained for at most 0.25 s and 64 KiB;
every connection then closes gracefully, flushing its response, sending FIN and
discarding input for at most 0.5 s and 64 KiB, so a client reads the refusal even
after chunked, malformed or late input (`finish()` in `duplotrain/gui.py` gives the
reasons). A response that cannot be written ends the connection: nothing follows a
partly written answer. Regressions send each such body late and still read the
status, and check that the waits are bounded.

The static Pyodide application uses the shared in-process dispatcher instead of
this HTTP listener, with the same engine rules.

## Reproducible dependency downloads

All three workflows use read-only repository tokens (only the Pages deploy job
also holds Pages-write and OIDC tokens), disable checkout credential persistence,
and pin actions to upstream commit SHAs. Version comments allow
Dependabot to maintain those pins, and it checks Python and GitHub Actions
dependencies weekly. The Lean workflow downloads the versioned
elan Linux release archive, checks its reviewed SHA-256 before extracting or
executing it, and uses the `lean-toolchain` version and the axiom audit.

The static builder verifies the Pyodide release archive against the reviewed
`PYODIDE_SHA256` map in `webapp/build.py` before touching the deployment output.
It checks cached archives on every build and regenerates loose runtime files
from verified bytes. Downloads and extraction are size-bounded, and downloads
have a timeout.

A checksum failure stops the build; it is never silently accepted. Remove the
reported archive from `webapp/vendor/` and retry to recover from corruption.
Before upgrading Pyodide, review the upstream release and add its asset digest
to `PYODIDE_SHA256`, then run the build and Chromium/WebKit tests. Do not generate
an expected checksum from an untrusted download during the build itself.

`tests/test_build_security.py` checks tampered downloads/caches, unsafe archive
members, unknown versions, and the workflow hardening invariants without network
access. The browser CI jobs additionally build and test the actual pinned runtime.

## Editor consistency and recoverable saves

Every mutating API route (including the search jobs and restore) requires an
integer `revision` copied from the state the client actually displayed. The HTTP
server checks it under the same session lock as the mutation. Missing, malformed or
stale revisions receive HTTP 409 with `code: "stale_revision"` and the current
`state`, without changing the session. Read-only state/export requests do not
require a revision. Non-browser JSON clients must follow this contract too.

Revisions restart at 0 in every engine process or worker, so the state also
carries a random engine `instance`. The editor sends it with the revision, and
a request naming another instance is stale even at an equal revision; clients
that omit it get the revision check alone. The local server binds its port
without address reuse on Windows, so a second server cannot share it.

The editor refreshes from a conflict response and clears old tools/previews,
but never automatically retries the rejected action against newly indexed
pieces. A conflict from a fresh engine at revision 0, such as a restarted local
server, restores the newest confirmed session there instead of adopting, and
autosaving, the empty one ([editor.md](editor.md#autosave)). Revisions prevent
stale edits; they are not credentials.

Before committing an edit, the session validates its proposed snapshot with the
same layout limits as import/recovery (1,500 pieces and 200 action stones), plus
a byte budget with room for the save/request envelope. This applies to manual
placement, solver candidate application and restore, as well as inventory
changes. An edit that crosses a limit is rejected without changing history,
revision, inventory or saved state. Unlimited inventory does not bypass these
recovery limits. Exporting, removing pieces/stones and undoing remain available.
