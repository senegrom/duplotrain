# Recovery and input boundaries

## Live offline tabs

An activating offline worker asks every in-scope window for its document's build
through a transferred message port. The document captures that build before its
engine starts; it does not report the version activated by another tab. The
handshake runs afresh, so a restarted service worker needs no volatile client map.

Pruning retains the current complete version, the most recently active previous
version, and every complete cache matching a live document's build. More than one
content version can share a build stamp, so all matching caches are retained.
Incomplete installations and caches belonging to other applications are untouched.

An older page without the handshake, a suspended/unresponsive tab, failed client
enumeration, a newly appearing tab, or an unknown build prevents deletion for that
activation. Each reply has a 1.5-second allowance. Closing those tabs permits
pruning at a later activation; there is no periodic background deletion. This
favours recoverability over a strict two-version storage cap. Browser eviction
still means downloaded project backups are necessary.

## Route witnesses

The existing failure priority remains: failure to loop, then failure to visit all
track, then failure to traverse all track both ways in the repeating cycle.
`counterexample_property` identifies `looping`, `completely` or `perfectly` for the
selected witness, or is null when none exists. The UI names that failed property
and the run's outcome. A known failure can be shown during incomplete analysis;
universal classifications and optimality still require the whole requested scope.

## Custom catalogue input

Exact catalogue numerators and denominators are limited to 512 bits before
geometry or float conversion, including integer, Fraction and Alg inputs. The
existing textual limit (64 characters, decimal exponent at most 64) remains.
Normal accepted exact values retain their representation. Excessive inputs raise
ValueError, which the existing CLI presents as a bad catalogue file.

Piece width and connector overhang are each capped at 10,000 mm; the existing
10,000 mm segment-length cap is unchanged. Independently, collision queries whose
cell radius exceeds 16 inspect occupied buckets rather than enumerating a huge
empty square. An overflowed radius inspects all stored buckets. The same precise
pair checks, exclusions and underpass/height thresholds apply in either path.
