# Upper-bound proof work

This branch is the visible coefficient-one working branch.

## Current verified bound

The strongest unconditional theorem currently kernel-checked in the
repository is on `agent/push-below-5`:

```text
known incoming edge:  2*N + 6
arbitrary start:       2*N + 7
```

## Current target

The coefficient-one programme targets:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

The exact residual is the raw theorem that at most four globally novel
repeated-writer events occur after entering through a known physical edge.

## New branch result

`theory/lean/TripleSelfLinkSimpleCycleTail.lean` closes the stable
simple-cycle half of the selected self-link raw-cycle obstruction. The
focused workflow builds the actual theorem chain rather than a probe file.

The detailed proof map, verification policy, other-agent comparison and
remaining global bridges are in:

```text
theory/lean/COEFFICIENT_ONE_STATUS.md
```

The remaining coefficient-one work is concentrated in early-self-link,
serial five-frame and residual strict-nest/support-contact placement.
