# Packed cyclic certificate replay optimization

This proof-only change preserves all 346 depth-eleven cyclic statements and their cap statements, all 18 selected Challenge/Solution statements, the finite payloads and the standard axiom boundary. PackedLookup proves direct fixed-width extraction equals the existing packed-tree lookup for every width, depth, payload and index. LevelElevenFast retains packed nodes and transports the faster check back to the original cyclic checker.

The additional two owner modules serve the existing depth-eleven cyclic family. They replace repeated decoder computation; they introduce no mathematical claim or new selected theorem. Moments, cap computations and lower-depth certificates remain unchanged.

## Validation scope

An isolated full-family experiment covered all 346 blocks and 177147 entries, with a balanced assembly proof. Compilation passed in 570.47 seconds. Its exported complete cyclic family passed Linux ARM64 Lean replay in 524.97 seconds and pinned NanoDa in 424.62 seconds. These are diagnostic measurements, not full-release Comparator verification.

A matched three-block comparison (0, 173, 344) passed both checkers for both variants. Combined checker time was 50.99 seconds originally and 12.72 seconds optimized. The export increased from 7.7 MB to 13.5 MB. No full-release speedup or completion deadline is inferred from these samples.

Production integration retains the original theorem names, module owners and summary assembly. Full selected-root Linux build, statement comparison and independent replay must pass on the new commit before release readiness is claimed. Prior registry and CI reports apply to their original immutable revisions.
