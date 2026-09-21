# Publication metadata preparation — 21 September 2026

Status: metadata prepared; replay and release gates pending.
Repository: https://github.com/shaikidris/CollatzConvergencePositiveDensity (private).
Running Linux proof snapshot: 52f2559e0475d80d3f1fdefa4e7d6f17f796b38b.
Candidate submission commit: resolve the full commit containing this packet; final intake remains pending.
Project directory: repository root. Challenge: Challenge.lean. Solution: Solution.lean.
Comparator: comparator.json (18 declarations, unchanged).
Title: Positive density of Collatz convergence at every rate above 3/log(4/3).
Paper DOI: https://doi.org/10.5281/zenodo.22871622.
SSRN: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7497758.
SSRN receipt confirms submission received; screening completion is not claimed.
The receipt retained Apache foundation; the manuscript says independent researcher.
No account or submission changes were made in this preparation batch.

Validation: upstream v0.4 schema passed; all extraction-manifest hashes passed;
18 Challenge/Solution/metadata selections match. All Lean sources, dependency
pins, Comparator and workflow bytes match the running commit. No Lean rebuild
was started for this documentation-only update.

Remaining sequence: finish Linux build and fresh axiom report; record the authorized metadata commit and private push; refresh exact Palomar
verifier/toolchain/provenance checks and run Comparator/NanoDa rehearsal; settle
public repository release with authorization; prepare the final immutable intake
packet. No registry identifier, independent replay success or ready-to-submit
status is claimed. Live Palomar state changes are a user handoff under the
installed preparation skill.

## Default Linux release check

Run `palomar-full-preflight.yml` as the first Linux release validation, using
Palomar's current reusable workflow in `mode: full`, with its workflow reference
and pipeline_commit pinned to the same SHA and the intended submission commit
explicitly pinned. Inspect the mechanical report, not just the job color.
The earlier `private-linux.yml` is diagnostic-only: Lake plus axiom reports
cannot replace Comparator and NanoDa. Do not run both sequentially by default.
Use a focused diagnostic build only for a named failure or an explicit need.
If public visibility is not authorized, prepare the full workflow and ask;
do not silently substitute a long private build as Palomar readiness evidence.

Lesson: the first Linux run passed 4893 jobs in 2:48:33 but omitted comparison
and independent replay, requiring another build cycle. The full preflight now
runs separately at https://github.com/shaikidris/CollatzConvergencePositiveDensity/actions/runs/35593969242.
That run is not restarted by this documentation update. Its target remains
9f15b521bac3a9a319d0be7d0935efa5683e899c. Repository visibility is now public.
