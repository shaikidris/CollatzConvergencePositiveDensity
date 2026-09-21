# Source provenance — expanded Phase 1 extraction

| Role | Value |
|---|---|
| Research source | `collatz/approaches/WordCertDensity` |
| Lean milestone | E-L7 local primitive migration plus AX-I2 restricted analytic extensions |
| Manuscript snapshot | `sources/manuscript-v1.0.0-d4cf2a4b.md` |
| Manuscript SHA-256 | `d4cf2a4be67dff8934cd67c68fe9055eaa2a99ad3a760bbaf84b8644d160778e` |
| Project modules | 1402 exact reachable modules |
| External non-Mathlib modules | 0 |
| Lean code license | Apache-2.0 |
| Paper license | CC-BY-4.0 |
| Published paper | https://doi.org/10.5281/zenodo.22871622 |
| SSRN submission | https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7497758 |

The proof architecture retains attribution to Tao and Mazur. The independence
claim is limited to the primitive input: this cone does not assume Mazur's
order-6409 numerical primitive-decay bound. It does not claim independent
historical invention of the surrounding structural methods.

## Retained adapted-code notices

Some local probability, word-law, and affine-map proofs are adapted from
Lech Mazur's Apache-2.0 code. Their source headers retain the attribution.
The referenced original LICENSE and NOTICE are included at
`third_party/mazur/`. These notices preserve code provenance;
the extraction does not import the former external primitive-decay theorem.

The appended public reference-law definitions expose the same geometric word
construction, fan and local coefficient recipe as the imported producers.
Structural bridge proofs identify their recursive definitions without
evaluating the enormous coefficient. The baseline eleven mathematical statements are preserved under public renaming; seven new selected companions are described in formalization.yaml.


## Commit roles and snapshot authority

| Commit | Literal role |
|---|---|
| `a71acad21b4fe8f0ba3315469ac8a4d821992c79` | Historical eleven-statement extraction baseline, before this expansion. |
| `0bffa2591ad90706eadb1ac274689c8a362cf6c3` | Historical research baseline for the completed local primitive migration. |
| `db584cd6d46c92f209a44c0f1c829460d327499d` | Pinned Mathlib dependency; not a project proof-source revision. |

The current extraction is identified locally by EXTRACTION_MANIFEST.json file
hashes. The Lean repository remains private; the manuscript is published separately. For any eventual intake, the authoritative
substantive snapshot is the immutable commit supplied to that intake, which must
match a clean checked-out HEAD and the authorized pushed remote commit. None of
the historical commits above is the authoritative revision of this expansion.

This clean repository was copied from the reviewed extraction using its file
manifest. No research Git history, build cache, intermediate proof probes, or
old manuscript snapshot is included. All 1402 production proof modules remain byte-identical to that reviewed
candidate. Challenge, Solution and Audit have a presentation-only name and
notation migration recorded in THEOREM_MAP.md. The initial private snapshot
is commit `d98194f7565627b6eb34ac56a055380e28f81e8d`; the presentation
revision was committed and privately pushed as `52f2559e0475d80d3f1fdefa4e7d6f17f796b38b`.
The publication-metadata synchronization is a later revision and does not change that running CI snapshot.

The published version 1.0.0 supersedes the earlier bundled b45f544d manuscript.
The old file remains recoverable from the prior Git commit. The final editorial
pass preserved mathematical displays; its last change identifies the ten-term
logarithm bounds and positive margins in Section 6. The selected Lean scope and
all proof-source bytes are unchanged. Publication does not imply Palomar acceptance.
