# Source provenance — expanded Phase 1 extraction

| Role | Value |
|---|---|
| Research source | `collatz/approaches/WordCertDensity` |
| Lean milestone | E-L7 local primitive migration plus AX-I2 restricted analytic extensions |
| Manuscript snapshot | `sources/manuscript-source-2026-09-21-b45f544d.md` |
| Manuscript SHA-256 | `b45f544d320f4cc780d3aaff369417b2fff6b712501b313ef7a6d6ff7917b87c` |
| Project modules | 1402 exact reachable modules |
| External non-Mathlib modules | 0 |
| License | Apache-2.0 |

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
evaluating the enormous coefficient. The baseline eleven statements remain
unchanged; seven new selected companions are described in formalization.yaml.


## Commit roles and snapshot authority

| Commit | Literal role |
|---|---|
| `a71acad21b4fe8f0ba3315469ac8a4d821992c79` | Historical eleven-statement extraction baseline, before this expansion. |
| `0bffa2591ad90706eadb1ac274689c8a362cf6c3` | Historical research baseline for the completed local primitive migration. |
| `db584cd6d46c92f209a44c0f1c829460d327499d` | Pinned Mathlib dependency; not a project proof-source revision. |

The current expansion is identified locally by EXTRACTION_MANIFEST.json file
hashes. It is not frozen or published. For any eventual intake, the authoritative
substantive snapshot is the immutable commit supplied to that intake, which must
match a clean checked-out HEAD and the authorized pushed remote commit. None of
the historical commits above is the authoritative revision of this expansion.

This clean repository was copied from the reviewed extraction using its file
manifest. No research Git history, build cache, intermediate proof probes, or
old manuscript snapshot is included. All Lean source files are byte-identical
to that reviewed candidate.
