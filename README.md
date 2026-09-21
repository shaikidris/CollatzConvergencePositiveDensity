# Positive density of Collatz convergence at every rate above 3/log(4/3)

This local Palomar-format EXTRACTION contains eighteen selected statements in
Challenge.lean, their proofs in Solution.lean, and exactly 1402 reachable
WordCertDensity source modules. The original eleven mathematical statements are preserved under descriptive renaming.

The main result gives one positive lower natural density of starting integers
that reach one within `c * log n` ordinary Collatz steps, for every
`c > 3 / log (4/3)`. For each positive target, such a positive density exists
exactly when the target is not divisible by three. Here convergence means
reaching one; for starting integers greater than one this also witnesses descent.

Seven companions add exact finite fan allocation, real-moment domination,
canonical/admissible-target profile density, actual entropy increments, a
finite entropy limit with explicit tail, and zero normalized growth.

The primitive-decay input is proved locally by Analytic.LocalPrimitive.Decay.
Some probability and word constructions retain adapted Mazur code and its
Apache-2.0 notices. No external numerical primitive theorem is imported.

The Renyi-order right limit, complementary capacity, coefficient-size and
optimized-density comparisons, deeper tables, full optimizers and amplified
roots remain outside the selected surface. No pointwise Collatz convergence
or evaluated cutoff is claimed.

Research owners and all eighteen public proofs passed local Lean/axiom checks.
The previous private snapshot passed direct Lean, an eighteen-theorem
standard-axiom audit, semantic lint and explicit nonempty style checks.
The presentation pass also passes fresh Challenge/Solution compilation, all
eighteen axiom reports, semantic lint and explicit style checks.
The private Linux build and fresh axiom report are running against `52f2559e0475d80d3f1fdefa4e7d6f17f796b38b`.
This metadata-only publication update leaves every Lean source, dependency pin,
Comparator configuration and workflow unchanged. Comparator, NanoDa and official
Palomar verification remain pending; the package is not yet registration-ready.

## Paper and source snapshot

- Published preprint v1.0.0: https://doi.org/10.5281/zenodo.22871622
- SSRN submission 7497758: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7497758
  (submission received; screening completion is not claimed).
- Source: [sources/manuscript-v1.0.0-d4cf2a4b.md](sources/manuscript-v1.0.0-d4cf2a4b.md)
- Reading PDF: [sources/manuscript-v1.0.0.pdf](sources/manuscript-v1.0.0.pdf)
- Source SHA-256: `d4cf2a4be67dff8934cd67c68fe9055eaa2a99ad3a760bbaf84b8644d160778e`
- Paper license: CC BY 4.0. Lean code license: Apache-2.0.

See PALOMAR_RELEASE_CONE.md, SOURCE_PROVENANCE.md and EXTRACTION_MANIFEST.json.

This repository contains only the selected proof cone, release metadata, current
manuscript snapshot and reading PDF, and required third-party license notices.
The research checkout and its history remain separate.
