# Selected theorem map

Eighteen statements are selected. The original eleven mathematical statements are
preserved under descriptive renaming; their existential constants, fractional residual qualification and
individual-root omissions remain described in formalization.yaml. The seven
companions below use explicit public definitions and structural bridge proofs.
Local checks do not constitute Comparator/NanoDa or registry verification.

| Companion | Manuscript clause | Exact scope |
|---|---|---|
| `CollatzWordCert.fan_profile_eq_optimal_allocation` | D.hinge; D.allocation | Exact actual-fan attained minimum, hinge supremum and feasible-domain bounds. |
| `CollatzWordCert.fan_profile_ge_real_moment_bound` | Individual moment branch of D.profiledominates | Every real order s > 1; positive moment ceiling and full-group normalization. No complementary branch. |
| `CollatzWordCert.collatz_convergence_profile_density_bound` | D.profiledensity with canonical sources | Existential positive paid residual and one level before every larger clock. |
| `CollatzWordCert.collatz_hitting_profile_density_bound` | D.profiledensity with fixed-target sources | Each positive target not divisible by three; target-dependent score and level. |
| `CollatzWordCert.reference_entropy_increment_bounds` | F.entropyincrement | Reindexed n+1 minus n, for n >= 1, with the actual compact mixing envelope. |
| `CollatzWordCert.reference_entropy_tends_to_finite_limit_with_tail_bound` | Finite-limit and tail clauses of F.entropybound | Actual law; compact-envelope tail implies the printed power-tail estimate. No Renyi-order right limit. |
| `CollatzWordCert.reference_entropy_div_level_tends_to_zero` | Order-one zero-rate clause of F.entropybound | Normalized limit and positive-index normalized infimum are zero. |

## Preserved baseline

- `CollatzWordCert.collatz_convergence_positive_lower_density`
- `CollatzWordCert.collatz_convergence_depth_eleven_density_bound`
- `CollatzWordCert.collatz_logarithmic_threshold_lt_10431_div_1000`
- `CollatzWordCert.collatz_hitting_positive_lower_density`
- `CollatzWordCert.collatz_hitting_depth_eleven_density_bound`
- `CollatzWordCert.collatz_hitting_positive_density_iff_target_not_divisible_by_three`
- `CollatzWordCert.collatz_canonical_root_reaches_one_with_positive_density`
- `CollatzWordCert.collatz_convergence_density_with_vanishing_clock_loss`
- `CollatzWordCert.collatz_hitting_density_with_vanishing_clock_loss`
- `CollatzWordCert.collatz_convergence_fractional_density_bound`
- `CollatzWordCert.collatz_hitting_fractional_density_bound`

The full Renyi-order limit, complementary-capacity comparison, coefficient-size
comparisons, deeper tables, optimized recipes and amplified roots remain
outside the selected surface. Source hashes are in EXTRACTION_MANIFEST.json.

## Presentation migration

The public names below replace the initial private snapshot names. The mathematical
statements and quantifier order are preserved; the main density statement is now
written directly rather than hidden behind a proposition name.

| Initial name | Readable public name |
|---|---|
| `common_density` | `collatz_convergence_positive_lower_density` |
| `depthEleven_density` | `collatz_convergence_depth_eleven_density_bound` |
| `numerical_clock` | `collatz_logarithmic_threshold_lt_10431_div_1000` |
| `every_admissible_target` | `collatz_hitting_positive_lower_density` |
| `every_admissible_target_depthEleven` | `collatz_hitting_depth_eleven_density_bound` |
| `target_criterion` | `collatz_hitting_positive_density_iff_target_not_divisible_by_three` |
| `individual_root` | `collatz_canonical_root_reaches_one_with_positive_density` |
| `common_vanishing_clock` | `collatz_convergence_density_with_vanishing_clock_loss` |
| `target_vanishing_clock` | `collatz_hitting_density_with_vanishing_clock_loss` |
| `fractional_density` | `collatz_convergence_fractional_density_bound` |
| `every_admissible_target_fractional` | `collatz_hitting_fractional_density_bound` |
| `profile_allocation` | `fan_profile_eq_optimal_allocation` |
| `profile_moment_bound` | `fan_profile_ge_real_moment_bound` |
| `profile_density` | `collatz_convergence_profile_density_bound` |
| `target_profile_density` | `collatz_hitting_profile_density_bound` |
| `entropy_increment` | `reference_entropy_increment_bounds` |
| `entropy_limit` | `reference_entropy_tends_to_finite_limit_with_tail_bound` |
| `entropy_zero_rate` | `reference_entropy_div_level_tends_to_zero` |
