/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.FiberAverage

/-!
# Projective triangle for the original reference oscillation

Uniform means are invariant under reduction. Thus the lower-level error
has exactly the same cost when lifted; no extra group-size factor appears.
-/

@[expose] public section

namespace WordCertDensity
namespace Reference

/-- Successive ternary reductions equal the direct reduction, including equal levels. -/
theorem project_project {m r n : ℕ} (hmr : m ≤ r) (hrn : r ≤ n)
    (x : ZMod (3 ^ n)) : project hmr (project hrn x) = project (hmr.trans hrn) x := by
  have h := ZMod.castHom_comp (Nat.pow_dvd_pow 3 hmr) (Nat.pow_dvd_pow 3 hrn)
  exact DFunLike.congr_fun h x

/-- Full-group density errors obey the projective triangle with no scaling loss. -/
theorem fullL1_triangle {m r n : ℕ} (hmr : m ≤ r) (hrn : r ≤ n) :
    mean n (fun x => |density n x - density m (project (hmr.trans hrn) x)|) ≤
      mean r (fun x => |density r x - density m (project hmr x)|) +
        mean n (fun x => |density n x - density r (project hrn x)|) := by
  rw [← mean_project hrn (fun x => |density r x - density m (project hmr x)|),
    ← mean_add]
  apply mean_mono
  intro x
  rw [project_project]
  exact (abs_sub_le (density n x) (density r (project hrn x))
    (density m (project (hmr.trans hrn) x))).trans_eq (add_comm _ _)

end Reference

namespace FiniteFourier

/-- Actual reference-mass oscillation obeys the same projective triangle (M.triangle). -/
theorem oscillation_mass_triangle {m r n : ℕ} (hmr : m ≤ r) (hrn : r ≤ n) :
    oscillation (hmr.trans hrn) (Reference.mass n) ≤
      oscillation hmr (Reference.mass r) + oscillation hrn (Reference.mass n) := by
  simp only [oscillation_mass]
  exact Reference.fullL1_triangle hmr hrn

end FiniteFourier
end WordCertDensity
