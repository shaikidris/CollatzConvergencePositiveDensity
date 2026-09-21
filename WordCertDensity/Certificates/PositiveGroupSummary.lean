/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.LevelThreeBounds
import WordCertDensity.Certificates.Data.Summaries

/-! # Complete summaries without expanding concrete residue groups -/

namespace WordCertDensity.Certificates

/-- The core energy summary agrees with the ambient mathematical sum. -/
theorem energySum_eq (z : Entries) (n : ℕ) :
    z.energySum n = ((List.range n).map (fun i => z.lookup i ^ 2)).sum := rfl

/-- The core fractional summary agrees with the ambient mathematical sum. -/
theorem fractionalSum_eq (z r : Entries) (n : ℕ) :
    z.fractionalSum r n =
      ((List.range n).map (fun i => z.lookup i * r.lookup i)).sum := rfl

/-- The complete list summary works for any positive group size. -/
theorem sum_zmod_positive_list (n : ℕ) [NeZero n] (f : ℕ → ℕ) :
    (∑ x : ZMod n, f x.val) = ((List.range n).map f).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact sum_zmod_succ_list k f

end WordCertDensity.Certificates
