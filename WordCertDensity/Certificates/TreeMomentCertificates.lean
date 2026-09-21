/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary

/-! # Moment certificates with abstract tree summaries -/

namespace WordCertDensity.Certificates

/-- Convert an exact tree energy bound before substituting concrete finite data. -/
theorem integer_energy_tree_certificate (d count S p q : ℕ)
    (hc : count = 3 ^ d) (hS : 0 < S) (hq : 0 < q) (z : Entries)
    (hz : ∀ x : ZMod (3 ^ d), (S : ℝ) * Reference.density d x ≤ z.lookup x.val)
    (hs : q * z.energySum count ≤ p * count * S ^ 2) :
    Reference.moment 2 d ≤ (p : ℝ) / q := by
  subst count
  apply integer_energy_certificate d S p q hS hq (fun x => z.lookup x.val) hz
  rw [sum_zmod_positive_list (3 ^ d) (fun i => z.lookup i ^ 2)]
  rw [← energySum_eq]
  exact hs

/-- Convert an exact fractional tree bound before substituting concrete finite data. -/
theorem integer_fractional_tree_certificate (d count k p q : ℕ)
    (hc : count = 3 ^ d) (hq : 0 < q) (z r : Entries)
    (hz : ∀ x : ZMod (3 ^ d),
      (2 : ℝ) ^ (2 * k) * Reference.density d x ≤ z.lookup x.val)
    (hr : ∀ x : ZMod (3 ^ d), z.lookup x.val ≤ r.lookup x.val ^ 2)
    (hs : q * z.fractionalSum r count ≤ p * count * 2 ^ (3 * k)) :
    Reference.moment (3 / 2) d ≤ (p : ℝ) / q := by
  subst count
  apply integer_fractional_even_certificate d k p q hq
    (fun x => z.lookup x.val) (fun x => r.lookup x.val) hz hr
  rw [sum_zmod_positive_list (3 ^ d) (fun i => z.lookup i * r.lookup i)]
  rw [← fractionalSum_eq]
  exact hs

end WordCertDensity.Certificates
