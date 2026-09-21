/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ProductSplit
public import WordCertDensity.Analytic.LocalPrimitive.PassageMoment
import Mathlib.Tactic

/-! # Original product comparison at covering pair-prefix stopping families -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Discarding the factors before a bounded pair stop gives the exact fresh
remaining-product average. Coverage, pair length, and the original PMF are
explicit; no optional-stopping or independence conclusion is assumed. -/
theorem whiteWindowProduct_stopping_le (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (m j : ℕ) (l : ℤ) (S : Set ValuationWord)
    (hpair : ∀ u ∈ S, ∃ q, q ≤ m ∧ u.length = 2 * q)
    (hcover : ∀ w : ValuationWord, w.length = 2 * m → ∃ u : S, (u : ValuationWord) <+: w) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * m) w * whiteWindowProduct white z m j l w) ≤
      ∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
        ∑' v : ValuationWord, Reference.wordPMF (2 * m - (u : ValuationWord).length) v *
          whiteWindowProduct white z (m - (u : ValuationWord).length / 2)
            (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total) v := by
  let F : ValuationWord → ValuationWord → ℝ≥0∞ := fun u v =>
    whiteWindowProduct white z (m - u.length / 2) (j + u.length / 2) (l + u.total) v
  have hlen : ∀ u ∈ S, u.length ≤ 2 * m := by
    intro u hu
    obtain ⟨q, hq, he⟩ := hpair u hu
    omega
  rw [← countableStoppedMoment_factor S (2 * m) F hlen]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w.length = 2 * m
  · obtain ⟨u, hup⟩ := hcover w hw
    obtain ⟨q, hq, hlength⟩ := hpair u u.property
    have he : (u : ValuationWord) = w.take (2 * q) := by
      simpa only [hlength] using List.prefix_iff_eq_take.mp hup
    have hhalf : (u : ValuationWord).length / 2 = q := by omega
    have hp := whiteWindowProduct_le_suffix white hz q (m - q) j l w
    rw [Nat.add_sub_of_le hq] at hp
    have hsingle : Reference.wordPMF (2 * m) w * whiteWindowProduct white z m j l w ≤
        if (u : ValuationWord) <+: w then Reference.wordPMF (2 * m) w *
          F u (w.drop (u : ValuationWord).length) else 0 := by
      rw [if_pos hup]
      dsimp only [F]
      rw [hhalf, hlength, he]
      exact mul_le_mul_right hp _
    exact hsingle.trans (ENNReal.le_tsum u)
  · have hzword := Reference.wordPMF_eq_zero_of_length_ne (2 * m) w hw
    rw [hzword, zero_mul]
    exact zero_le

end WordCertDensity.LocalPrimitive
