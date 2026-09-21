/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostPassageProduct
import Mathlib.Tactic

/-! # The stopped product bound with the actual geometric shortage paid -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The literal original-law stopped product is bounded by two delta plus
the exact predictable quarter-mark moment. -/
theorem postPassageProductMoment_toReal_lt {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (a j : ℕ) (top l : ℤ) (B L : ℕ) {z : ℝ≥0∞} (hz : z ≤ 1)
    (hadm : longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B))
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B + localPrimitiveK B + n / 2 ≤ L) :
    (postPassageProductMoment n ξ (top - l).toNat j l B L z).toReal <
      2 / (localPrimitiveDeltaDenom B : ℝ) +
        (((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ localPrimitiveK B).toReal := by
  let E := passageWhiteShortageEvent n ξ (top - l).toNat j l B
  let c := ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ localPrimitiveK B
  have hzfin : z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hz
  have hc : c ≠ ⊤ := by dsimp [c]; finiteness
  have hefin := Gated.event_ne_top (Reference.wordPMF (2 * L)) E
  have hm := postPassageProductMoment_le n ξ (top - l).toNat j l B L hz hL
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hefin, hc⟩) hm
  rw [ENNReal.toReal_add hefin hc] at hr
  change (postPassageProductMoment n ξ (top - l).toNat j l B L z).toReal ≤
    Gated.probability (Reference.wordPMF (2 * L)) E + c.toReal at hr
  have heq : Gated.probability (Reference.wordPMF (2 * L)) E =
      Gated.probability (Reference.wordPMF (2 * L))
        (postPassageShortageEvent n ξ (top - l).toNat j l B) := by
    apply Gated.probability_congr_on_support
    intro w hw
    have hlen : w.length = 2 * L := by
      by_contra hne
      exact hw (Reference.wordPMF_eq_zero_of_length_ne (2 * L) w hne)
    exact passageWhiteShortageEvent_iff n ξ (top - l).toNat j l B w (by omega)
  rw [heq] at hr
  exact hr.trans_lt (add_lt_add_of_lt_of_le
    (postPassage_white_shortage_probability_lt_window hn ξ hξ a j top l B L hadm (by omega))
    le_rfl)

end WordCertDensity.LocalPrimitive
