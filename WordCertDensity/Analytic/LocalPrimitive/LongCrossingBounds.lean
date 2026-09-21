/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingRectangle
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingPacking
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingColumns
import WordCertDensity.Analytic.Typical

/-! # The fixed-offset and simultaneous long-crossing estimates -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

private theorem stopped_position_in_rectangle (s j p A : ℕ) (top l : ℤ)
    (hl : l ≤ top) (hs : s = (top - l).toNat)
    (w : ValuationWord) (i : Fin (s / 2 + 1)) (hc : horizonTailEvent s 0 i w)
    (hh : ¬ longCrossingHorizontalEvent s ((A : ℝ) * ((p : ℝ) + 1)) w)
    (hv : ¬ longCrossingVerticalEvent s p (A * (p + 1)) w) :
    inLongCrossingRectangle
      (longCrossingRectangleLo s j p ((A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1))
      (longCrossingRectangleHi s j p ((A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1))
      top (A * (p + 1)) (longCrossingPosition j l ((i : ℕ) + 1) p w) := by
  have hhor : |(((i : ℕ) + 1 : ℕ) : ℝ) - (s : ℝ) / 4| ≤
      (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1 := by
    by_contra hnot
    exact hh ⟨i, hc, lt_of_not_ge hnot⟩
  have hx : |((j + ((i : ℕ) + 1) + p : ℕ) : ℝ) -
      ((j : ℝ) + (s : ℝ) / 4 + p)| ≤
        (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1 := by
    convert hhor using 1
    push_cast
    congr 1
    ring
  have hxy := longCrossing_rectangle_contains_window s j p _ _ hx
  have hmono := ValuationWord.total_take_mono w
    (show 2 * ((i : ℕ) + 1) ≤ 2 * ((i : ℕ) + 1 + p) by omega)
  have hcross := hc.2
  have hheight : ValuationWord.total (w.take (2 * ((i : ℕ) + 1 + p))) - s ≤ A * (p + 1) := by
    by_contra hnot
    exact hv ⟨i, hc, lt_of_not_ge hnot⟩
  have hsInt : (s : ℤ) = top - l := by
    rw [hs, Int.toNat_of_nonneg (sub_nonneg.mpr hl)]
  refine ⟨hxy.1, hxy.2, ?_, ?_⟩ <;>
    simp only [longCrossingPosition] <;> omega

private theorem column_count_simplify (A H s p : ℕ) (W : ℝ)
    (hA : 0 < A) (hH : 0 < H) (hs : 0 < s)
    (hW : W ≤ 2 * A * ((p : ℝ) + 1) * Real.sqrt s) :
    (2 * ((A * (p + 1) : ℕ) : ℝ) +
        320 * ((A * (p + 1) : ℕ) : ℝ) * W / (longCrossingThreshold H p)) *
          (4 / Real.sqrt s) ≤
      8 * A * ((p : ℝ) + 1) / Real.sqrt s +
        (2560 * (A : ℝ) ^ 2 / H) / ((p : ℝ) + 1) ^ 2 := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  have hr : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  unfold longCrossingThreshold
  push_cast
  calc
    _ ≤ (2 * ((A : ℝ) * ((p : ℝ) + 1)) +
        320 * ((A : ℝ) * ((p : ℝ) + 1)) *
          (2 * A * ((p : ℝ) + 1) * Real.sqrt s) / (H * ((p : ℝ) + 1) ^ 4)) *
          (4 / Real.sqrt s) := by gcongr
    _ = _ := by field_simp; ring

/-- Appendix E.5's literal fixed-offset bound, with every geometry, law,
tail, and recipe premise discharged from the original admissibility conditions. -/
theorem longCrossing_fixed_target : LongCrossingFixedTarget := by
  intro n ξ old j top l B A H P Z hadm L hL p hp
  rcases hadm with ⟨hn, hξ, holdN, hold, hstart, hB, hP, hA, hH, hZ, hlevel⟩
  let s := (top - l).toNat
  let Y := A * (p + 1)
  let W : ℝ := (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1
  let u := longCrossingThreshold H p
  let lo := longCrossingRectangleLo s j p W
  let hi := longCrossingRectangleHi s j p W
  let bad := longCrossingBadColumns (rectangleLargeAnchors n ξ lo hi top Y u) Y
  have hmargin := longCrossing_recipe_sqrt_margin s B A P Z p hA hZ hlevel hp
  have hb := longCrossing_rectangle_width_budgets s A p hmargin.1 hmargin.2
  rcases hb with ⟨hs, hYone, hWsmall, hYsmall, hpsmall, hYW, hWlarge⟩
  have hYreal : (1 : ℝ) ≤ Y := by exact_mod_cast hYone
  have hYr : (Y : ℝ) = (A : ℝ) * ((p : ℝ) + 1) := by dsimp [Y]; push_cast; rfl
  have hs64 : 64 ≤ s := by
    have hsR : (64 : ℝ) ≤ s := by rw [hYr] at hYreal; linarith
    exact_mod_cast hsR
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hYbudget : (Y : ℝ) ≤ (s : ℝ) / 64 := by rw [hYr]; exact hYsmall
  have hround := longCrossing_rectangle_rounding s j p Y W hs64 hW0 hWsmall hYbudget hpsmall
  have hrow := longCrossing_rectangle_old_top n ξ old j p Y top l W hn hξ holdN
    hstart hs64 hW0 hWsmall hYbudget hpsmall
  have hu := longCrossing_recipe_threshold_budget B A H p hmargin.1 hH
  have hcount := rectangle_badColumns_card_le n ξ old lo hi Y u top W hn hξ hold
    hround.1 hround.2.2.1 hrow hu.2 hu.1 hYone
    (by dsimp [W]; exact le_add_of_nonneg_left (by positivity))
    (by rw [hYr]; exact hYW) hround.2.2.2.2
  let EH := longCrossingHorizontalEvent s ((A : ℝ) * ((p : ℝ) + 1))
  let EV := longCrossingVerticalEvent s p Y
  let EC := longCrossingColumnsEvent s j p bad
  have hcontain : Gated.probability (Reference.wordPMF (2 * L))
      (longCrossingLargeEvent n ξ s j l H p) ≤
        Gated.probability (Reference.wordPMF (2 * L)) (fun w => EH w ∨ EV w ∨ EC w) := by
    apply Gated.probability_mono_on_support
    intro w _ hw
    by_cases hh : EH w
    · exact Or.inl hh
    by_cases hv : EV w
    · exact Or.inr (Or.inl hv)
    right
    right
    rcases hw with ⟨i, hc, hlarge⟩
    refine ⟨i, hc, ?_⟩
    have hrect := stopped_position_in_rectangle s j p A top l hstart.2.1 rfl w i hc hh hv
    exact rectangle_largeTriangle_badColumn_cover n ξ old lo hi Y u top hn hξ hold
      hround.1 hrow _ hrect hlarge
  have hL' : s / 2 + 1 ≤ L := by dsimp [s]; omega
  have hLp : s / 2 + 1 + p ≤ L := by dsimp [s]; omega
  have hAp : 0 < A := by omega
  have hHp : 0 < H := by rw [hH]; positivity
  have hwidth : (1 : ℝ) ≤ (A : ℝ) * ((p : ℝ) + 1) := by rwa [hYr] at hYreal
  have hh := longCrossingHorizontal_probability_le L s hL' hs _ hwidth
  have hv := longCrossingVertical_probability_le L s p A hLp hmargin.1
  have hc := longCrossingColumns_probability_le L s j p bad hL' hs
  have hc' : Gated.probability (Reference.wordPMF (2 * L)) EC ≤
      8 * A * ((p : ℝ) + 1) / Real.sqrt s +
        (2560 * (A : ℝ) ^ 2 / H) / ((p : ℝ) + 1) ^ 2 := by
    apply hc.trans
    apply (mul_le_mul_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ 4 / Real.sqrt s)).trans
    exact column_count_simplify A H s p W hAp hHp hs hWlarge
  have hunion := Gated.probability_or_le (Reference.wordPMF (2 * L)) EH
    (fun w => EV w ∨ EC w)
  have hunion' := Gated.probability_or_le (Reference.wordPMF (2 * L)) EV EC
  have hsum := hcontain.trans (hunion.trans (add_le_add le_rfl hunion'))
  have htotal := hsum.trans (add_le_add hh (add_le_add hv hc'))
  apply htotal.trans
  unfold longCrossingProbabilityBound
  dsimp [s] at *
  apply le_of_eq
  field_simp
  ring

/-- Appendix E.5's simultaneous union estimate on one original-word horizon. -/
theorem longCrossing_union_target : LongCrossingUnionTarget :=
  longCrossingUnionTarget_of_fixed longCrossing_fixed_target

end WordCertDensity.LocalPrimitive
