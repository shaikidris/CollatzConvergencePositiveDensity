/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftOffsetConstant
import WordCertDensity.Construction.GraftTransition
import WordCertDensity.Construction.MacroHistories

/-! # Transition and continuation at the actual appended count

The transition occupies the first B_0 stopped blocks. Later macro histories
start at that count, so their offsets retain every preceding contraction.
The bounds are uniform in the number of completed continuation stages.
-/

namespace WordCertDensity.Construction

/-- The common-precision part of the appended offset bound. -/
noncomputable def graftTransitionOffset (E : ℕ) : ℝ :=
  (8 / 7 : ℝ) * (3 / 2 : ℝ) ^ (E - 1)

private theorem commonPrecision_offset {E : ℕ} {w : ValuationWord}
    (hw : w ∈ stoppedWords E) : (w.offset : ℝ) ≤ (3 / 2 : ℝ) ^ (E - 1) := by
  have ho := Rat.cast_le (K := ℝ) |>.mpr (word_offset_le_depth w)
  norm_num only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at ho
  have hd : w.length ≤ E - 1 := by have := stoppedWords_length_lt hw; omega
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hd
  linarith

private theorem graftBlocks_offset {E : ℕ} {ws : List ValuationWord}
    (hw : ∀ w ∈ ws, w ∈ stoppedWords E) :
    (ValuationWord.offset ws.flatten : ℝ) ≤ graftTransitionOffset E := by
  induction ws with
  | nil => simp only [List.flatten_nil, ValuationWord.offset, Rat.cast_zero]
           unfold graftTransitionOffset
           positivity
  | cons w ws ih =>
      have hfirst := commonPrecision_offset (hw w (by simp))
      have ht := ih (fun v hv => hw v (by simp [hv]))
      have hm := mul_le_mul (stoppedWords_weight_le (hw w (by simp))) ht
        (Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg ws.flatten))
        (by norm_num : (0 : ℝ) ≤ 1 / 8)
      rw [List.flatten_cons, ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul]
      change (w.offset : ℝ) + Transfer.weight w * (ValuationWord.offset ws.flatten : ℝ) ≤ _
      unfold graftTransitionOffset at hm ⊢
      linarith

/-- Any fixed-precision transition concatenation has the full geometric offset bound. -/
theorem graftWords_offset {E n : ℕ} {w : ValuationWord} (hw : w ∈ graftWords E n) :
    (w.offset : ℝ) ≤ graftTransitionOffset E := by
  obtain ⟨ws, _, hws, rfl⟩ := (mem_graftWords E n w).mp hw
  exact graftBlocks_offset hws

/-- Both retained transition corridors preserve the same offset bound. -/
theorem graftTransitionWords_offset {δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) :
    (w.offset : ℝ) ≤ graftTransitionOffset (graftPrecision b t) :=
  graftWords_offset ((mem_graftTransitionWords δ b t w).mp hw).1

/-- The complete appended offset envelope is a finite fixed expression for each splice. -/
noncomputable def graftAppendedOffset (b t : ℕ) : ℝ :=
  graftTransitionOffset (graftPrecision b t) + (graftOffsetConstant : ℝ)

/-- The appended offset envelope is nonnegative. -/
theorem graftAppendedOffset_nonneg (b t : ℕ) : 0 ≤ graftAppendedOffset b t := by
  have hc := graftOffsetConstant_nonneg
  unfold graftAppendedOffset graftTransitionOffset
  positivity

/-- Later macroblocks use B_0 as their original starting count in the global offset series. -/
theorem graftAppended_offset {L δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) {ws : List ValuationWord}
    (hws : MacroHistory L δ (graftInitialCount b t) ws) :
    (ValuationWord.offset (w ++ ws.flatten) : ℝ) ≤ graftAppendedOffset b t := by
  have h := macroHistory_incoming_offset_le hws w (graftTransitionWords_weight hw)
  exact h.trans (add_le_add (graftTransitionWords_offset hw)
    continuationOffsetBound_le_graftOffsetConstant)

/-- The whole appended word pays one contraction per original block, including the transition. -/
theorem graftAppended_weight {L δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) {ws : List ValuationWord}
    (hws : MacroHistory L δ (graftInitialCount b t) ws) :
    Transfer.weight (w ++ ws.flatten) ≤
      (1 / 8 : ℝ) ^ macroCount L (graftInitialCount b t) ws.length := by
  have h := mul_le_mul (graftTransitionWords_weight hw) (macroHistory_weight_le hws)
    (Transfer.weight_pos ws.flatten).le (by positivity : (0 : ℝ) ≤
      (1 / 8 : ℝ) ^ graftInitialCount b t)
  have hc := macroCount_ge_start L (graftInitialCount b t) ws.length
  have he : graftInitialCount b t +
      (macroCount L (graftInitialCount b t) ws.length - graftInitialCount b t) =
      macroCount L (graftInitialCount b t) ws.length := by omega
  rw [← pow_add, he] at h
  simpa only [Transfer.weight, ValuationWord.slope_append, Rat.cast_mul] using h

/-- Transition and continuation corridors add at the actual total appended count. -/
theorem graftAppended_corridor {L δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) {ws : List ValuationWord}
    (hws : MacroHistory L δ (graftInitialCount b t) ws) :
    MacroCorridor δ (macroCount L (graftInitialCount b t) ws.length) (w ++ ws.flatten) := by
  have h := macroCorridor_append ((mem_graftTransitionWords δ b t w).mp hw).2
    (macroHistory_corridor hws)
  have hc := macroCount_ge_start L (graftInitialCount b t) ws.length
  have he : graftInitialCount b t +
      (macroCount L (graftInitialCount b t) ws.length - graftInitialCount b t) =
      macroCount L (graftInitialCount b t) ws.length := by omega
  simpa only [he] using h

end WordCertDensity.Construction
