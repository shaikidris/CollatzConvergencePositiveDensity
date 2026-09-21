/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.Macroblocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual retained macro histories and their cumulative corridors

A history consumes original blocks at the recursive current count. Flattening
retained macroblocks yields a valid original stopped-block schedule. Summed
corridors retain the incoming prefix explicitly, and the original schedule
supplies its slope and offset bounds. Depth and valuation are recovered from
the exact displacement and ordinary cost, before integer tag counting.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- No macro schedule decreases its original starting count, even at zero coefficient. -/
theorem macroCount_ge_start (L : ℝ) (B j : ℕ) : B ≤ macroCount L B j := by
  rw [macroCount_eq_sum]
  omega

/-- The first actual macro step can be absorbed into the starting count. -/
theorem macroCount_succ_start (L : ℝ) (B j : ℕ) :
    macroCount L B (j + 1) = macroCount L (B + macroLength L B) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun k => k + macroLength L k) ih

/-- Consumed original counts add, with natural subtraction justified by actual count growth. -/
theorem macroCount_consumed_succ (L : ℝ) (B j : ℕ) :
    macroCount L B (j + 1) - B = macroLength L B +
      (macroCount L (B + macroLength L B) j - (B + macroLength L B)) := by
  rw [macroCount_succ_start]
  have h := macroCount_ge_start L (B + macroLength L B) j
  omega

/-- A retained history uses the actual finite family at each current original count. -/
def MacroHistory (L δ : ℝ) : ℕ → List ValuationWord → Prop
  | _, [] => True
  | B, w :: ws => w ∈ macroblocks L δ B ∧ MacroHistory L δ (B + macroLength L B) ws

/-- Joining retained histories starts the second history at the count consumed by the first. -/
theorem macroHistory_append (L δ : ℝ) (B : ℕ) (ws vs : List ValuationWord) :
    MacroHistory L δ B (ws ++ vs) ↔ MacroHistory L δ B ws ∧
      MacroHistory L δ (macroCount L B ws.length) vs := by
  induction ws generalizing B with
  | nil => simp [MacroHistory, macroCount]
  | cons w ws ih =>
      simp only [List.cons_append, MacroHistory, ih, List.length_cons,
        macroCount_succ_start, and_assoc]

/-- Every actual macro history has a valid original-block parsing with the exact total count. -/
theorem macroHistory_originalBlocks {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) :
    ∃ us : List ValuationWord, ScheduledBlocks B us ∧ us.flatten = ws.flatten ∧
      B + us.length = macroCount L B ws.length := by
  induction ws generalizing B with
  | nil => exact ⟨[], trivial, rfl, by simp [macroCount]⟩
  | cons w ws ih =>
      obtain ⟨hw, ht⟩ := h
      obtain ⟨⟨us, hul, hup, hue⟩, _⟩ := (mem_macroblocks L δ B w).mp hw
      obtain ⟨vs, hvp, hve, hvc⟩ := ih ht
      refine ⟨us ++ vs, ?_, ?_, ?_⟩
      · apply (scheduledBlocks_append B us vs).mpr
        exact ⟨hup, by simpa only [hul] using hvp⟩
      · simp only [List.flatten_append, List.flatten_cons, hue, hve]
      · simp only [List.length_append, List.length_cons, macroCount_succ_start]
        omega

/-- The flattened history belongs to the actual prescribed-count finite original family. -/
theorem macroHistory_mem_scheduledWords {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) :
    ws.flatten ∈ scheduledWords B (macroCount L B ws.length - B) := by
  obtain ⟨us, hup, hue, huc⟩ := macroHistory_originalBlocks h
  exact (mem_scheduledWords _ _ _).mpr ⟨us, by omega, hup, hue⟩

private theorem displacement_join (u v : ValuationWord) :
    displacement (u ++ v) = displacement u + displacement v := by
  simpa using displacement_flatten [u, v]

private theorem add_corridor {x y μ δ : ℝ} {n m : ℕ}
    (hx : |x - (n : ℝ) * μ| ≤ δ * n) (hy : |y - (m : ℝ) * μ| ≤ δ * m) :
    |x + y - ((n + m : ℕ) : ℝ) * μ| ≤ δ * (n + m : ℕ) := by
  have he : x + y - ((n + m : ℕ) : ℝ) * μ =
      (x - (n : ℝ) * μ) + (y - (m : ℝ) * μ) := by push_cast; ring
  rw [he]
  calc
    _ ≤ |x - (n : ℝ) * μ| + |y - (m : ℝ) * μ| := abs_add_le _ _
    _ ≤ δ * n + δ * m := add_le_add hx hy
    _ = _ := by push_cast; ring

/-- Concatenating two retained corridors adds their original block counts. -/
theorem macroCorridor_append {δ : ℝ} {n m : ℕ} {u v : ValuationWord}
    (hu : MacroCorridor δ n u) (hv : MacroCorridor δ m v) :
    MacroCorridor δ (n + m) (u ++ v) := by
  constructor
  · rw [displacement_join]
    exact add_corridor hu.1 hv.1
  · rw [ValuationWord.ordinaryCost_append, Nat.cast_add]
    exact add_corridor hu.2 hv.2

/-- Every retained history satisfies both summed corridors at its actual consumed count. -/
theorem macroHistory_corridor {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) :
    MacroCorridor δ (macroCount L B ws.length - B) ws.flatten := by
  induction ws generalizing B with
  | nil => simp [macroCount, MacroCorridor, displacement, ValuationWord.total,
      ValuationWord.ordinaryCost]
  | cons w ws ih =>
      have hc := macroCorridor_append ((mem_macroblocks L δ B w).mp h.1).2 (ih h.2)
      simpa only [List.length_cons, macroCount_consumed_succ, List.flatten_cons] using hc

/-- A fixed incoming prefix contributes its exact additive displacement and cost constants. -/
theorem macroHistory_incoming_corridors {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) (incoming : ValuationWord) :
    |displacement (incoming ++ ws.flatten) - displacement incoming -
      ((macroCount L B ws.length - B : ℕ) : ℝ) * stoppedExpectation displacement| ≤
        δ * (macroCount L B ws.length - B : ℕ) ∧
    |(ValuationWord.ordinaryCost (incoming ++ ws.flatten) : ℝ) -
      (incoming.ordinaryCost : ℝ) - ((macroCount L B ws.length - B : ℕ) : ℝ) *
        stoppedExpectation (fun w => w.ordinaryCost)| ≤
          δ * (macroCount L B ws.length - B : ℕ) := by
  have hy : displacement (incoming ++ ws.flatten) - displacement incoming =
      displacement ws.flatten := by rw [displacement_join]; ring
  have hr : (ValuationWord.ordinaryCost (incoming ++ ws.flatten) : ℝ) -
      (incoming.ordinaryCost : ℝ) = (ValuationWord.ordinaryCost ws.flatten : ℝ) := by
    rw [ValuationWord.ordinaryCost_append, Nat.cast_add]
    ring
  rw [hy, hr]
  exact macroHistory_corridor h

/-- Retained macro histories inherit the contraction at the number of original blocks. -/
theorem macroHistory_weight_le {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) :
    Transfer.weight ws.flatten ≤ (1 / 8 : ℝ) ^ (macroCount L B ws.length - B) := by
  obtain ⟨us, hup, hue, huc⟩ := macroHistory_originalBlocks h
  have hn : us.length = macroCount L B ws.length - B := by omega
  simpa only [hue, hn] using scheduledBlocks_weight_le hup

/-- The incoming-count scaling preserves the one global offset envelope. -/
theorem macroHistory_scaled_offset_le {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) :
    (1 / 8 : ℝ) ^ B * (ValuationWord.offset ws.flatten : ℝ) ≤
      continuationOffsetBound := by
  obtain ⟨us, hup, hue, _⟩ := macroHistory_originalBlocks h
  rw [← hue]
  exact (scheduledBlocks_scaled_offset_le hup).trans (scheduledOffsetBudget_le B us.length)

/-- Actual incoming contraction pays the offset of every retained continuation. -/
theorem macroHistory_incoming_offset_le {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) (incoming : ValuationWord)
    (hweight : Transfer.weight incoming ≤ (1 / 8 : ℝ) ^ B) :
    (ValuationWord.offset (incoming ++ ws.flatten) : ℝ) ≤
      (incoming.offset : ℝ) + continuationOffsetBound := by
  obtain ⟨us, hup, hue, _⟩ := macroHistory_originalBlocks h
  rw [← hue]
  exact incoming_scheduled_offset_le B incoming hup hweight

/-- The actual word depth is recovered by the first coordinate identity in (S.tags). -/
theorem word_depth_coordinates (w : ValuationWord) :
    (w.length : ℝ) = ((w.ordinaryCost : ℝ) - displacement w) / (1 + Head.logRatio) := by
  apply (eq_div_iff (show (1 + Head.logRatio : ℝ) ≠ 0 by
    linarith [Head.one_lt_logRatio])).mpr
  simp only [ValuationWord.ordinaryCost, displacement, Nat.cast_add]
  ring

/-- The actual total valuation is recovered by the second identity in (S.tags). -/
theorem word_total_coordinates (w : ValuationWord) :
    (w.total : ℝ) = (Head.logRatio * (w.ordinaryCost : ℝ) + displacement w) /
      (1 + Head.logRatio) := by
  apply (eq_div_iff (show (1 + Head.logRatio : ℝ) ≠ 0 by
    linarith [Head.one_lt_logRatio])).mpr
  simp only [ValuationWord.ordinaryCost, displacement, Nat.cast_add]
  ring

end WordCertDensity.Construction
