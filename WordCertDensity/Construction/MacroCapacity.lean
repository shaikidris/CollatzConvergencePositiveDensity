/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.CorridorTags
import Mathlib.Tactic.Linarith

/-!
# Capacity of actual retained histories

The incoming family pays its actual tag multiplicity and starting-count
contraction. Retained continuations provide the remaining contraction and
uniform offset envelope. Physicality and within-tag source uniqueness remain
explicit inputs to the existing physical-history capacity theorem.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- Incoming and continuation contraction combine at the final original count. -/
theorem macroHistory_incoming_weight_le {L δ : ℝ} {B : ℕ} {ws : List ValuationWord}
    (h : MacroHistory L δ B ws) (incoming : ValuationWord)
    (hpre : Transfer.weight incoming ≤ (1 / 8 : ℝ) ^ B) :
    Transfer.weight (incoming ++ ws.flatten) ≤ (1 / 8 : ℝ) ^ macroCount L B ws.length := by
  have hcount : B + (macroCount L B ws.length - B) = macroCount L B ws.length := by
    have hge := macroCount_ge_start L B ws.length
    omega
  calc
    _ = Transfer.weight incoming * Transfer.weight ws.flatten := by
      simp only [Transfer.weight, ValuationWord.slope_append, Rat.cast_mul]
    _ ≤ (1 / 8 : ℝ) ^ B * (1 / 8 : ℝ) ^ (macroCount L B ws.length - B) :=
      mul_le_mul hpre (macroHistory_weight_le h) (Transfer.weight_pos _).le (by positivity)
    _ = _ := by rw [← pow_add, hcount]

/-- Actual retained-history capacity keeps incoming tags, offsets and the residual point term. -/
theorem macroHistory_capacity {α : Type*} (H : Finset α)
    (incoming : α → ValuationWord) (history : α → List ValuationWord) (source : α → ℕ)
    {L δ C : ℝ} {B j M : ℕ} (q : ℕ) (a : ZMod (3 ^ q))
    (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hh : ∀ i ∈ H, MacroHistory L δ B (history i))
    (hj : ∀ i ∈ H, (history i).length = j)
    (hpre : ∀ i ∈ H, Transfer.weight (incoming i) ≤ (1 / 8 : ℝ) ^ B)
    (hoff : ∀ i ∈ H, ((incoming i).offset : ℝ) ≤ C)
    (hphysical : ∀ i ∈ H, PhysicalHistory (incoming i ++ (history i).flatten) M (source i))
    (hinj : ∀ i ∈ H, ∀ k ∈ H,
      Transfer.historyTag (incoming i ++ (history i).flatten) =
        Transfer.historyTag (incoming k ++ (history k).flatten) →
      source i = source k → i = k) :
    (3 : ℝ) ^ q * Transfer.historyHistogram H
      (fun i => incoming i ++ (history i).flatten) source q a ≤
      (((H.image (fun i => Transfer.historyTag (incoming i))).card : ℝ) *
        (2 * δ * (macroCount L B j - B : ℕ) + 1) ^ 2) *
          ((C + continuationOffsetBound) + (3 : ℝ) ^ q *
            (1 / 8 : ℝ) ^ macroCount L B j) := by
  have hw : ∀ i ∈ H, Transfer.weight (incoming i ++ (history i).flatten) ≤
      (1 / 8 : ℝ) ^ macroCount L B j := by
    intro i hi
    simpa only [hj i hi] using macroHistory_incoming_weight_le (hh i hi) (incoming i) (hpre i hi)
  have ho : ∀ i ∈ H, (0 : ℝ) ≤
      (ValuationWord.offset (incoming i ++ (history i).flatten) : ℝ) ∧
      (ValuationWord.offset (incoming i ++ (history i).flatten) : ℝ) ≤
        C + continuationOffsetBound := by
    intro i hi
    refine ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _), ?_⟩
    exact (macroHistory_incoming_offset_le (hh i hi) (incoming i) (hpre i hi)).trans
      (add_le_add (hoff i hi) (le_refl continuationOffsetBound))
  have hc := Transfer.history_capacity H (fun i => incoming i ++ (history i).flatten)
    source q a hphysical hinj hw (by positivity)
    (show 0 ≤ C + continuationOffsetBound from
      add_nonneg hC continuationOffsetBound_bounds.1) ho
    (macroHistory_incoming_tag_card H history incoming hδ hh hj)
  simpa only [sub_zero] using hc

end WordCertDensity.Construction
