/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.ScheduledMass
import Mathlib.Tactic.Linarith

/-!
# Actual finite corridor macroblocks

At each original count B, retain the scheduled words inside both displacement
and ordinary-cost corridors. These finite families have no physical parent
parameter. Their original mass satisfies the precision-plus-corridor rejection
bound, and their actual maximal depth satisfies the scheduled depth budget.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter Asymptotics
open scoped Classical Topology

/-- The two retained, non-strict corridors for n original stopped blocks. -/
def MacroCorridor (δ : ℝ) (n : ℕ) (w : ValuationWord) : Prop :=
  |displacement w - (n : ℝ) * stoppedExpectation displacement| ≤ δ * n ∧
    |(w.ordinaryCost : ℝ) - (n : ℝ) * stoppedExpectation (fun v => v.ordinaryCost)| ≤ δ * n

/-- The actual finite macroblock family uses the original count and both corridors. -/
noncomputable def macroblocks (L δ : ℝ) (B : ℕ) : Finset ValuationWord :=
  (scheduledWords B (macroLength L B)).filter (MacroCorridor δ (macroLength L B))

/-- The reference mass is the original finite geometric sum, with no conditioning. -/
noncomputable def macroblockMass (L δ : ℝ) (B : ℕ) : ℝ :=
  Reference.stoppingMass (macroblocks L δ B)

/-- Actual maximal depth, including the zero convention for an empty family. -/
noncomputable def macroblockDepth (L δ : ℝ) (B : ℕ) : ℕ :=
  (macroblocks L δ B).sup List.length

/-- Membership gives precisely a valid prescribed-count parsing and both corridors. -/
theorem mem_macroblocks (L δ : ℝ) (B : ℕ) (w : ValuationWord) :
    w ∈ macroblocks L δ B ↔
      (∃ ws : List ValuationWord, ws.length = macroLength L B ∧
        ScheduledBlocks B ws ∧ ws.flatten = w) ∧ MacroCorridor δ (macroLength L B) w := by
  simp only [macroblocks, Finset.mem_filter, mem_scheduledWords]

/-- Corridor restriction preserves the original finite scheduled family. -/
theorem macroblocks_subset (L δ : ℝ) (B : ℕ) :
    macroblocks L δ B ⊆ scheduledWords B (macroLength L B) :=
  Finset.filter_subset _ _

/-- Fixed-count parsing makes the actual corridor family prefix-free. -/
theorem macroblocks_prefixFree (L δ : ℝ) (B : ℕ) :
    (macroblocks L δ B : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) :=
  scheduledWords_subset_prefixFree (macroblocks_subset L δ B)

/-- Actual finite-family mass lies in the probability interval. -/
theorem macroblockMass_bounds (L δ : ℝ) (B : ℕ) :
    0 ≤ macroblockMass L δ B ∧ macroblockMass L δ B ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _,
    Reference.stoppingMass_le_one _ (macroblocks_prefixFree L δ B)⟩

/-- Finite filtering retains exactly the probability of the original stopped-copy event. -/
theorem macroblocks_probability (L δ : ℝ) (B : ℕ) :
    Gated.probability (stoppedCopiesPMF (macroLength L B))
      (fun ws => ScheduledBlocks B ws ∧ MacroCorridor δ (macroLength L B) ws.flatten) =
      macroblockMass L δ B :=
  scheduledWords_gate_probability B (macroLength L B) (MacroCorridor δ (macroLength L B))

/-- The complement of the actual word corridor has the existing strict four-tail bound. -/
theorem macroCorridor_rejection_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Gated.probability (stoppedCopiesPMF n) (fun ws => ¬ MacroCorridor δ n ws.flatten) ≤
      4 * Real.exp (-stoppedCorridorRate δ * n) := by
  simpa only [MacroCorridor, not_and_or, not_le, displacement_flatten,
    ordinaryCost_flatten] using stoppedCopies_corridor_le n hδ

/-- The actual macroblock deficit is bounded by precision rejection plus corridor rejection. -/
theorem macroblockMass_deficit_le (L : ℝ) {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    1 - macroblockMass L δ B ≤ macroDeficitEnvelope L (stoppedCorridorRate δ) B := by
  rw [← macroblocks_probability, ← Gated.probability_compl]
  have hsplit := Gated.probability_mono_on_support (stoppedCopiesPMF (macroLength L B))
    (fun ws => ¬ (ScheduledBlocks B ws ∧ MacroCorridor δ (macroLength L B) ws.flatten))
    (fun ws => ¬ ScheduledBlocks B ws ∨ ¬ MacroCorridor δ (macroLength L B) ws.flatten)
    (fun _ _ h => not_and_or.mp h)
  exact hsplit.trans ((Gated.probability_or_le _ _ _).trans
    (add_le_add (scheduledBlocks_rejection_le B (macroLength L B))
      (macroCorridor_rejection_le (macroLength L B) hδ)))

/-- The actual deficit has a uniform inverse-ninth-power bound at every original count. -/
theorem macroblockMass_deficit_bounds {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (B : ℕ) :
    0 ≤ 1 - macroblockMass L δ B ∧
      1 - macroblockMass L δ B ≤ (L + 5) * ((B : ℝ) + 2) ^ (-9 : ℝ) :=
  ⟨sub_nonneg.mpr (macroblockMass_bounds L δ B).2,
    (macroblockMass_deficit_le L hδ B).trans
      (macroDeficitEnvelope_bounds hL (stoppedCorridorRate_pos hδ).le hpay B).2⟩

/-- This is the manuscript's asymptotic deficit for the actual retained family. -/
theorem macroblockMass_deficit_isBigO {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    (fun B => 1 - macroblockMass L δ B) =O[atTop]
      (fun B : ℕ => ((B : ℝ) + 2) ^ (-9 : ℝ)) := by
  apply IsBigO.of_bound (L + 5)
  apply Filter.Eventually.of_forall
  intro B
  rw [Real.norm_eq_abs, abs_of_nonneg (macroblockMass_deficit_bounds hL hδ hpay B).1,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (macroblockMass_deficit_bounds hL hδ hpay B).2

/-- Actual nonnegative losses are summable even over every integer original count. -/
theorem summable_macroblockMass_deficit {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    Summable (fun B => 1 - macroblockMass L δ B) :=
  (summable_macroDeficitEnvelope hL (stoppedCorridorRate_pos hδ).le hpay).of_nonneg_of_le
    (fun B => (macroblockMass_deficit_bounds hL hδ hpay B).1)
    (fun B => macroblockMass_deficit_le L hδ B)

/-- The actual finite-family masses tend to one under the paid corridor guard. -/
theorem tendsto_macroblockMass {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    Tendsto (macroblockMass L δ) atTop (𝓝 1) := by
  have ht := (summable_macroblockMass_deficit hL hδ hpay).tendsto_atTop_zero
  have h : Tendsto (fun B => (1 : ℝ) - (1 - macroblockMass L δ B))
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub ht
  simpa only [sub_sub_cancel, sub_zero] using h

/-- A single eventual original-count cutoff gives strictly positive retained mass. -/
theorem eventually_macroblockMass_pos {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ B in atTop, 0 < macroblockMass L δ B :=
  (tendsto_order.mp (tendsto_macroblockMass hL hδ hpay)).1 0 (by norm_num)

/-- Along every actual macro schedule, the original deficits are still summable. -/
theorem summable_macroblockMass_deficit_schedule {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (B₀ : ℕ) :
    Summable (fun j => 1 - macroblockMass L δ (macroCount L B₀ j)) :=
  (summable_macroblockMass_deficit hL.le hδ hpay).comp_injective
    (macroCount_strictMono hL B₀).injective

/-- Every actual retained word has depth below the literal sum of precision budgets. -/
theorem macroblocks_depth_le {L δ : ℝ} {B : ℕ} {w : ValuationWord}
    (hw : w ∈ macroblocks L δ B) :
    w.length ≤ scheduledDepthBudget B (macroLength L B) := by
  obtain ⟨⟨ws, hlen, hp, rfl⟩, _⟩ := (mem_macroblocks L δ B w).mp hw
  simpa only [hlen] using scheduledBlocks_depth_le hp

/-- Taking the actual maximum does not enlarge the prescribed integer budget. -/
theorem macroblockDepth_le (L δ : ℝ) (B : ℕ) :
    macroblockDepth L δ B ≤ scheduledDepthBudget B (macroLength L B) :=
  Finset.sup_le (fun _ hw => macroblocks_depth_le hw)

/-- The actual maximum depth has an explicit log-squared bound independent of B₀. -/
theorem macroblockDepth_le_log_sq {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) (B : ℕ) :
    (macroblockDepth L δ B : ℝ) ≤
      (2000 * (L + 2) * (2 * L + 5)) * Real.log ((B : ℝ) + 2) ^ 2 :=
  (Nat.cast_le.mpr (macroblockDepth_le L δ B)).trans (macroDepth_le_log_sq hL B)

/-- The actual maximum depth satisfies the manuscript's asymptotic statement. -/
theorem macroblockDepth_isBigO {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    (fun B : ℕ => (macroblockDepth L δ B : ℝ)) =O[atTop]
      (fun B : ℕ => Real.log ((B : ℝ) + 2) ^ 2) := by
  apply IsBigO.of_bound (2000 * (L + 2) * (2 * L + 5))
  apply Filter.Eventually.of_forall
  intro B
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  exact macroblockDepth_le_log_sq hL δ B

end WordCertDensity.Construction
