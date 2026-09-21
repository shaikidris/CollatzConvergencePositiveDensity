/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftWords
import WordCertDensity.Construction.GraftScales
import WordCertDensity.Construction.Macroblocks
import WordCertDensity.Transfer.Stopped

/-! # The actual parent-independent graft transition

The finite family uses the literal rounded precision and count and both
stopped-mean corridors. Its original mass pays precision and corridor rejection.
At the enlarged incoming conductor, finite stopping retains both mixing costs.
The selected reference operator is not yet identified with physical extensions.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The manuscript's transition at splice t, with both original stopped-mean corridors. -/
noncomputable def graftTransitionWords (δ : ℝ) (b t : ℕ) : Finset ValuationWord :=
  (graftWords (graftPrecision b t) (graftInitialCount b t)).filter
    (MacroCorridor δ (graftInitialCount b t))

/-- The transition retains original reference mass, without survival normalization. -/
noncomputable def graftTransitionMass (δ : ℝ) (b t : ℕ) : ℝ :=
  Reference.stoppingMass (graftTransitionWords δ b t)

/-- The literal precision-plus-corridor rejection envelope. -/
noncomputable def graftTransitionFailure (δ : ℝ) (b t : ℕ) : ℝ :=
  (graftInitialCount b t : ℝ) * (2 : ℝ) ^ (-(graftPrecision b t : ℝ) / 100) +
    4 * Real.exp (-stoppedCorridorRate δ * graftInitialCount b t)

/-- Membership records both the actual stopped blocks and the terminal-free transition corridor. -/
theorem mem_graftTransitionWords (δ : ℝ) (b t : ℕ) (w : ValuationWord) :
    w ∈ graftTransitionWords δ b t ↔
      w ∈ graftWords (graftPrecision b t) (graftInitialCount b t) ∧
        MacroCorridor δ (graftInitialCount b t) w := by
  simp only [graftTransitionWords, Finset.mem_filter]

/-- Corridor filtering preserves the prescribed-count prefix-free family. -/
theorem graftTransitionWords_prefixFree (δ : ℝ) (b t : ℕ) :
    (graftTransitionWords δ b t : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v) := by
  intro u hu v hv hne hp
  exact graftWords_prefixFree (graftPrecision b t) (graftInitialCount b t)
    ((mem_graftTransitionWords δ b t u).mp hu).1
    ((mem_graftTransitionWords δ b t v).mp hv).1 hne hp

/-- Original mass lies in the probability interval, including empty retained families. -/
theorem graftTransitionMass_bounds (δ : ℝ) (b t : ℕ) :
    0 ≤ graftTransitionMass δ b t ∧ graftTransitionMass δ b t ≤ 1 :=
  ⟨Reference.stoppingMass_nonneg _,
    Reference.stoppingMass_le_one _ (graftTransitionWords_prefixFree δ b t)⟩

/-- Every retained word fits in the original quarter-depth transition budget. -/
theorem graftTransitionWords_depth {δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) : w.length ≤ seedSize b t / 4 :=
  (graftWords_depth_le ((mem_graftTransitionWords δ b t w).mp hw).1).trans
    (graftTransition_depth b t)

/-- The transition pays the B_0 stopped contractions before continuation starts. -/
theorem graftTransitionWords_weight {δ : ℝ} {b t : ℕ} {w : ValuationWord}
    (hw : w ∈ graftTransitionWords δ b t) :
    Transfer.weight w ≤ (1 / 8 : ℝ) ^ graftInitialCount b t :=
  graftWords_weight_le ((mem_graftTransitionWords δ b t w).mp hw).1

/-- The transition is the original complete stopped-copy event, not a conditioned law. -/
theorem graftTransitionWords_probability (δ : ℝ) (b t : ℕ) :
    Gated.probability (stoppedCopiesPMF (graftInitialCount b t))
      (fun ws => (∀ w ∈ ws, w ∈ stoppedWords (graftPrecision b t)) ∧
        MacroCorridor δ (graftInitialCount b t) ws.flatten) = graftTransitionMass δ b t :=
  graftWords_gate_probability _ _ _

/-- The original deficit pays the precision and both coordinate-corridor failures. -/
theorem graftTransitionMass_deficit {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    1 - graftTransitionMass δ b t ≤ graftTransitionFailure δ b t := by
  rw [← graftTransitionWords_probability, ← Gated.probability_compl]
  have hsplit := Gated.probability_mono_on_support (stoppedCopiesPMF (graftInitialCount b t))
    (fun ws => ¬ ((∀ w ∈ ws, w ∈ stoppedWords (graftPrecision b t)) ∧
      MacroCorridor δ (graftInitialCount b t) ws.flatten))
    (fun ws => ¬ (∀ w ∈ ws, w ∈ stoppedWords (graftPrecision b t)) ∨
      ¬ MacroCorridor δ (graftInitialCount b t) ws.flatten)
    (fun _ _ h => not_and_or.mp h)
  have hprecision := mul_le_mul_of_nonneg_left
    ((stoppedWords_timeout (graftPrecision b t) (graftPrecision_ge_256 hb t)).1.trans
      (stoppedWords_timeout (graftPrecision b t) (graftPrecision_ge_256 hb t)).2)
    (Nat.cast_nonneg (graftInitialCount b t) : (0 : ℝ) ≤ graftInitialCount b t)
  exact hsplit.trans ((Gated.probability_or_le _ _ _).trans
    (add_le_add ((graftBlocks_rejection_le _ _).trans hprecision)
      (macroCorridor_rejection_le _ hδ)))

/-- The literal enlarged conductor leaves room for the new marker after every retained word. -/
theorem graftTransitionWords_level {b : ℕ} (hb : 256 ^ 2 ≤ b) (δ : ℝ) (t : ℕ)
    (w : ValuationWord) (hw : w ∈ graftTransitionWords δ b t) :
    macroLevel (graftInitialCount b t) ≤ 2 * seedSize b t - w.length := by
  have hd := graftWords_depth_le ((mem_graftTransitionWords δ b t w).mp hw).1
  have hg := (graftTransition_level_guards hb t).2.2
  omega

/-- Finite stopping at Q=2b_t pays both marker discrepancies and the rejected original mass. -/
theorem graftTransition_reference_error {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    Reference.mean (2 * seedSize b t) (fun y =>
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (macroLevel (graftInitialCount b t)) (graftTransitionWords_level hb δ t) y -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards hb t).2.1 y)|) ≤
      (2 / 3 : ℝ) * (Analytic.mixingError (macroLevel (graftInitialCount b t)) +
        Analytic.mixingError (seedTailDepth b t) + graftTransitionFailure δ b t) := by
  have hold : 1 ≤ seedTailDepth b t := by
    have hs := seedSize_ge b t
    unfold seedTailDepth
    omega
  have hlen : ∀ w ∈ graftTransitionWords δ b t, w.length ≤ 2 * seedSize b t := by
    intro w hw
    have hd := graftTransitionWords_depth hw
    omega
  have he := Transfer.stopped_transfer_le (graftTransitionWords δ b t) hlen
    (graftTransitionWords_level hb δ t) (graftTransition_level_guards hb t).1
    hold (graftTransition_level_guards hb t).2.1 (graftTransitionWords_prefixFree δ b t)
  have hd := graftTransitionMass_deficit hδ hb t
  change 1 - Reference.stoppingMass (graftTransitionWords δ b t) ≤ _ at hd
  exact he.trans (by linarith)

end WordCertDensity.Construction
