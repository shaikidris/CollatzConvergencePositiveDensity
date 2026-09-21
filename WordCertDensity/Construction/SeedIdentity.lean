/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedExtension
import WordCertDensity.Construction.SeedIncrement

/-! # The exact signed increment of actual seed marks -/

namespace WordCertDensity.Construction

open scoped Classical

/-- At each actual parent, coarse transfer equals the full compatible physical child sum. -/
theorem seedCoarse_eq_children {b n root : ℕ} (hb : 32 ^ 5 ≤ b) (hr : 16 ^ b ≤ root)
    {ws : List ValuationWord} (hw : ws ∈ physicalSeedHistories b n root) :
    Transfer.coarseSelected (seedWords (seedSize b n)) (seedIncrementConductor (seedSize b n))
      (seedNextMarker (seedSize b n)) (fun _ hv => (seedIncrement_residual hv).ge)
      (seedHistorySource root ws : ZMod (3 ^ seedIncrementConductor (seedSize b n))) =
    ∑ w ∈ seedWords (seedSize b n),
      if ∃ source, PhysicalHistory w (seedHistorySource root ws) source then
        Transfer.weight w * Reference.marker (seedTailDepth b (n + 1))
          (seedHistorySource root (ws ++ [w]) : ZMod (3 ^ seedTailDepth b (n + 1)))
      else 0 := by
  obtain ⟨hs, hp⟩ := (mem_physicalSeedHistories b n root ws).mp hw
  obtain ⟨hlen, hblocks⟩ := (mem_seedBlockLists b 0 n ws).mp hs
  have hheight : 16 ^ seedSize b n ≤ seedHistorySource root ws := by
    simpa only [Nat.zero_add, hlen] using
      seedBlocks_source_height hb hblocks (show 16 ^ seedSize b 0 ≤ root from hr) hp
  have hB : 32 ^ 5 ≤ seedSize b n := hb.trans (seedSize_ge b n)
  rw [Transfer.coarseSelected]
  conv_rhs => rw [← Finset.sum_attach (seedWords (seedSize b n))]
  apply Finset.sum_congr rfl
  intro w _
  have hw' := w.property
  have hq : w.val.length ≤ seedIncrementConductor (seedSize b n) := by
    rw [((mem_seedWords w.val (seedSize b n)).mp hw').1]
    unfold seedIncrementConductor
    omega
  split_ifs with hc
  · obtain ⟨source, hc⟩ := hc
    rw [Transfer.wordOperator_of_physical hq hc, Reference.project_natCast]
    have he := seedHistorySource_snoc hp hc
    rw [he]
    rfl
  · have hoff := seedWords_offset_half (show 1 ≤ seedSize b n by omega) hheight hw'
    have hparent : (0 : ℚ) ≤ seedHistorySource root ws := Nat.cast_nonneg _
    exact Transfer.wordOperator_eq_zero_of_no_physical w.val hq _ hp.source_odd
      (by linarith) hc _

/-- The next mark is coarse transfer against the original incoming physical weights. -/
theorem physicalSeedMark_coarse {b root : ℕ} (hb : 32 ^ 5 ≤ b) (hr : 16 ^ b ≤ root)
    (n : ℕ) :
    physicalSeedMark b (n + 1) root =
      ∑ ws ∈ physicalSeedHistories b n root, Transfer.weight ws.flatten *
        Transfer.coarseSelected (seedWords (seedSize b n)) (seedIncrementConductor (seedSize b n))
          (seedNextMarker (seedSize b n)) (fun _ hv => (seedIncrement_residual hv).ge)
          (seedHistorySource root ws : ZMod (3 ^ seedIncrementConductor (seedSize b n))) := by
  rw [physicalSeedMark_snoc]
  apply Finset.sum_congr rfl
  intro ws hw
  rw [seedCoarse_eq_children hb hr hw]

/-- Successive physical marks have the literal signed incoming-histogram identity. -/
theorem physicalSeedMark_increment_identity {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    physicalSeedMark b (n + 1) root - physicalSeedMark b n root =
      ∑ y, Transfer.historyHistogram (physicalSeedHistories b n root) List.flatten
        (seedHistorySource root) (seedIncrementConductor (seedSize b n)) y *
          seedIncrementTest (seedSize b n) y := by
  rw [Transfer.historyHistogram_pair_eq, physicalSeedMark_coarse hb hr, physicalSeedMark,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ws _
  rw [seedIncrementTest, Reference.project_natCast, mul_sub]
  rfl

/-- Actual physical mark increments retain both mixing costs and the original failure mass. -/
theorem physicalSeedMark_increment_le {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
      (2 / 3 : ℝ) * seedCapacity b n *
        (Analytic.mixingError (seedNextMarker (seedSize b n)) +
          Analytic.mixingError (seedSize b n / 4) + 1 - Reference.stoppingMass (seedWords (seedSize b n))) := by
  rw [physicalSeedMark_increment_identity hb hr]
  exact seedIncrement_pairing_le hb n root

end WordCertDensity.Construction
