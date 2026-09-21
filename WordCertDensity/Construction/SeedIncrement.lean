/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedCapacity
import WordCertDensity.Transfer.CapacityPairing

/-! # The seed increment's actual conductor and signed residue comparison -/

namespace WordCertDensity.Construction

/-- The marker precision after one further seed block. -/
def seedNextMarker (B : ℕ) : ℕ := (B + B / 100) / 4

/-- The local conductor paid when comparing successive seed marks. -/
def seedIncrementConductor (B : ℕ) : ℕ := B + seedNextMarker B

/-- Every seed word leaves exactly the next marker precision. -/
theorem seedIncrement_residual {B : ℕ} {w : ValuationWord} (hw : w ∈ seedWords B) :
    seedIncrementConductor B - w.length = seedNextMarker B := by
  rw [((mem_seedWords w B).mp hw).1, seedIncrementConductor, Nat.add_sub_cancel_left]

/-- The old marker fits inside the local increment conductor. -/
theorem seedIncrement_old_le (B : ℕ) : B / 4 ≤ seedIncrementConductor B := by
  unfold seedIncrementConductor
  omega

/-- Both marker levels are positive and the next level is at least the old one. -/
theorem seedIncrement_marker_guards {B : ℕ} (hB : 8 ≤ B) :
    1 ≤ B / 4 ∧ B / 4 ≤ seedNextMarker B ∧ 1 ≤ seedNextMarker B := by
  unfold seedNextMarker
  omega

/-- The floor loses at most half the nominal quarter-depth precision. -/
theorem seedIncrement_old_lower {B : ℕ} (hB : 8 ≤ B) : (B : ℝ) / 8 ≤ (B / 4 : ℕ) := by
  have hf : B ≤ 4 * (B / 4) + 3 := by omega
  have hf' : (B : ℝ) ≤ 4 * (B / 4 : ℕ) + 3 := by exact_mod_cast hf
  have hb' : (8 : ℝ) ≤ B := by exact_mod_cast hB
  linarith

/-- The exact local conductor remains below its printed rational multiple of the block depth. -/
theorem seedIncrement_conductor_le (B : ℕ) :
    (seedIncrementConductor B : ℝ) ≤ (501 / 400 : ℝ) * B := by
  have h1 : 100 * (B / 100) ≤ B := by omega
  have h2 : 4 * seedNextMarker B ≤ B + B / 100 := by unfold seedNextMarker; omega
  have h1' : (100 : ℝ) * (B / 100 : ℕ) ≤ B := by exact_mod_cast h1
  have h2' : (4 : ℝ) * seedNextMarker B ≤ B + (B / 100 : ℕ) := by exact_mod_cast h2
  unfold seedIncrementConductor
  push_cast
  linarith

/-- Positive block depth makes the comparison conductor strictly smaller than twice the depth. -/
theorem seedIncrement_conductor_lt {B : ℕ} (hB : 0 < B) : seedIncrementConductor B < 2 * B := by
  have hb' : (0 : ℝ) < B := by exact_mod_cast hB
  have h := seedIncrement_conductor_le B
  have hr : (seedIncrementConductor B : ℝ) < 2 * B := by linarith
  exact_mod_cast hr

/-- The signed local test uses the same root-independent seed family for every parent. -/
noncomputable def seedIncrementTest (B : ℕ) (y : ZMod (3 ^ seedIncrementConductor B)) : ℝ :=
  Transfer.coarseSelected (seedWords B) (seedIncrementConductor B) (seedNextMarker B)
    (fun _ hw => (seedIncrement_residual hw).ge) y -
      Reference.marker (B / 4) (Reference.project (seedIncrement_old_le B) y)

/-- The signed local test retains both mixing costs and the original seed failure. -/
theorem seedIncrementTest_mean_le {B : ℕ} (hB : 8 ≤ B) :
    Reference.mean (seedIncrementConductor B) (fun y => |seedIncrementTest B y|) ≤
      (2 / 3 : ℝ) * (Analytic.mixingError (seedNextMarker B) + Analytic.mixingError (B / 4) +
        1 - Reference.stoppingMass (seedWords B)) := by
  exact Transfer.stopped_transfer_le (seedWords B)
    (fun w hw => by
      rw [((mem_seedWords w B).mp hw).1]
      unfold seedIncrementConductor
      omega)
    (fun _ hw => (seedIncrement_residual hw).ge)
    (seedIncrement_marker_guards hB).2.2 (seedIncrement_marker_guards hB).1
    (seedIncrement_old_le B) (seedWords_prefixFree B)

/-- Actual incoming histories pair with the signed local test under the retained seed capacity. -/
theorem seedIncrement_pairing_le {b : ℕ} (hb : 32 ^ 5 ≤ b) (j root : ℕ) :
    |∑ y, Transfer.historyHistogram (physicalSeedHistories b j root) List.flatten
      (seedHistorySource root) (seedIncrementConductor (seedSize b j)) y *
        seedIncrementTest (seedSize b j) y| ≤
      (2 / 3 : ℝ) * seedCapacity b j *
        (Analytic.mixingError (seedNextMarker (seedSize b j)) +
          Analytic.mixingError (seedSize b j / 4) + 1 - Reference.stoppingMass (seedWords (seedSize b j))) := by
  have hB := hb.trans (seedSize_ge b j)
  have hq := (seedIncrement_conductor_lt (show 0 < seedSize b j by omega)).le
  have hp := Transfer.capacity_pairing (seedIncrementConductor (seedSize b j))
    (Transfer.historyHistogram (physicalSeedHistories b j root) List.flatten (seedHistorySource root) _)
    (seedIncrementTest (seedSize b j))
    (Transfer.historyHistogram_nonneg _ _ _ _)
    (fun y => physicalSeedHistories_capacity _ hb (Finset.Subset.refl _) _ hq y)
  have hc : 0 ≤ seedCapacity b j := (seedTagBudget_nonneg b j).trans (seedTagBudget_le_capacity b j)
  have hm := mul_le_mul_of_nonneg_left (seedIncrementTest_mean_le (show 8 ≤ seedSize b j by omega)) hc
  apply hp.trans
  convert! hm using 1
  ring

end WordCertDensity.Construction
