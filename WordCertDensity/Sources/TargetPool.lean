/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Sources.Target
import WordCertDensity.Construction.BlockPersistentMark
import WordCertDensity.Roots.PredecessorBounds

/-! # Actual all-scale sources for every admissible fixed target

Two adjacent complete unit predecessor blocks of an odd unit target realise the
same residues, so the persistent residue vector supplies a common score on
whichever of them is nonrecurrent. The explicit start pays the seed height and
the incoming dyadic path guard together, which covers even targets through the
odd-part decomposition.

No hypothesis that the target reaches one is used, and no shared-allocation
optimiser is required.
-/

namespace WordCertDensity.Sources

open Construction Roots

/-- One complete nonrecurrent unit block supplies actual sources for the dyadic target. -/
theorem dyadicBlockSources {b v y j : ℕ} {K : ℚ} (hb : 32 ^ 5 ≤ b)
    (hy : ¬ 3 ∣ y) (hjle : j ≤ 1) (hK : 0 < K)
    (hKmass : (K : ℝ) ≤ ∑ r ∈ unitResidues (seedConductor b (seedStartupIndex b hb)),
      blockPersistentMark b hb r)
    (hP : NonrecurrentPool acceleratedStep
      (↑(unitPredecessorBlock y (seedConductor b (seedStartupIndex b hb))
        (predecessorStart b v + j * 3 ^ seedConductor b (seedStartupIndex b hb))) : Set ℕ)) :
    AllScaleSources (2 ^ v * y)
      ((predecessorScore (27 / 2 ^ 27 : ℚ) K y (seedConductor b (seedStartupIndex b hb))
        (predecessorStart b v) : ℚ) : ℝ) := by
  classical
  have hq : 0 < seedConductor b (seedStartupIndex b hb) :=
    seedConductor_pos (by omega) _
  refine targetPoolSources (b := b) (N := seedStartupIndex b hb)
    (z := fun r => blockPersistentMark b hb
      (r % 3 ^ seedConductor b (seedStartupIndex b hb)))
    hb ?_ hP ?_ ?_ ?_ ?_
  · exact_mod_cast predecessorScore_pos (by norm_num) hK hy _ _
  · intro root hroot
    exact unitPredecessorBlock_height hy hroot
  · intro root hroot
    have hv : v ≤ predecessorStart b v + j * 3 ^ seedConductor b (seedStartupIndex b hb) := by
      have hstart : v ≤ predecessorStart b v := by
        unfold predecessorStart
        exact Nat.le_add_left v (16 ^ b)
      exact hstart.trans (Nat.le_add_right _ _)
    obtain ⟨t, _, _, hreach⟩ := unitPredecessorBlock_reaches hy hv hroot
    exact ⟨_, hreach⟩
  · intro i hi root hroot
    exact blockPersistentMark_le_physical hb (unitPredecessorBlock_height hy hroot)
      (unitPredecessorBlock_physical hy hroot).2 hi
  · exact predecessorScore_le_sum hy hq hjle (27 / 2 ^ 27 : ℚ) K (blockPersistentMark b hb)
      (fun r _ => blockPersistentMark_nonneg b hb r) hKmass

/-- Every odd unit target, and every dyadic multiple of one, has a positive
small score with actual sources at every scale and every larger clock. -/
theorem dyadicUnitTargetSources {v y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) :
    ∃ W : ℝ, 0 < W ∧ W ≤ 27 / 2 ^ 27 ∧ AllScaleSources (2 ^ v * y) W := by
  classical
  have hb : 32 ^ 5 ≤ survivalSeedSize := by rfl
  have hmass := survival_unitResidues_mass hb
  have hres : 0 < seedStartupResidual survivalSeedSize hb := (seedStartup_spec _ hb).2.2
  have hzero : (0 : ℝ) < ∑ r ∈ unitResidues (seedConductor survivalSeedSize
      (seedStartupIndex survivalSeedSize hb)), blockPersistentMark survivalSeedSize hb r := by
    refine lt_of_le_of_lt ?_ hmass
    positivity
  obtain ⟨K, hK0, hKlt⟩ := exists_rat_btwn hzero
  have hK : 0 < K := by exact_mod_cast hK0
  refine ⟨((predecessorScore (27 / 2 ^ 27 : ℚ) K y (seedConductor survivalSeedSize
    (seedStartupIndex survivalSeedSize hb)) (predecessorStart survivalSeedSize v) : ℚ) : ℝ),
    by exact_mod_cast predecessorScore_pos (by norm_num) hK hy _ _, ?_, ?_⟩
  · have hle := (Rat.cast_le (K := ℝ)).2
      (predecessorScore_le (27 / 2 ^ 27 : ℚ) K y
        (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb))
        (predecessorStart survivalSeedSize v))
    push_cast at hle
    exact hle
  obtain h0 | h1 := exists_nonrecurrent_unitPredecessorBlock hy hodd
    (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb))
    (predecessorStart survivalSeedSize v)
  · exact dyadicBlockSources (j := 0) hb hy (by norm_num) hK hKlt.le (by simpa using h0)
  · exact dyadicBlockSources (j := 1) hb hy (by norm_num) hK hKlt.le (by simpa using h1)

/-- Every positive target not divisible by three has actual all-scale sources. -/
theorem admissibleTargetSources {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ W : ℝ, 0 < W ∧ W ≤ 27 / 2 ^ 27 ∧ AllScaleSources n W := by
  obtain ⟨v, y, hyodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  exact dyadicUnitTargetSources (v := v) (fun h => h3 (h.mul_left _)) hyodd

end WordCertDensity.Sources
