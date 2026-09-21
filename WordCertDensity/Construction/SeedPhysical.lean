/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedMarks
public import WordCertDensity.Construction.SeedCapacity

/-!
# The finite seed mark as an actual physical sum

At a sufficiently large odd root every compatible residue word is an actual
positive history. The finite physical sum retains its original weight and
marks its exact source at the terminal reference depth.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- Restricting the finite mean to units cancels exactly its factor two thirds. -/
theorem unitMean_seedMark {b : ℕ} (hb : 4 ≤ b) (n : ℕ) :
    (∑ y ∈ Finset.univ.filter (fun y : ZMod (3 ^ seedConductor b n) => IsUnit y),
      seedMark b n y) / (2 * (3 : ℝ) ^ (seedConductor b n - 1)) =
      ∏ j ∈ Finset.range n, Reference.stoppingMass (seedWords (seedSize b j)) := by
  classical
  have hs : (∑ y ∈ Finset.univ.filter (fun y : ZMod (3 ^ seedConductor b n) => IsUnit y),
      seedMark b n y) = ∑ y, seedMark b n y := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : IsUnit y
    · rw [if_pos hy]
    · rw [if_neg hy, seedMark_eq_zero_of_not_isUnit hb n y hy]
  rw [hs]
  have hm := mean_seedMark (show 0 < b by omega) n
  unfold Reference.mean at hm
  have hq := seedConductor_pos hb n
  have he : (3 : ℝ) ^ seedConductor b n = 3 ^ (seedConductor b n - 1) * 3 := by
    conv_lhs => rw [show seedConductor b n = (seedConductor b n - 1) + 1 by omega]
    rw [pow_succ]
  rw [div_eq_iff (by positivity), he] at hm
  rw [div_eq_iff (by positivity)]
  nlinarith [hm]

/-- The physical seed mark retains all actual histories and their exact source markers. -/
noncomputable def physicalSeedMark (b n root : ℕ) : ℝ :=
  ∑ ws ∈ physicalSeedHistories b n root,
    Transfer.weight ws.flatten * Reference.marker (seedTailDepth b n)
      (seedHistorySource root ws : ZMod (3 ^ seedTailDepth b n))

/-- The uniform seed height guard dominates every complete seed offset. -/
theorem seedHistory_offset_lt_root {b n root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) {ws : List ValuationWord}
    (hw : ws ∈ seedBlockLists b 0 n) :
    ValuationWord.offset ws.flatten < (root : ℚ) := by
  have ho := seedBlocks_offset_lt hb ((mem_seedBlockLists b 0 n ws).mp hw).2
  have hg : (2 : ℚ) ^ (b + 1) ≤ 16 ^ b := by
    calc
      _ ≤ (2 : ℚ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have hroot : (16 : ℚ) ^ b ≤ root := by exact_mod_cast hr
  simpa only [seedSize] using ho.trans_le (hg.trans hroot)

/-- A physical summand uses the exact terminal marker, with no loss of precision. -/
theorem seedOperator_of_physical {b n root : ℕ} {ws : List ValuationWord}
    (hw : ws ∈ physicalSeedHistories b n root) :
    Transfer.wordOperator ws.flatten (seedConductor b n)
      (Reference.marker (seedConductor b n - ws.flatten.length))
      (root : ZMod (3 ^ seedConductor b n)) =
    Transfer.weight ws.flatten * Reference.marker (seedTailDepth b n)
      (seedHistorySource root ws : ZMod (3 ^ seedTailDepth b n)) := by
  obtain ⟨hs, hp⟩ := (mem_physicalSeedHistories b n root ws).mp hw
  have hf : ws.flatten ∈ seedHistoryWords b 0 n := Finset.mem_image.mpr ⟨ws, hs, rfl⟩
  have hd := seedConductor_sub_length hf
  rw [Transfer.wordOperator_of_physical (seedHistoryWords_length_le hf) hp]
  congr 1
  exact congrArg (fun k => Reference.marker k (seedHistorySource root ws : ZMod (3 ^ k))) hd

/-- The residue seed mark equals the complete finite sum over actual physical histories. -/
theorem seedMark_eq_physicalSeedMark {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) (n : ℕ) :
    seedMark b n (root : ZMod (3 ^ seedConductor b n)) = physicalSeedMark b n root := by
  classical
  unfold seedMark Transfer.selected seedHistoryWords
  rw [Finset.sum_image]
  · unfold physicalSeedMark physicalSeedHistories
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ws hw
    by_cases hp : ∃ source, PhysicalHistory ws.flatten root source
    · rw [if_pos hp]
      apply seedOperator_of_physical
      exact Finset.mem_filter.mpr ⟨hw, hp⟩
    · rw [if_neg hp]
      have hf : ws.flatten ∈ seedHistoryWords b 0 n :=
        Finset.mem_image.mpr ⟨ws, hw, rfl⟩
      exact Transfer.wordOperator_eq_zero_of_no_physical ws.flatten
        (seedHistoryWords_length_le hf) root hodd (seedHistory_offset_lt_root hb hr hw) hp _
  · intro us hu vs hv he
    exact seedBlocks_flatten_injective (by omega) ((mem_seedBlockLists b 0 n us).mp hu).2
      ((mem_seedBlockLists b 0 n vs).mp hv).2 he

/-- The physical sum inherits the exact finite reference cap whenever the root is guarded. -/
theorem physicalSeedMark_le_marker {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) (n : ℕ) :
    physicalSeedMark b n root ≤
      Reference.marker (seedConductor b n) (root : ZMod (3 ^ seedConductor b n)) := by
  rw [← seedMark_eq_physicalSeedMark hb hr hodd]
  exact seedMark_le_marker b n _

end WordCertDensity.Construction
