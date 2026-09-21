/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedScore

/-! # Small-score domain of the unchanged canonical allocation minimum -/

namespace WordCertDensity.Construction

/-- The unit allocation is feasible and bounds the minimum by the complete
reciprocal root sum whenever p≤1. -/
theorem seedAllocationScore_le_reciprocals (b : ℕ) {q : ℕ} (hq : 0 < q)
    {p : ℝ} (hp : p ≤ 1) :
    seedAllocationScore b q p ≤ ∑ x ∈ seedRootPool b q, (x : ℝ)⁻¹ := by
  classical
  have hc : (Fintype.card {x // x ∈ seedRootPool b q} : ℝ) = 2 * (3 : ℝ) ^ (q - 1) := by
    rw [Fintype.card_coe, card_seedRootPool b hq]
    push_cast
    rfl
  have hcap : (1 : ℝ) ≤ (2 / 3 : ℝ) * 2 ^ q := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hq)
    norm_num only [pow_one] at h
    linarith
  have hm : (2 * (3 : ℝ) ^ (q - 1)) * p ≤
      (Fintype.card {x // x ∈ seedRootPool b q} : ℝ) * ((2 / 3 : ℝ) * 2 ^ q) := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left (hp.trans hcap) (by positivity)
  have hv : (fun _ : {x // x ∈ seedRootPool b q} => (1 : ℝ)) ∈
      Roots.allocationFeasible ((2 / 3 : ℝ) * 2 ^ q) ((2 * (3 : ℝ) ^ (q - 1)) * p) := by
    refine ⟨⟨fun _ => zero_le_one, fun _ => hcap⟩, ?_⟩
    change (2 * (3 : ℝ) ^ (q - 1)) * p ≤ ∑ _ : {x // x ∈ seedRootPool b q}, (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hc]
    exact mul_le_of_le_one_right (by positivity) hp
  have h := Roots.allocationScore_le (fun x : {x // x ∈ seedRootPool b q} => (x.val : ℝ)⁻¹)
    (by positivity) hm hv
  simp only [Roots.allocationObjective, mul_one] at h
  rw [Finset.sum_coe_sort (seedRootPool b q) (fun x : ℕ => (x : ℝ)⁻¹)] at h
  exact h

private theorem root_reciprocal_bound {b : ℕ} (hb : 1 ≤ b) (i : ℕ) :
    (Roots.value (2 * b + 1 + i) : ℝ)⁻¹ ≤ ((16 : ℝ) ^ b)⁻¹ * (1 / 4 : ℝ) ^ i := by
  have hformula := Roots.three_mul_value_add_one (2 * b + 1)
  rw [pow_add, pow_mul] at hformula
  norm_num only [pow_one, show (4 : ℕ) ^ 2 = 16 by norm_num] at hformula
  have hsize := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 16) hb
  norm_num only [pow_one] at hsize
  have hbase : 16 ^ b ≤ Roots.value (2 * b + 1) := by nlinarith
  have hroot : 4 ^ i * 16 ^ b ≤ Roots.value (2 * b + 1 + i) := by
    rw [Nat.add_comm (2 * b + 1) i, Roots.value_add]
    exact (Nat.mul_le_mul_left _ hbase).trans (Nat.le_add_left _ _)
  have hr : (4 : ℝ) ^ i * (16 : ℝ) ^ b ≤ Roots.value (2 * b + 1 + i) := by exact_mod_cast hroot
  have h := one_div_le_one_div_of_le (by positivity) hr
  simpa only [one_div, mul_inv_rev, inv_pow] using h

/-- A geometric reciprocal sum bounds the finite pool independently of its conductor. -/
theorem sum_seedRootPool_reciprocals_lt {b : ℕ} (hb : 1 ≤ b) (q : ℕ) :
    (∑ x ∈ seedRootPool b q, (x : ℝ)⁻¹) < 2 * ((16 : ℝ) ^ b)⁻¹ := by
  classical
  let full := (Finset.range (3 ^ q)).image (fun i => Roots.value (2 * b + 1 + i))
  have hsub : seedRootPool b q ⊆ full := by
    intro x hx
    obtain ⟨_, i, hi⟩ := mem_seedRootPool.mp hx
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hi⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => inv_nonneg.mpr (Nat.cast_nonneg x : (0 : ℝ) ≤ x))
  have hfull : (∑ x ∈ full, (x : ℝ)⁻¹) =
      ∑ i ∈ Finset.range (3 ^ q), (Roots.value (2 * b + 1 + i) : ℝ)⁻¹ := by
    apply Finset.sum_image
    intro i _ j _ hij
    exact Nat.add_left_cancel (Roots.value_injective hij)
  rw [hfull] at hsum
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (3 ^ q)) => root_reciprocal_bound hb i)
  rw [← Finset.mul_sum] at hbound
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)
  have hgeom := hg.sum_le_tsum (Finset.range (3 ^ q)) (fun i _ => pow_nonneg (by norm_num) i)
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)] at hgeom
  norm_num at hgeom
  have hscaled := mul_le_mul_of_nonneg_left hgeom (by positivity : (0 : ℝ) ≤ ((16 : ℝ) ^ b)⁻¹)
  have hpos : (0 : ℝ) < ((16 : ℝ) ^ b)⁻¹ := by positivity
  nlinarith

/-- The actual unchanged score satisfies the manuscript's strict binary domain. -/
theorem persistentRootScore_small :
    persistentRootScore < ((2 : ℝ) ^ (134217727 : ℕ))⁻¹ := by
  have hq := seedConductor_pos (b := survivalSeedSize) (by norm_num [survivalSeedSize])
    (seedStartupIndex survivalSeedSize (by rfl))
  have hp := (seedStartupResidual_le_fraction survivalSeedSize (by rfl)).trans (by norm_num : (24 / 25 : ℝ) ≤ 1)
  have h := (seedAllocationScore_le_reciprocals survivalSeedSize hq hp).trans_lt
    (sum_seedRootPool_reciprocals_lt (by norm_num [survivalSeedSize] : 1 ≤ survivalSeedSize) _)
  have heq : 2 * ((16 : ℝ) ^ survivalSeedSize)⁻¹ = ((2 : ℝ) ^ (134217727 : ℕ))⁻¹ := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← pow_mul]
    change 2 * ((2 : ℝ) ^ (134217727 + 1))⁻¹ = _
    rw [pow_succ, mul_inv_rev]
    have htwo : (2 : ℝ) * 2⁻¹ = 1 := by norm_num
    rw [← mul_assoc, htwo, one_mul]
  exact h.trans_eq heq

/-- Both the positive score and the order-4096 small-score guard hold. -/
theorem persistentRootScore_domain :
    0 < persistentRootScore ∧ persistentRootScore < ((2 : ℝ) ^ (4096 : ℕ))⁻¹ := by
  refine ⟨persistentRootScore_pos, persistentRootScore_small.trans ?_⟩
  have h := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (4096 : ℕ) < 134217727)
  simpa only [one_div] using one_div_lt_one_div_of_lt (by positivity) h

end WordCertDensity.Construction
