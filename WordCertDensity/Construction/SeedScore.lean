/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedRootPool
import WordCertDensity.Roots.Allocation

/-! # The canonical allocation score and its persistent physical witness -/

namespace WordCertDensity.Construction

/-- The final canonical root in the containing complete index interval. -/
def seedRootCeiling (b q : ℕ) : ℕ := Roots.value (2 * b + 3 ^ q)

/-- The containing root ceiling is positive. -/
theorem seedRootCeiling_pos (b q : ℕ) : 0 < seedRootCeiling b q := by
  apply Roots.value_pos
  have h : 0 < (3 : ℕ) ^ q := pow_pos (by decide) _
  omega

/-- The containing interval ceiling bounds every retained unit root. -/
theorem seedRootPool_le_ceiling {b q x : ℕ} (hx : x ∈ seedRootPool b q) :
    x ≤ seedRootCeiling b q := by
  obtain ⟨_, i, rfl⟩ := mem_seedRootPool.mp hx
  apply Roots.value_strictMono.monotone
  have h := i.isLt
  omega

/-- Literal R.score: the minimum reciprocal objective over all feasible marks. -/
noncomputable def seedAllocationScore (b q : ℕ) (p : ℝ) : ℝ :=
  Roots.allocationScore (ι := {x // x ∈ seedRootPool b q}) (fun x => (x.val : ℝ)⁻¹)
    ((2 / 3 : ℝ) * 2 ^ q) ((2 * (3 : ℝ) ^ (q - 1)) * p)

private theorem seedAllocation_capacity (b : ℕ) {q : ℕ} (hq : 0 < q) {p : ℝ} (hp : p ≤ 1) :
    (2 * (3 : ℝ) ^ (q - 1)) * p ≤
      (Fintype.card {x // x ∈ seedRootPool b q} : ℝ) * ((2 / 3 : ℝ) * 2 ^ q) := by
  rw [Fintype.card_coe, card_seedRootPool b hq]
  push_cast
  have hpow : (2 : ℝ) ≤ 2 ^ q := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.succ_le_of_lt hq)
  apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The allocation minimum is strictly positive on its full stated parameter domain. -/
theorem seedAllocationScore_pos {b q : ℕ} (hb : 1 ≤ b) (hq : 0 < q)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : 0 < seedAllocationScore b q p := by
  have hcost : ∀ x : {x // x ∈ seedRootPool b q},
      (seedRootCeiling b q : ℝ)⁻¹ ≤ (x.val : ℝ)⁻¹ := by
    intro x
    have hx : (0 : ℝ) < x.val := by
      exact_mod_cast (Nat.zero_le (16 ^ b)).trans_lt (seedRootPool_height hb x.property).2
    have hle : (x.val : ℝ) ≤ seedRootCeiling b q := by exact_mod_cast seedRootPool_le_ceiling x.property
    simpa only [one_div] using one_div_le_one_div_of_le hx hle
  have hC : (0 : ℝ) < seedRootCeiling b q := by exact_mod_cast seedRootCeiling_pos b q
  exact Roots.allocationScore_pos _ (by positivity) (seedAllocation_capacity b hq hp1)
    (inv_pos.mpr hC) hcost (mul_pos (by positivity) hp)

/-- The retained whole residual fits the allocation parameter domain. -/
theorem seedStartupResidual_le_fraction (b : ℕ) (hb : 32 ^ 5 ≤ b) :
    seedStartupResidual b hb ≤ 24 / 25 := by
  have ht := seedVariationTail_nonneg (seedStartupIndex b hb)
  have h := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ seedStartupExponent b) ht
  unfold seedStartupResidual startupResidual
  change 24 / 25 - (2 : ℝ) ^ seedStartupExponent b *
    seedVariationTail (seedStartupIndex b hb) ≤ 24 / 25
  linarith

/-- The fixed score W_* uses the actual startup conductor and whole residual. -/
noncomputable def persistentRootScore : ℝ :=
  seedAllocationScore survivalSeedSize
    (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl)))
    (seedStartupResidual survivalSeedSize (by rfl))

/-- Positivity of the actual fixed minimum-allocation score. -/
theorem persistentRootScore_pos : 0 < persistentRootScore := by
  apply seedAllocationScore_pos (by norm_num [survivalSeedSize])
    (seedConductor_pos (by norm_num [survivalSeedSize]) _)
    (seedStartup_spec survivalSeedSize (by rfl)).2.2
  exact (seedStartupResidual_le_fraction survivalSeedSize (by rfl)).trans (by norm_num)

/-- The actual persistent vector is feasible and therefore pays at least W_*.
This is the weighted inequality in R.graftinput, with one fixed pool. -/
theorem persistentRootScore_le_marks :
    persistentRootScore ≤
      ∑ x ∈ seedRootPool survivalSeedSize
        (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))),
        persistentSeedMark survivalSeedSize (by rfl) x / x := by
  classical
  let b := survivalSeedSize
  have hb : 32 ^ 5 ≤ b := by rfl
  let N := seedStartupIndex b hb
  let q := seedConductor b N
  let p := seedStartupResidual b hb
  have hq : 0 < q := seedConductor_pos (by norm_num [b, survivalSeedSize]) N
  have hp1 : p ≤ 1 := (seedStartupResidual_le_fraction b hb).trans (by norm_num)
  have hv : (fun x : {x // x ∈ seedRootPool b q} => persistentSeedMark b hb x.val) ∈
      Roots.allocationFeasible ((2 / 3 : ℝ) * 2 ^ q) ((2 * (3 : ℝ) ^ (q - 1)) * p) := by
    refine ⟨⟨fun x => persistentSeedMark_nonneg b hb x.val, ?_⟩, ?_⟩
    · intro x
      have hx := seedRootPool_height (by norm_num [b, survivalSeedSize] : 1 ≤ b) x.property
      exact persistentSeedMark_cap hb hx.2.le hx.1
    · change (2 * (3 : ℝ) ^ (q - 1)) * p ≤
        ∑ x : {x // x ∈ seedRootPool b q}, persistentSeedMark b hb x.val
      rw [Finset.sum_coe_sort]
      exact seedRootPool_persistent_mass.le
  have h := Roots.allocationScore_le (fun x : {x // x ∈ seedRootPool b q} => (x.val : ℝ)⁻¹)
    (by positivity) (seedAllocation_capacity b hq hp1) hv
  unfold Roots.allocationObjective at h
  rw [Finset.sum_coe_sort (seedRootPool b q)
    (fun x : ℕ => (x : ℝ)⁻¹ * persistentSeedMark b hb x)] at h
  simpa only [persistentRootScore, seedAllocationScore, div_eq_mul_inv, mul_comm] using h

end WordCertDensity.Construction
