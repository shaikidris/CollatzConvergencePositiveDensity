/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedStartup
import WordCertDensity.Construction.SurvivalProduct
import WordCertDensity.Roots.PredecessorBlocks

/-! # The canonical finite root pool and its actual seed mean -/

namespace WordCertDensity.Construction

private theorem inverseRoot_one (t : ℕ) : Roots.inverseRoot 1 t = Roots.value (t + 1) := by
  rw [Roots.inverseRoot, Roots.inverseExponent, Roots.inverseParity, Roots.value_eq_quotient]
  norm_num only [Nat.one_mod, if_pos, mul_one]
  congr 2
  rw [show 2 * t + 2 = 2 * (t + 1) by omega, pow_mul]
  norm_num

/-- The canonical roots R_s for H≤s<H+3^q, restricted to units;
the predecessor constructor has index s-1. -/
def seedRootPool (b q : ℕ) : Finset ℕ := Roots.unitPredecessorBlock 1 q (2 * b)

/-- Every pool member retains an index in the exact canonical interval. -/
theorem mem_seedRootPool {b q x : ℕ} :
    x ∈ seedRootPool b q ↔ ¬ 3 ∣ x ∧
      ∃ i : Fin (3 ^ q), Roots.value (2 * b + 1 + i.val) = x := by
  rw [seedRootPool, Roots.mem_unitPredecessorBlock]
  simp only [inverseRoot_one, Nat.add_right_comm (2 * b)]

/-- Exactly one root is present for each unit residue. -/
theorem card_seedRootPool (b : ℕ) {q : ℕ} (hq : 0 < q) :
    (seedRootPool b q).card = 2 * 3 ^ (q - 1) :=
  Roots.card_unitPredecessorBlock (by decide : ¬ 3 ∣ 1) hq _

/-- Every member is odd and exceeds the physical seed height guard. -/
theorem seedRootPool_height {b q x : ℕ} (hb : 1 ≤ b) (hx : x ∈ seedRootPool b q) :
    Odd x ∧ 16 ^ b < x := by
  obtain ⟨_, i, rfl⟩ := mem_seedRootPool.mp hx
  have hmono := Roots.value_strictMono.monotone (show 2 * b + 1 ≤ 2 * b + 1 + i.val by omega)
  have hformula := Roots.three_mul_value_add_one (2 * b + 1)
  rw [pow_add, pow_mul] at hformula
  norm_num only [pow_one, show (4 : ℕ) ^ 2 = 16 by norm_num] at hformula
  have hsize := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 16) hb
  norm_num only [pow_one] at hsize
  refine ⟨Roots.value_odd (by omega), ?_⟩
  nlinarith

/-- Each root has its retained ordinary path to one. -/
theorem seedRootPool_reaches_one {b q x : ℕ} (hb : 1 ≤ b) (hx : x ∈ seedRootPool b q) :
    ∃ i : Fin (3 ^ q), Roots.value (2 * b + 1 + i.val) = x ∧
      ReachesIn x 1 (2 * (2 * b + 1 + i.val) + 1) := by
  obtain ⟨_, i, rfl⟩ := mem_seedRootPool.mp hx
  exact ⟨i, rfl, Roots.reachesIn_one (by omega)⟩

private theorem sum_unitResidues_zmod {q : ℕ} (hq : 0 < q) (f : ZMod (3 ^ q) → ℝ) :
    (∑ r ∈ Roots.unitResidues q, f r) =
      ∑ z ∈ Finset.univ.filter (fun z : ZMod (3 ^ q) => IsUnit z), f z := by
  classical
  apply Finset.sum_bij (fun (r : ℕ) _ => (r : ZMod (3 ^ q)))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_three hq).mpr
        (Finset.mem_filter.mp hr).2⟩
  · intro r hr s hs heq
    have h := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hr).1),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)] at h
    exact h
  · intro z hz
    refine ⟨z.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt z), ?_⟩,
      ZMod.natCast_zmod_val z⟩
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_three hq).mp
    simpa only [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hz).2
  · intros
    rfl

/-- Exact complete-period summation for arbitrary real unit-residue marks. -/
theorem sum_seedRootPool (b : ℕ) {q : ℕ} (hq : 0 < q) (f : ZMod (3 ^ q) → ℝ) :
    (∑ x ∈ seedRootPool b q, f x) =
      ∑ z ∈ Finset.univ.filter (fun z : ZMod (3 ^ q) => IsUnit z), f z := by
  have h := Roots.sum_unitPredecessorBlock (by decide : ¬ 3 ∣ 1) hq (2 * b)
    (fun r => f (r : ZMod (3 ^ q)))
  have hcast (x : ℕ) : ((x % 3 ^ q : ℕ) : ZMod (3 ^ q)) = x := by simp
  simp only [hcast] at h
  exact h.trans (sum_unitResidues_zmod hq f)

/-- The original reference survival mean is the exact physical mean on the
canonical finite pool; the unit restriction cancels the factor two thirds. -/
theorem seedRootPool_physical_mean {b : ℕ} (hb : 32 ^ 5 ≤ b) (n : ℕ) :
    (∑ x ∈ seedRootPool b (seedConductor b n), physicalSeedMark b n x) =
      (2 * (3 : ℝ) ^ (seedConductor b n - 1)) *
        ∏ j ∈ Finset.range n, Reference.stoppingMass (seedWords (seedSize b j)) := by
  classical
  have hq := seedConductor_pos (b := b) (by omega) n
  have heq : (∑ x ∈ seedRootPool b (seedConductor b n), physicalSeedMark b n x) =
      ∑ x ∈ seedRootPool b (seedConductor b n), seedMark b n (x : ZMod (3 ^ seedConductor b n)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hh := seedRootPool_height (by omega : 1 ≤ b) hx
    exact (seedMark_eq_physicalSeedMark hb hh.2.le hh.1 n).symm
  rw [heq, sum_seedRootPool b hq]
  have hm := unitMean_seedMark (b := b) (by omega) n
  apply (div_eq_iff (by positivity : (2 * (3 : ℝ) ^ (seedConductor b n - 1)) ≠ 0)).mp at hm
  simpa only [mul_comm] using hm

/-- The canonical pool has total physical seed mass strictly above its
unit count times the retained survival fraction. -/
theorem seedRootPool_survival_mean (n : ℕ) :
    (2 * (3 : ℝ) ^ (seedConductor survivalSeedSize n - 1)) * (24 / 25) <
      ∑ x ∈ seedRootPool survivalSeedSize (seedConductor survivalSeedSize n),
        physicalSeedMark survivalSeedSize n x := by
  rw [seedRootPool_physical_mean (by rfl)]
  have h := survivalFraction_lt_partialProduct n
  exact mul_lt_mul_of_pos_left h (by positivity)

/-- The fixed lower mark after paying the entire future variation budget. -/
noncomputable def persistentSeedMark (b : ℕ) (hb : 32 ^ 5 ≤ b) (root : ℕ) : ℝ :=
  max (physicalSeedMark b (seedStartupIndex b hb) root -
    (24 / 25 - seedStartupResidual b hb)) 0

/-- Persistent marks are nonnegative by construction. -/
theorem persistentSeedMark_nonneg (b : ℕ) (hb : 32 ^ 5 ≤ b) (root : ℕ) :
    0 ≤ persistentSeedMark b hb root := le_max_right _ _

/-- One fixed lower mark works at every later physical generation. -/
theorem persistentSeedMark_le_later {b root j : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) (hj : seedStartupIndex b hb ≤ j) :
    persistentSeedMark b hb root ≤ physicalSeedMark b j root := by
  have h := physicalSeedMark_startup_tail hb hr hj
  have hn := (physicalSeedMark_cap hb hr hodd j).1
  unfold persistentSeedMark
  exact max_le (by linarith [(abs_le.mp h).1]) hn

/-- Persistent marks retain the original startup conductor cap. -/
theorem persistentSeedMark_cap {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) :
    persistentSeedMark b hb root ≤
      (2 / 3 : ℝ) * 2 ^ seedConductor b (seedStartupIndex b hb) :=
  (persistentSeedMark_le_later hb hr hodd le_rfl).trans
    (physicalSeedMark_cap hb hr hodd _).2

/-- The canonical pool retains positive total mass after paying the full
future tail. This does not assert survival at every root. -/
theorem seedRootPool_persistent_mass :
    (2 * (3 : ℝ) ^ (seedConductor survivalSeedSize
      (seedStartupIndex survivalSeedSize (by rfl)) - 1)) *
      seedStartupResidual survivalSeedSize (by rfl) <
    ∑ x ∈ seedRootPool survivalSeedSize
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))),
      persistentSeedMark survivalSeedSize (by rfl) x := by
  classical
  let b := survivalSeedSize
  have hb : 32 ^ 5 ≤ b := by rfl
  let N := seedStartupIndex b hb
  let q := seedConductor b N
  have hq : 0 < q := seedConductor_pos (by norm_num [b, survivalSeedSize]) N
  have hm := seedRootPool_survival_mean N
  have hs : (∑ x ∈ seedRootPool b q, (physicalSeedMark b N x -
      (24 / 25 - seedStartupResidual b hb))) ≤
      ∑ x ∈ seedRootPool b q, persistentSeedMark b hb x := by
    apply Finset.sum_le_sum
    intro x _
    exact le_max_left _ _
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_seedRootPool b hq] at hs
  push_cast at hs
  change (2 * (3 : ℝ) ^ (q - 1)) * seedStartupResidual b hb < _
  change (2 * (3 : ℝ) ^ (q - 1)) * (24 / 25) <
    ∑ x ∈ seedRootPool b q, physicalSeedMark b N x at hm
  nlinarith

end WordCertDensity.Construction
