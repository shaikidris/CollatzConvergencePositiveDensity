/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Periods
public import WordCertDensity.Roots.Antichain
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Complete unit predecessor blocks

Adjacent complete periods give disjoint finite candidate pools. Each realizes
the same unit residues and weighted sums. The unique possible periodic
predecessor cannot occur in both blocks, so one entire block is nonrecurrent.
-/

@[expose] public section

namespace WordCertDensity.Roots

/-- The unit residues represented in the natural interval below the modulus. -/
def unitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range (3 ^ q)).filter fun r => ¬ 3 ∣ r

/-- Unit predecessors in one complete consecutive index block. -/
def unitPredecessorBlock (y q start : ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (3 ^ q))).image
    (fun i => inverseRoot y (start + i.val))).filter fun x => ¬ 3 ∣ x

/-- Membership retains the exact constructor index and the unit filter. -/
theorem mem_unitPredecessorBlock {y q start x : ℕ} :
    x ∈ unitPredecessorBlock y q start ↔
      ¬ 3 ∣ x ∧ ∃ i : Fin (3 ^ q), inverseRoot y (start + i.val) = x := by
  simp [unitPredecessorBlock, and_comm]

/-- Every retained root is positive and odd for a unit target. -/
theorem unitPredecessorBlock_physical {y q start x : ℕ} (hy : ¬ 3 ∣ y)
    (hx : x ∈ unitPredecessorBlock y q start) : 0 < x ∧ Odd x := by
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  exact ⟨inverseRoot_pos hy _, inverseRoot_odd hy _⟩

/-- At an odd unit target every retained root has exactly that accelerated endpoint. -/
theorem unitPredecessorBlock_fiber {y q start x : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y)
    (hx : x ∈ unitPredecessorBlock y q start) : acceleratedStep x = y := by
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  exact inverseRoot_acceleratedStep hy hodd _

/-- Reduction at positive level preserves the literal unit condition. -/
theorem unit_mod_iff {q : ℕ} (hq : 0 < q) (x : ℕ) :
    ¬ 3 ∣ x % 3 ^ q ↔ ¬ 3 ∣ x := by
  have hd : 3 ∣ 3 ^ q := by
    simpa using Nat.pow_dvd_pow 3 (Nat.succ_le_of_lt hq)
  exact not_congr (Nat.dvd_mod_iff hd)

/-- The actual residues of a filtered block are unit representatives. -/
theorem unitPredecessorBlock_residue_mem {y q start x : ℕ} (hq : 0 < q)
    (hx : x ∈ unitPredecessorBlock y q start) : x % 3 ^ q ∈ unitResidues q := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos (by decide) _)),
    (unit_mod_iff hq x).mpr (mem_unitPredecessorBlock.mp hx).1⟩

/-- Residue reduction is injective within a complete predecessor block. -/
theorem unitPredecessorBlock_residue_inj {y q start : ℕ} (hy : ¬ 3 ∣ y) :
    Set.InjOn (fun x => x % 3 ^ q) (↑(unitPredecessorBlock y q start) : Set ℕ) := by
  intro x hx z hz heq
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  obtain ⟨_, j, rfl⟩ := mem_unitPredecessorBlock.mp hz
  have hij := inverseResidue_injective hy q start (Fin.ext heq)
  exact congrArg (fun k : Fin (3 ^ q) => inverseRoot y (start + k.val)) hij

/-- Every unit residue occurs in a filtered predecessor block. -/
theorem unitPredecessorBlock_residue_surj {y q start r : ℕ}
    (hy : ¬ 3 ∣ y) (hq : 0 < q) (hr : r ∈ unitResidues q) :
    ∃ x ∈ unitPredecessorBlock y q start, x % 3 ^ q = r := by
  obtain ⟨hrlt, hrunit⟩ := Finset.mem_filter.mp hr
  obtain ⟨i, hi⟩ := (inverseResidue_bijective hy q start).2
    ⟨r, Finset.mem_range.mp hrlt⟩
  have heq : inverseRoot y (start + i.val) % 3 ^ q = r := congrArg Fin.val hi
  refine ⟨inverseRoot y (start + i.val), mem_unitPredecessorBlock.mpr ⟨?_, i, rfl⟩, heq⟩
  exact (unit_mod_iff hq _).mp (heq.symm ▸ hrunit)

/-- There are exactly two unit classes per ternary triple at positive level. -/
theorem card_unitResidues {q : ℕ} (hq : 0 < q) :
    (unitResidues q).card = 2 * 3 ^ (q - 1) := by
  have hset : unitResidues q =
      (Finset.range (3 ^ q)).filter (fun r => Nat.Coprime (3 ^ q) r) := by
    ext r
    simp [unitResidues, Nat.coprime_pow_left_iff hq, Nat.prime_three.coprime_iff_not_dvd]
  rw [hset, ← Nat.totient_eq_card_coprime, Nat.totient_prime_pow Nat.prime_three hq]
  omega

/-- A complete filtered predecessor block has the exact unit-class count. -/
theorem card_unitPredecessorBlock {y q : ℕ} (hy : ¬ 3 ∣ y) (hq : 0 < q) (start : ℕ) :
    (unitPredecessorBlock y q start).card = 2 * 3 ^ (q - 1) := by
  rw [← card_unitResidues hq]
  apply Finset.card_bij (fun x _ => x % 3 ^ q)
  · exact fun x hx => unitPredecessorBlock_residue_mem hq hx
  · exact fun x hx z hz h => unitPredecessorBlock_residue_inj hy hx hz h
  · intro r hr
    obtain ⟨x, hx, heq⟩ := unitPredecessorBlock_residue_surj (start := start) hy hq hr
    exact ⟨x, hx, heq⟩

/-- At positive level each filtered block is nonempty. -/
theorem unitPredecessorBlock_nonempty {y q : ℕ} (hy : ¬ 3 ∣ y) (hq : 0 < q)
    (start : ℕ) : (unitPredecessorBlock y q start).Nonempty := by
  rw [← Finset.card_pos, card_unitPredecessorBlock hy hq]
  positivity

/-- Each full block realizes the same sum of arbitrary real unit-residue weights. -/
theorem sum_unitPredecessorBlock {y q : ℕ} (hy : ¬ 3 ∣ y) (hq : 0 < q)
    (start : ℕ) (z : ℕ → ℝ) :
    (∑ x ∈ unitPredecessorBlock y q start, z (x % 3 ^ q)) = ∑ r ∈ unitResidues q, z r := by
  apply Finset.sum_bij (fun x _ => x % 3 ^ q)
  · exact fun x hx => unitPredecessorBlock_residue_mem hq hx
  · exact fun x hx w hw h => unitPredecessorBlock_residue_inj hy hx hw h
  · intro r hr
    obtain ⟨x, hx, heq⟩ := unitPredecessorBlock_residue_surj (start := start) hy hq hr
    exact ⟨x, hx, heq⟩
  · intros
    rfl

/-- Adjacent constructor blocks have no common root. -/
theorem unitPredecessorBlock_disjoint {y : ℕ} (hy : ¬ 3 ∣ y) (q start : ℕ) :
    Disjoint (unitPredecessorBlock y q start) (unitPredecessorBlock y q (start + 3 ^ q)) := by
  rw [Finset.disjoint_left]
  intro x hx hz
  obtain ⟨_, i, hi⟩ := mem_unitPredecessorBlock.mp hx
  obtain ⟨_, j, hj⟩ := mem_unitPredecessorBlock.mp hz
  have heq := inverseRoot_injective hy (hi.trans hj.symm)
  have hilt := i.isLt
  omega

/-- An odd unit target has a whole nonrecurrent block among two adjacent candidates. -/
theorem exists_nonrecurrent_unitPredecessorBlock {y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y)
    (q start : ℕ) :
    NonrecurrentPool acceleratedStep (↑(unitPredecessorBlock y q start) : Set ℕ) ∨
      NonrecurrentPool acceleratedStep (↑(unitPredecessorBlock y q (start + 3 ^ q)) : Set ℕ) := by
  have good (a : ℕ) (ha : ∀ x ∈ unitPredecessorBlock y q a,
      x ∉ Function.periodicPts acceleratedStep) :
      NonrecurrentPool acceleratedStep (↑(unitPredecessorBlock y q a) : Set ℕ) := by
    apply (nonrecurrentPool_nonperiodic_fiber acceleratedStep y).mono
    intro x hx
    exact ⟨unitPredecessorBlock_fiber hy hodd hx, ha x hx⟩
  by_cases hfirst : ∀ x ∈ unitPredecessorBlock y q start,
      x ∉ Function.periodicPts acceleratedStep
  · exact Or.inl (good start hfirst)
  · push Not at hfirst
    obtain ⟨x, hx, hp⟩ := hfirst
    refine Or.inr (good (start + 3 ^ q) ?_)
    intro z hz hzp
    have heq : x = z := periodic_fiber_subsingleton acceleratedStep y
      ⟨unitPredecessorBlock_fiber hy hodd hx, hp⟩
      ⟨unitPredecessorBlock_fiber hy hodd hz, hzp⟩
    exact Finset.disjoint_left.mp (unitPredecessorBlock_disjoint hy q start) hx (heq ▸ hz)

end WordCertDensity.Roots
