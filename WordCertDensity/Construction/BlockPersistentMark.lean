/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedRootPool
import WordCertDensity.Construction.SeedPhysical

/-! # A residue-indexed persistent mark for arbitrary predecessor blocks

The canonical pool fixes one persistent mark per physical root. An arbitrary
complete unit predecessor block meets the same residues, so the same mark can
be carried by residue instead of by root.

This supplies the one premise of `Sources.targetPoolSources` that the existing
block interface does not already discharge: a fixed weight vector below every
later physical seed mark, whose total unit-residue mass is still positive.

Nothing here assumes physical equidistribution, and no root is required to
reach one.
-/

namespace WordCertDensity.Construction

/-- The persistent mark read off a residue rather than a root. -/
noncomputable def blockPersistentMark (b : ℕ) (hb : 32 ^ 5 ≤ b) (r : ℕ) : ℝ :=
  max (seedMark b (seedStartupIndex b hb)
    (r : ZMod (3 ^ seedConductor b (seedStartupIndex b hb))) -
      (24 / 25 - seedStartupResidual b hb)) 0

/-- Residue marks are nonnegative by construction. -/
theorem blockPersistentMark_nonneg (b : ℕ) (hb : 32 ^ 5 ≤ b) (r : ℕ) :
    0 ≤ blockPersistentMark b hb r := le_max_right _ _

/-- At every physical root the residue mark is the canonical persistent mark. -/
theorem blockPersistentMark_eq_persistent {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) :
    blockPersistentMark b hb (root % 3 ^ seedConductor b (seedStartupIndex b hb)) =
      persistentSeedMark b hb root := by
  have hcast : ((root % 3 ^ seedConductor b (seedStartupIndex b hb) : ℕ) :
      ZMod (3 ^ seedConductor b (seedStartupIndex b hb))) =
      (root : ZMod (3 ^ seedConductor b (seedStartupIndex b hb))) := by
    simp
  have h : seedMark b (seedStartupIndex b hb)
      ((root % 3 ^ seedConductor b (seedStartupIndex b hb) : ℕ) :
        ZMod (3 ^ seedConductor b (seedStartupIndex b hb))) =
      physicalSeedMark b (seedStartupIndex b hb) root := by
    rw [hcast]
    exact seedMark_eq_physicalSeedMark hb hr hodd _
  unfold blockPersistentMark persistentSeedMark
  rw [h]

/-- One fixed residue mark stays below every later physical seed mark. -/
theorem blockPersistentMark_le_physical {b root j : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) (hj : seedStartupIndex b hb ≤ j) :
    blockPersistentMark b hb (root % 3 ^ seedConductor b (seedStartupIndex b hb)) ≤
      physicalSeedMark b j root := by
  rw [blockPersistentMark_eq_persistent hb hr hodd]
  exact persistentSeedMark_le_later hb hr hodd hj

/-- Every complete unit block realizes the same total residue mark. -/
theorem sum_blockPersistentMark {b : ℕ} (hb : 32 ^ 5 ≤ b) {y q start : ℕ}
    (hy : ¬ 3 ∣ y) (hq : 0 < q) :
    (∑ x ∈ Roots.unitPredecessorBlock y q start, blockPersistentMark b hb (x % 3 ^ q)) =
      ∑ r ∈ Roots.unitResidues q, blockPersistentMark b hb r :=
  Roots.sum_unitPredecessorBlock hy hq start (blockPersistentMark b hb)

/-- The actual seed's unit residues retain positive total persistent mass.
This transports the accepted canonical-pool bound, root by root. -/
theorem survival_unitResidues_mass (hb : 32 ^ 5 ≤ survivalSeedSize) :
    (2 * (3 : ℝ) ^ (seedConductor survivalSeedSize
      (seedStartupIndex survivalSeedSize hb) - 1)) *
      seedStartupResidual survivalSeedSize hb <
    ∑ r ∈ Roots.unitResidues (seedConductor survivalSeedSize
      (seedStartupIndex survivalSeedSize hb)),
      blockPersistentMark survivalSeedSize hb r := by
  classical
  have hq : 0 < seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb) :=
    seedConductor_pos (by norm_num [survivalSeedSize]) _
  have hblock := sum_blockPersistentMark (b := survivalSeedSize) hb (y := 1)
    (q := seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb))
    (start := 2 * survivalSeedSize) (by decide) hq
  have hroot : (∑ x ∈ Roots.unitPredecessorBlock 1
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb))
      (2 * survivalSeedSize),
        blockPersistentMark survivalSeedSize hb
          (x % 3 ^ seedConductor survivalSeedSize
            (seedStartupIndex survivalSeedSize hb))) =
      ∑ x ∈ seedRootPool survivalSeedSize
        (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize hb)),
        persistentSeedMark survivalSeedSize hb x := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hodd, hgt⟩ := seedRootPool_height (b := survivalSeedSize)
      (by norm_num [survivalSeedSize]) hx
    exact blockPersistentMark_eq_persistent hb hgt.le hodd
  rw [← hblock, hroot]
  exact seedRootPool_persistent_mass

end WordCertDensity.Construction
