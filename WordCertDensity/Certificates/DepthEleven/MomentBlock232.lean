/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelElevenRoots

/-! # Bounded depth-eleven moment certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118784 128 =
      24472133437739490569601681024208 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 128 =
      775721577423406114008311 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118784 : ∀ i : Fin 128,
    levelEleven.lookup (118784 + i.val) ≤ levelElevenRoots.lookup (118784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118912 128 =
      118514179845206204825163233700019 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118912 128 =
      1989249270120917568811744 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118912 : ∀ i : Fin 128,
    levelEleven.lookup (118912 + i.val) ≤ levelElevenRoots.lookup (118912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119040 128 =
      27438957991765505138434701306172 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119040 128 =
      878836371114324802075924 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119040 : ∀ i : Fin 128,
    levelEleven.lookup (119040 + i.val) ≤ levelElevenRoots.lookup (119040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119168 128 =
      71709186043196310323114826162943 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119168 128 =
      1506494718391735102079084 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119168 : ∀ i : Fin 128,
    levelEleven.lookup (119168 + i.val) ≤ levelElevenRoots.lookup (119168 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118784 512 =
      242134457317907510856314442193342 := by
  have h0 := levelEleven_energy_118784
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118784 256 =
      142986313282945695394764914724227 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118784 128 128
      24472133437739490569601681024208 118514179845206204825163233700019 h0 levelEleven_energy_118912
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118784 384 =
      170425271274711200533199616030399 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118784 256 128
      142986313282945695394764914724227 27438957991765505138434701306172 h1 levelEleven_energy_119040
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118784 512 =
      242134457317907510856314442193342 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118784 384 128
      170425271274711200533199616030399 71709186043196310323114826162943 h2 levelEleven_energy_119168
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 512 =
      5150301937050383586975063 := by
  have h0 := levelEleven_fractional_118784
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 256 =
      2764970847544323682820055 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 128 128
      775721577423406114008311 1989249270120917568811744 h0 levelEleven_fractional_118912
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 384 =
      3643807218658648484895979 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 256 128
      2764970847544323682820055 878836371114324802075924 h1 levelEleven_fractional_119040
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 512 =
      5150301937050383586975063 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118784 384 128
      3643807218658648484895979 1506494718391735102079084 h2 levelEleven_fractional_119168
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_232 : ∀ i : Fin 512,
    levelEleven.lookup (118784 + i.val) ≤ levelElevenRoots.lookup (118784 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_118784
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118784 128 128
    h0 levelEleven_squares_118912
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118784 256 128
    h1 levelEleven_squares_119040
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118784 384 128
    h2 levelEleven_squares_119168
  exact h3

end WordCertDensity.Certificates
