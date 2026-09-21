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
theorem levelEleven_energy_145408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145408 128 =
      96819969788935461589306050297501 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 128 =
      1727302864075431772623628 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145408 : ∀ i : Fin 128,
    levelEleven.lookup (145408 + i.val) ≤ levelElevenRoots.lookup (145408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145536 128 =
      23752136701648330927811104724229 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145536 128 =
      793969887209981207495110 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145536 : ∀ i : Fin 128,
    levelEleven.lookup (145536 + i.val) ≤ levelElevenRoots.lookup (145536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145664 128 =
      105548204766574647316178537051679 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145664 128 =
      1750699086291457242928022 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145664 : ∀ i : Fin 128,
    levelEleven.lookup (145664 + i.val) ≤ levelElevenRoots.lookup (145664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145792 128 =
      32463470757780373375188121219916 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145792 128 =
      887329233005189232422864 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145792 : ∀ i : Fin 128,
    levelEleven.lookup (145792 + i.val) ≤ levelElevenRoots.lookup (145792 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_284 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145408 512 =
      258583782014938813208483813293325 := by
  have h0 := levelEleven_energy_145408
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145408 256 =
      120572106490583792517117155021730 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145408 128 128
      96819969788935461589306050297501 23752136701648330927811104724229 h0 levelEleven_energy_145536
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145408 384 =
      226120311257158439833295692073409 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145408 256 128
      120572106490583792517117155021730 105548204766574647316178537051679 h1 levelEleven_energy_145664
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145408 512 =
      258583782014938813208483813293325 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145408 384 128
      226120311257158439833295692073409 32463470757780373375188121219916 h2 levelEleven_energy_145792
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_284 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 512 =
      5159301070582059455469624 := by
  have h0 := levelEleven_fractional_145408
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 256 =
      2521272751285412980118738 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 128 128
      1727302864075431772623628 793969887209981207495110 h0 levelEleven_fractional_145536
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 384 =
      4271971837576870223046760 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 256 128
      2521272751285412980118738 1750699086291457242928022 h1 levelEleven_fractional_145664
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 512 =
      5159301070582059455469624 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145408 384 128
      4271971837576870223046760 887329233005189232422864 h2 levelEleven_fractional_145792
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_284 : ∀ i : Fin 512,
    levelEleven.lookup (145408 + i.val) ≤ levelElevenRoots.lookup (145408 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_145408
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145408 128 128
    h0 levelEleven_squares_145536
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145408 256 128
    h1 levelEleven_squares_145664
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145408 384 128
    h2 levelEleven_squares_145792
  exact h3

end WordCertDensity.Certificates
