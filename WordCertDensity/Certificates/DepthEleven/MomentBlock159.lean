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
theorem levelEleven_energy_81408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81408 128 =
      30346179868158050164010038037797 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 128 =
      899062285735308090697473 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81408 : ∀ i : Fin 128,
    levelEleven.lookup (81408 + i.val) ≤ levelElevenRoots.lookup (81408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81536 128 =
      63183603577914993902362964306163 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81536 128 =
      1384585608311985739660195 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81536 : ∀ i : Fin 128,
    levelEleven.lookup (81536 + i.val) ≤ levelElevenRoots.lookup (81536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81664 128 =
      24434872809889430982706456186302 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81664 128 =
      762710343164449862505276 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81664 : ∀ i : Fin 128,
    levelEleven.lookup (81664 + i.val) ≤ levelElevenRoots.lookup (81664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81792 128 =
      120439070908970236251318868404720 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81792 128 =
      2075469900732847366578099 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81792 : ∀ i : Fin 128,
    levelEleven.lookup (81792 + i.val) ≤ levelElevenRoots.lookup (81792 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_159 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81408 512 =
      238403727164932711300398326934982 := by
  have h0 := levelEleven_energy_81408
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81408 256 =
      93529783446073044066373002343960 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81408 128 128
      30346179868158050164010038037797 63183603577914993902362964306163 h0 levelEleven_energy_81536
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81408 384 =
      117964656255962475049079458530262 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81408 256 128
      93529783446073044066373002343960 24434872809889430982706456186302 h1 levelEleven_energy_81664
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81408 512 =
      238403727164932711300398326934982 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81408 384 128
      117964656255962475049079458530262 120439070908970236251318868404720 h2 levelEleven_energy_81792
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_159 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 512 =
      5121828137944591059441043 := by
  have h0 := levelEleven_fractional_81408
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 256 =
      2283647894047293830357668 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 128 128
      899062285735308090697473 1384585608311985739660195 h0 levelEleven_fractional_81536
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 384 =
      3046358237211743692862944 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 256 128
      2283647894047293830357668 762710343164449862505276 h1 levelEleven_fractional_81664
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 512 =
      5121828137944591059441043 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81408 384 128
      3046358237211743692862944 2075469900732847366578099 h2 levelEleven_fractional_81792
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_159 : ∀ i : Fin 512,
    levelEleven.lookup (81408 + i.val) ≤ levelElevenRoots.lookup (81408 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_81408
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81408 128 128
    h0 levelEleven_squares_81536
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81408 256 128
    h1 levelEleven_squares_81664
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81408 384 128
    h2 levelEleven_squares_81792
  exact h3

end WordCertDensity.Certificates
