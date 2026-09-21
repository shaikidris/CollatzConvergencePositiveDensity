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
theorem levelEleven_energy_72192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72192 128 =
      21746690003890491377401463958574 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 128 =
      704161792976783394963395 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72192 : ∀ i : Fin 128,
    levelEleven.lookup (72192 + i.val) ≤ levelElevenRoots.lookup (72192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72320 128 =
      54881981085702459784971371079569 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72320 128 =
      1365927849055936163217552 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72320 : ∀ i : Fin 128,
    levelEleven.lookup (72320 + i.val) ≤ levelElevenRoots.lookup (72320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72448 128 =
      45047614202252953678930771230776 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72448 128 =
      1151699701622582869551036 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72448 : ∀ i : Fin 128,
    levelEleven.lookup (72448 + i.val) ≤ levelElevenRoots.lookup (72448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72576 128 =
      43803132286035640135800374910638 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72576 128 =
      1128325795798820819131038 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72576 : ∀ i : Fin 128,
    levelEleven.lookup (72576 + i.val) ≤ levelElevenRoots.lookup (72576 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_141 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72192 512 =
      165479417577881544977103981179557 := by
  have h0 := levelEleven_energy_72192
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72192 256 =
      76628671089592951162372835038143 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72192 128 128
      21746690003890491377401463958574 54881981085702459784971371079569 h0 levelEleven_energy_72320
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72192 384 =
      121676285291845904841303606268919 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72192 256 128
      76628671089592951162372835038143 45047614202252953678930771230776 h1 levelEleven_energy_72448
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72192 512 =
      165479417577881544977103981179557 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72192 384 128
      121676285291845904841303606268919 43803132286035640135800374910638 h2 levelEleven_energy_72576
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_141 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 512 =
      4350115139454123246863021 := by
  have h0 := levelEleven_fractional_72192
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 256 =
      2070089642032719558180947 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 128 128
      704161792976783394963395 1365927849055936163217552 h0 levelEleven_fractional_72320
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 384 =
      3221789343655302427731983 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 256 128
      2070089642032719558180947 1151699701622582869551036 h1 levelEleven_fractional_72448
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 512 =
      4350115139454123246863021 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72192 384 128
      3221789343655302427731983 1128325795798820819131038 h2 levelEleven_fractional_72576
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_141 : ∀ i : Fin 512,
    levelEleven.lookup (72192 + i.val) ≤ levelElevenRoots.lookup (72192 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_72192
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72192 128 128
    h0 levelEleven_squares_72320
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72192 256 128
    h1 levelEleven_squares_72448
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72192 384 128
    h2 levelEleven_squares_72576
  exact h3

end WordCertDensity.Certificates
