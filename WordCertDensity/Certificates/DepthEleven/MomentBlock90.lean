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
theorem levelEleven_energy_46080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46080 128 =
      151476382319209557330843585209390 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 128 =
      2314066994678187254314111 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46080 : ∀ i : Fin 128,
    levelEleven.lookup (46080 + i.val) ≤ levelElevenRoots.lookup (46080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46208 128 =
      28228215102718962980815473185975 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46208 128 =
      882655452490743479057262 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46208 : ∀ i : Fin 128,
    levelEleven.lookup (46208 + i.val) ≤ levelElevenRoots.lookup (46208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46336 128 =
      31272079763975383831004555056038 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46336 128 =
      979930279756372271208388 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46336 : ∀ i : Fin 128,
    levelEleven.lookup (46336 + i.val) ≤ levelElevenRoots.lookup (46336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46464 128 =
      51670552148866055353079446242633 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46464 128 =
      1161451613809981568915474 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46464 : ∀ i : Fin 128,
    levelEleven.lookup (46464 + i.val) ≤ levelElevenRoots.lookup (46464 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_90 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46080 512 =
      262647229334769959495743059694036 := by
  have h0 := levelEleven_energy_46080
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46080 256 =
      179704597421928520311659058395365 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46080 128 128
      151476382319209557330843585209390 28228215102718962980815473185975 h0 levelEleven_energy_46208
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46080 384 =
      210976677185903904142663613451403 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46080 256 128
      179704597421928520311659058395365 31272079763975383831004555056038 h1 levelEleven_energy_46336
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46080 512 =
      262647229334769959495743059694036 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46080 384 128
      210976677185903904142663613451403 51670552148866055353079446242633 h2 levelEleven_energy_46464
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_90 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 512 =
      5338104340735284573495235 := by
  have h0 := levelEleven_fractional_46080
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 256 =
      3196722447168930733371373 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 128 128
      2314066994678187254314111 882655452490743479057262 h0 levelEleven_fractional_46208
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 384 =
      4176652726925303004579761 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 256 128
      3196722447168930733371373 979930279756372271208388 h1 levelEleven_fractional_46336
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 512 =
      5338104340735284573495235 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46080 384 128
      4176652726925303004579761 1161451613809981568915474 h2 levelEleven_fractional_46464
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_90 : ∀ i : Fin 512,
    levelEleven.lookup (46080 + i.val) ≤ levelElevenRoots.lookup (46080 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_46080
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46080 128 128
    h0 levelEleven_squares_46208
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46080 256 128
    h1 levelEleven_squares_46336
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46080 384 128
    h2 levelEleven_squares_46464
  exact h3

end WordCertDensity.Certificates
