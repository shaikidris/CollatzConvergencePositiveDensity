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
theorem levelEleven_energy_99328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99328 128 =
      26878725266851015112040134262744 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 128 =
      814510668934929862311138 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99328 : ∀ i : Fin 128,
    levelEleven.lookup (99328 + i.val) ≤ levelElevenRoots.lookup (99328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99456 128 =
      62811182083346550593258052725151 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99456 128 =
      1325767773944489620254847 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99456 : ∀ i : Fin 128,
    levelEleven.lookup (99456 + i.val) ≤ levelElevenRoots.lookup (99456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99584 128 =
      22202975894875708474794369084205 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99584 128 =
      775398183428077714149394 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99584 : ∀ i : Fin 128,
    levelEleven.lookup (99584 + i.val) ≤ levelElevenRoots.lookup (99584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99712 128 =
      34647865703400558197501221052766 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99712 128 =
      1022523651883797027561990 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99712 : ∀ i : Fin 128,
    levelEleven.lookup (99712 + i.val) ≤ levelElevenRoots.lookup (99712 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_194 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99328 512 =
      146540748948473832377593777124866 := by
  have h0 := levelEleven_energy_99328
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99328 256 =
      89689907350197565705298186987895 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99328 128 128
      26878725266851015112040134262744 62811182083346550593258052725151 h0 levelEleven_energy_99456
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99328 384 =
      111892883245073274180092556072100 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99328 256 128
      89689907350197565705298186987895 22202975894875708474794369084205 h1 levelEleven_energy_99584
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99328 512 =
      146540748948473832377593777124866 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99328 384 128
      111892883245073274180092556072100 34647865703400558197501221052766 h2 levelEleven_energy_99712
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_194 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 512 =
      3938200278191294224277369 := by
  have h0 := levelEleven_fractional_99328
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 256 =
      2140278442879419482565985 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 128 128
      814510668934929862311138 1325767773944489620254847 h0 levelEleven_fractional_99456
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 384 =
      2915676626307497196715379 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 256 128
      2140278442879419482565985 775398183428077714149394 h1 levelEleven_fractional_99584
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 512 =
      3938200278191294224277369 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99328 384 128
      2915676626307497196715379 1022523651883797027561990 h2 levelEleven_fractional_99712
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_194 : ∀ i : Fin 512,
    levelEleven.lookup (99328 + i.val) ≤ levelElevenRoots.lookup (99328 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_99328
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99328 128 128
    h0 levelEleven_squares_99456
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99328 256 128
    h1 levelEleven_squares_99584
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99328 384 128
    h2 levelEleven_squares_99712
  exact h3

end WordCertDensity.Certificates
