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
theorem levelEleven_energy_49152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49152 128 =
      61808178061457243376292886849592 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 128 =
      1394956318389618800878635 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49152 : ∀ i : Fin 128,
    levelEleven.lookup (49152 + i.val) ≤ levelElevenRoots.lookup (49152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49280 128 =
      15103181690707195517913019611251 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49280 128 =
      613460911398827463292492 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49280 : ∀ i : Fin 128,
    levelEleven.lookup (49280 + i.val) ≤ levelElevenRoots.lookup (49280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49408 128 =
      230821665033473697456699016133946 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49408 128 =
      2652230398934489302305210 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49408 : ∀ i : Fin 128,
    levelEleven.lookup (49408 + i.val) ≤ levelElevenRoots.lookup (49408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49536 128 =
      91796866285584970207264583109237 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49536 128 =
      1436820887625043654594974 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49536 : ∀ i : Fin 128,
    levelEleven.lookup (49536 + i.val) ≤ levelElevenRoots.lookup (49536 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_96 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49152 512 =
      399529891071223106558169505704026 := by
  have h0 := levelEleven_energy_49152
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49152 256 =
      76911359752164438894205906460843 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49152 128 128
      61808178061457243376292886849592 15103181690707195517913019611251 h0 levelEleven_energy_49280
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49152 384 =
      307733024785638136350904922594789 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49152 256 128
      76911359752164438894205906460843 230821665033473697456699016133946 h1 levelEleven_energy_49408
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49152 512 =
      399529891071223106558169505704026 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49152 384 128
      307733024785638136350904922594789 91796866285584970207264583109237 h2 levelEleven_energy_49536
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_96 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 512 =
      6097468516347979221071311 := by
  have h0 := levelEleven_fractional_49152
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 256 =
      2008417229788446264171127 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 128 128
      1394956318389618800878635 613460911398827463292492 h0 levelEleven_fractional_49280
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 384 =
      4660647628722935566476337 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 256 128
      2008417229788446264171127 2652230398934489302305210 h1 levelEleven_fractional_49408
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 512 =
      6097468516347979221071311 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49152 384 128
      4660647628722935566476337 1436820887625043654594974 h2 levelEleven_fractional_49536
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_96 : ∀ i : Fin 512,
    levelEleven.lookup (49152 + i.val) ≤ levelElevenRoots.lookup (49152 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_49152
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49152 128 128
    h0 levelEleven_squares_49280
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49152 256 128
    h1 levelEleven_squares_49408
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49152 384 128
    h2 levelEleven_squares_49536
  exact h3

end WordCertDensity.Certificates
