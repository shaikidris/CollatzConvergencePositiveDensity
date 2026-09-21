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
theorem levelEleven_energy_56320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56320 128 =
      29010913158252417381905159916088 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 128 =
      905379965217789376597766 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56320 : ∀ i : Fin 128,
    levelEleven.lookup (56320 + i.val) ≤ levelElevenRoots.lookup (56320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56448 128 =
      38512211458292772116125166969678 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56448 128 =
      1057282075798829501322161 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56448 : ∀ i : Fin 128,
    levelEleven.lookup (56448 + i.val) ≤ levelElevenRoots.lookup (56448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56576 128 =
      45873312010864150435466174202328 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56576 128 =
      1113068808122191851084674 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56576 : ∀ i : Fin 128,
    levelEleven.lookup (56576 + i.val) ≤ levelElevenRoots.lookup (56576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56704 128 =
      108261397891714096555785068357518 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56704 128 =
      1986718231604302083001041 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56704 : ∀ i : Fin 128,
    levelEleven.lookup (56704 + i.val) ≤ levelElevenRoots.lookup (56704 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_110 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56320 512 =
      221657834519123436489281569445612 := by
  have h0 := levelEleven_energy_56320
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56320 256 =
      67523124616545189498030326885766 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56320 128 128
      29010913158252417381905159916088 38512211458292772116125166969678 h0 levelEleven_energy_56448
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56320 384 =
      113396436627409339933496501088094 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56320 256 128
      67523124616545189498030326885766 45873312010864150435466174202328 h1 levelEleven_energy_56576
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56320 512 =
      221657834519123436489281569445612 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56320 384 128
      113396436627409339933496501088094 108261397891714096555785068357518 h2 levelEleven_energy_56704
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_110 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 512 =
      5062449080743112812005642 := by
  have h0 := levelEleven_fractional_56320
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 256 =
      1962662041016618877919927 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 128 128
      905379965217789376597766 1057282075798829501322161 h0 levelEleven_fractional_56448
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 384 =
      3075730849138810729004601 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 256 128
      1962662041016618877919927 1113068808122191851084674 h1 levelEleven_fractional_56576
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 512 =
      5062449080743112812005642 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56320 384 128
      3075730849138810729004601 1986718231604302083001041 h2 levelEleven_fractional_56704
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_110 : ∀ i : Fin 512,
    levelEleven.lookup (56320 + i.val) ≤ levelElevenRoots.lookup (56320 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_56320
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56320 128 128
    h0 levelEleven_squares_56448
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56320 256 128
    h1 levelEleven_squares_56576
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56320 384 128
    h2 levelEleven_squares_56704
  exact h3

end WordCertDensity.Certificates
