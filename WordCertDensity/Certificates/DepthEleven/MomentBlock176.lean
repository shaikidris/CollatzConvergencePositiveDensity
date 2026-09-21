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
theorem levelEleven_energy_90112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90112 128 =
      39019923876020440479873980728780 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 128 =
      969516807661257020646860 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90112 : ∀ i : Fin 128,
    levelEleven.lookup (90112 + i.val) ≤ levelElevenRoots.lookup (90112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_90240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90240 128 =
      85736067147403548887858497470476 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90240 128 =
      1513132035427752494146805 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90240 : ∀ i : Fin 128,
    levelEleven.lookup (90240 + i.val) ≤ levelElevenRoots.lookup (90240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_90368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90368 128 =
      21223627855226637634340116567532 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90368 128 =
      729607128282310394852899 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90368 : ∀ i : Fin 128,
    levelEleven.lookup (90368 + i.val) ≤ levelElevenRoots.lookup (90368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_90496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90496 128 =
      37903493088434303208554217529253 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90496 128 =
      1086890350949312492958585 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90496 : ∀ i : Fin 128,
    levelEleven.lookup (90496 + i.val) ≤ levelElevenRoots.lookup (90496 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90112 512 =
      183883111967084930210626812296041 := by
  have h0 := levelEleven_energy_90112
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90112 256 =
      124755991023423989367732478199256 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90112 128 128
      39019923876020440479873980728780 85736067147403548887858497470476 h0 levelEleven_energy_90240
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90112 384 =
      145979618878650627002072594766788 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90112 256 128
      124755991023423989367732478199256 21223627855226637634340116567532 h1 levelEleven_energy_90368
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90112 512 =
      183883111967084930210626812296041 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90112 384 128
      145979618878650627002072594766788 37903493088434303208554217529253 h2 levelEleven_energy_90496
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 512 =
      4299146322320632402605149 := by
  have h0 := levelEleven_fractional_90112
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 256 =
      2482648843089009514793665 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 128 128
      969516807661257020646860 1513132035427752494146805 h0 levelEleven_fractional_90240
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 384 =
      3212255971371319909646564 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 256 128
      2482648843089009514793665 729607128282310394852899 h1 levelEleven_fractional_90368
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 512 =
      4299146322320632402605149 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90112 384 128
      3212255971371319909646564 1086890350949312492958585 h2 levelEleven_fractional_90496
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_176 : ∀ i : Fin 512,
    levelEleven.lookup (90112 + i.val) ≤ levelElevenRoots.lookup (90112 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_90112
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90112 128 128
    h0 levelEleven_squares_90240
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90112 256 128
    h1 levelEleven_squares_90368
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90112 384 128
    h2 levelEleven_squares_90496
  exact h3

end WordCertDensity.Certificates
