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
theorem levelEleven_energy_7168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7168 128 =
      98086194383461516955840934025248 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 128 =
      1709731260061796831802112 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7168 : ∀ i : Fin 128,
    levelEleven.lookup (7168 + i.val) ≤ levelElevenRoots.lookup (7168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7296 128 =
      70942382148934625257373382919782 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7296 128 =
      1163669700873386216398605 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7296 : ∀ i : Fin 128,
    levelEleven.lookup (7296 + i.val) ≤ levelElevenRoots.lookup (7296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7424 128 =
      41387924809286020060544074357373 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7424 128 =
      1061902869462940672817075 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7424 : ∀ i : Fin 128,
    levelEleven.lookup (7424 + i.val) ≤ levelElevenRoots.lookup (7424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7552 128 =
      41804269119441221117945371769585 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7552 128 =
      1079548084048534498306517 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7552 : ∀ i : Fin 128,
    levelEleven.lookup (7552 + i.val) ≤ levelElevenRoots.lookup (7552 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_14 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7168 512 =
      252220770461123383391703763071988 := by
  have h0 := levelEleven_energy_7168
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7168 256 =
      169028576532396142213214316945030 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7168 128 128
      98086194383461516955840934025248 70942382148934625257373382919782 h0 levelEleven_energy_7296
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7168 384 =
      210416501341682162273758391302403 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7168 256 128
      169028576532396142213214316945030 41387924809286020060544074357373 h1 levelEleven_energy_7424
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7168 512 =
      252220770461123383391703763071988 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7168 384 128
      210416501341682162273758391302403 41804269119441221117945371769585 h2 levelEleven_energy_7552
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_14 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 512 =
      5014851914446658219324309 := by
  have h0 := levelEleven_fractional_7168
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 256 =
      2873400960935183048200717 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 128 128
      1709731260061796831802112 1163669700873386216398605 h0 levelEleven_fractional_7296
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 384 =
      3935303830398123721017792 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 256 128
      2873400960935183048200717 1061902869462940672817075 h1 levelEleven_fractional_7424
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 512 =
      5014851914446658219324309 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7168 384 128
      3935303830398123721017792 1079548084048534498306517 h2 levelEleven_fractional_7552
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_14 : ∀ i : Fin 512,
    levelEleven.lookup (7168 + i.val) ≤ levelElevenRoots.lookup (7168 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_7168
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7168 128 128
    h0 levelEleven_squares_7296
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7168 256 128
    h1 levelEleven_squares_7424
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7168 384 128
    h2 levelEleven_squares_7552
  exact h3

end WordCertDensity.Certificates
