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
theorem levelEleven_energy_108032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108032 128 =
      67683985712961141378785154846902 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 128 =
      1475879030625218160865891 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108032 : ∀ i : Fin 128,
    levelEleven.lookup (108032 + i.val) ≤ levelElevenRoots.lookup (108032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108160 128 =
      44315400732106288738176066204842 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108160 128 =
      1095756444290881488582009 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108160 : ∀ i : Fin 128,
    levelEleven.lookup (108160 + i.val) ≤ levelElevenRoots.lookup (108160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108288 128 =
      29278070609886443878516919812894 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108288 128 =
      923823904611834152012368 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108288 : ∀ i : Fin 128,
    levelEleven.lookup (108288 + i.val) ≤ levelElevenRoots.lookup (108288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108416 128 =
      59151451098601231884997387433566 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108416 128 =
      1227723553355370919171442 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108416 : ∀ i : Fin 128,
    levelEleven.lookup (108416 + i.val) ≤ levelElevenRoots.lookup (108416 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_211 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108032 512 =
      200428908153555105880475528298204 := by
  have h0 := levelEleven_energy_108032
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108032 256 =
      111999386445067430116961221051744 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108032 128 128
      67683985712961141378785154846902 44315400732106288738176066204842 h0 levelEleven_energy_108160
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108032 384 =
      141277457054953873995478140864638 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108032 256 128
      111999386445067430116961221051744 29278070609886443878516919812894 h1 levelEleven_energy_108288
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108032 512 =
      200428908153555105880475528298204 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108032 384 128
      141277457054953873995478140864638 59151451098601231884997387433566 h2 levelEleven_energy_108416
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_211 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 512 =
      4723182932883304720631710 := by
  have h0 := levelEleven_fractional_108032
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 256 =
      2571635474916099649447900 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 128 128
      1475879030625218160865891 1095756444290881488582009 h0 levelEleven_fractional_108160
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 384 =
      3495459379527933801460268 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 256 128
      2571635474916099649447900 923823904611834152012368 h1 levelEleven_fractional_108288
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 512 =
      4723182932883304720631710 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108032 384 128
      3495459379527933801460268 1227723553355370919171442 h2 levelEleven_fractional_108416
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_211 : ∀ i : Fin 512,
    levelEleven.lookup (108032 + i.val) ≤ levelElevenRoots.lookup (108032 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_108032
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108032 128 128
    h0 levelEleven_squares_108160
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108032 256 128
    h1 levelEleven_squares_108288
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108032 384 128
    h2 levelEleven_squares_108416
  exact h3

end WordCertDensity.Certificates
