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
theorem levelEleven_energy_54272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54272 128 =
      38808353429093338291129002161143 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 128 =
      1125794296850261888454566 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54272 : ∀ i : Fin 128,
    levelEleven.lookup (54272 + i.val) ≤ levelElevenRoots.lookup (54272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54400 128 =
      22133550485632144232039667924687 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54400 128 =
      732174047457332105497564 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54400 : ∀ i : Fin 128,
    levelEleven.lookup (54400 + i.val) ≤ levelElevenRoots.lookup (54400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54528 128 =
      67383372580435017632239735272122 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54528 128 =
      1458717446609322044798959 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54528 : ∀ i : Fin 128,
    levelEleven.lookup (54528 + i.val) ≤ levelElevenRoots.lookup (54528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54656 128 =
      776504124172573940400644148683909 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54656 128 =
      5515540936362622937033396 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54656 : ∀ i : Fin 128,
    levelEleven.lookup (54656 + i.val) ≤ levelElevenRoots.lookup (54656 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_106 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54272 512 =
      904829400667734440556052554041861 := by
  have h0 := levelEleven_energy_54272
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54272 256 =
      60941903914725482523168670085830 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54272 128 128
      38808353429093338291129002161143 22133550485632144232039667924687 h0 levelEleven_energy_54400
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54272 384 =
      128325276495160500155408405357952 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54272 256 128
      60941903914725482523168670085830 67383372580435017632239735272122 h1 levelEleven_energy_54528
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54272 512 =
      904829400667734440556052554041861 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54272 384 128
      128325276495160500155408405357952 776504124172573940400644148683909 h2 levelEleven_energy_54656
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_106 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 512 =
      8832226727279538975784485 := by
  have h0 := levelEleven_fractional_54272
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 256 =
      1857968344307593993952130 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 128 128
      1125794296850261888454566 732174047457332105497564 h0 levelEleven_fractional_54400
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 384 =
      3316685790916916038751089 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 256 128
      1857968344307593993952130 1458717446609322044798959 h1 levelEleven_fractional_54528
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 512 =
      8832226727279538975784485 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54272 384 128
      3316685790916916038751089 5515540936362622937033396 h2 levelEleven_fractional_54656
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_106 : ∀ i : Fin 512,
    levelEleven.lookup (54272 + i.val) ≤ levelElevenRoots.lookup (54272 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_54272
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54272 128 128
    h0 levelEleven_squares_54400
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54272 256 128
    h1 levelEleven_squares_54528
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54272 384 128
    h2 levelEleven_squares_54656
  exact h3

end WordCertDensity.Certificates
