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
theorem levelEleven_energy_171520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171520 128 =
      19930371334421839419034158416552 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 128 =
      730974016728506782668260 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171520 : ∀ i : Fin 128,
    levelEleven.lookup (171520 + i.val) ≤ levelElevenRoots.lookup (171520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171648 128 =
      31841191568171303134622237482681 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171648 128 =
      1013430318039067680665152 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171648 : ∀ i : Fin 128,
    levelEleven.lookup (171648 + i.val) ≤ levelElevenRoots.lookup (171648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171776 128 =
      17662590018067117519076560320121 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171776 128 =
      675172446517345559613171 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171776 : ∀ i : Fin 128,
    levelEleven.lookup (171776 + i.val) ≤ levelElevenRoots.lookup (171776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_171904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171904 128 =
      96553796327240948996321717483947 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_171904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171904 128 =
      1732344406038196612805142 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_171904 : ∀ i : Fin 128,
    levelEleven.lookup (171904 + i.val) ≤ levelElevenRoots.lookup (171904 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_335 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 171520 512 =
      165987949247901209069054673703301 := by
  have h0 := levelEleven_energy_171520
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171520 256 =
      51771562902593142553656395899233 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171520 128 128
      19930371334421839419034158416552 31841191568171303134622237482681 h0 levelEleven_energy_171648
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171520 384 =
      69434152920660260072732956219354 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171520 256 128
      51771562902593142553656395899233 17662590018067117519076560320121 h1 levelEleven_energy_171776
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 171520 512 =
      165987949247901209069054673703301 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 171520 384 128
      69434152920660260072732956219354 96553796327240948996321717483947 h2 levelEleven_energy_171904
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_335 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 512 =
      4151921187323116635751725 := by
  have h0 := levelEleven_fractional_171520
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 256 =
      1744404334767574463333412 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 128 128
      730974016728506782668260 1013430318039067680665152 h0 levelEleven_fractional_171648
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 384 =
      2419576781284920022946583 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 256 128
      1744404334767574463333412 675172446517345559613171 h1 levelEleven_fractional_171776
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 512 =
      4151921187323116635751725 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 171520 384 128
      2419576781284920022946583 1732344406038196612805142 h2 levelEleven_fractional_171904
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_335 : ∀ i : Fin 512,
    levelEleven.lookup (171520 + i.val) ≤ levelElevenRoots.lookup (171520 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_171520
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171520 128 128
    h0 levelEleven_squares_171648
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171520 256 128
    h1 levelEleven_squares_171776
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 171520 384 128
    h2 levelEleven_squares_171904
  exact h3

end WordCertDensity.Certificates
