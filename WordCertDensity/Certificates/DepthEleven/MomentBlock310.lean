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
theorem levelEleven_energy_158720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158720 128 =
      31770526005106722058346589158292 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 128 =
      951304804680221117168917 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158720 : ∀ i : Fin 128,
    levelEleven.lookup (158720 + i.val) ≤ levelElevenRoots.lookup (158720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158848 128 =
      28397661243998310927182151620333 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158848 128 =
      862650241828346865858573 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158848 : ∀ i : Fin 128,
    levelEleven.lookup (158848 + i.val) ≤ levelElevenRoots.lookup (158848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158976 128 =
      68607834792812610377949367334935 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158976 128 =
      1424634516235832318497078 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158976 : ∀ i : Fin 128,
    levelEleven.lookup (158976 + i.val) ≤ levelElevenRoots.lookup (158976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_159104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159104 128 =
      93292266359440287103272393698481 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159104 128 =
      1501810480078677360059966 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159104 : ∀ i : Fin 128,
    levelEleven.lookup (159104 + i.val) ≤ levelElevenRoots.lookup (159104 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_310 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158720 512 =
      222068288401357930466750501812041 := by
  have h0 := levelEleven_energy_158720
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158720 256 =
      60168187249105032985528740778625 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158720 128 128
      31770526005106722058346589158292 28397661243998310927182151620333 h0 levelEleven_energy_158848
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158720 384 =
      128776022041917643363478108113560 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158720 256 128
      60168187249105032985528740778625 68607834792812610377949367334935 h1 levelEleven_energy_158976
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158720 512 =
      222068288401357930466750501812041 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158720 384 128
      128776022041917643363478108113560 93292266359440287103272393698481 h2 levelEleven_energy_159104
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_310 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 512 =
      4740400042823077661584534 := by
  have h0 := levelEleven_fractional_158720
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 256 =
      1813955046508567983027490 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 128 128
      951304804680221117168917 862650241828346865858573 h0 levelEleven_fractional_158848
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 384 =
      3238589562744400301524568 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 256 128
      1813955046508567983027490 1424634516235832318497078 h1 levelEleven_fractional_158976
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 512 =
      4740400042823077661584534 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158720 384 128
      3238589562744400301524568 1501810480078677360059966 h2 levelEleven_fractional_159104
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_310 : ∀ i : Fin 512,
    levelEleven.lookup (158720 + i.val) ≤ levelElevenRoots.lookup (158720 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_158720
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158720 128 128
    h0 levelEleven_squares_158848
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158720 256 128
    h1 levelEleven_squares_158976
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158720 384 128
    h2 levelEleven_squares_159104
  exact h3

end WordCertDensity.Certificates
