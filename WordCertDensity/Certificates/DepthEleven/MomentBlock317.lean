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
theorem levelEleven_energy_162304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162304 128 =
      35139363034710485670333469580293 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 128 =
      942430240219764755280849 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162304 : ∀ i : Fin 128,
    levelEleven.lookup (162304 + i.val) ≤ levelElevenRoots.lookup (162304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162432 128 =
      42078645891300324455385576721408 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162432 128 =
      1103058320200524829987746 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162432 : ∀ i : Fin 128,
    levelEleven.lookup (162432 + i.val) ≤ levelElevenRoots.lookup (162432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162560 128 =
      21779987180504310514979366902207 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162560 128 =
      735456963420523062235591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162560 : ∀ i : Fin 128,
    levelEleven.lookup (162560 + i.val) ≤ levelElevenRoots.lookup (162560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162688 128 =
      45032667338859195109278220260198 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162688 128 =
      1195293871190669958688678 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162688 : ∀ i : Fin 128,
    levelEleven.lookup (162688 + i.val) ≤ levelElevenRoots.lookup (162688 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_317 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162304 512 =
      144030663445374315749976633464106 := by
  have h0 := levelEleven_energy_162304
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162304 256 =
      77218008926010810125719046301701 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162304 128 128
      35139363034710485670333469580293 42078645891300324455385576721408 h0 levelEleven_energy_162432
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162304 384 =
      98997996106515120640698413203908 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162304 256 128
      77218008926010810125719046301701 21779987180504310514979366902207 h1 levelEleven_energy_162560
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162304 512 =
      144030663445374315749976633464106 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162304 384 128
      98997996106515120640698413203908 45032667338859195109278220260198 h2 levelEleven_energy_162688
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_317 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 512 =
      3976239395031482606192864 := by
  have h0 := levelEleven_fractional_162304
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 256 =
      2045488560420289585268595 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 128 128
      942430240219764755280849 1103058320200524829987746 h0 levelEleven_fractional_162432
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 384 =
      2780945523840812647504186 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 256 128
      2045488560420289585268595 735456963420523062235591 h1 levelEleven_fractional_162560
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 512 =
      3976239395031482606192864 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162304 384 128
      2780945523840812647504186 1195293871190669958688678 h2 levelEleven_fractional_162688
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_317 : ∀ i : Fin 512,
    levelEleven.lookup (162304 + i.val) ≤ levelElevenRoots.lookup (162304 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_162304
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162304 128 128
    h0 levelEleven_squares_162432
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162304 256 128
    h1 levelEleven_squares_162560
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162304 384 128
    h2 levelEleven_squares_162688
  exact h3

end WordCertDensity.Certificates
