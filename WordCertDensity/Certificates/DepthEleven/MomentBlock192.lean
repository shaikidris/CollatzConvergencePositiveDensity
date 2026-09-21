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
theorem levelEleven_energy_98304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98304 128 =
      116046909316326401372807954582958 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 128 =
      1987040273385917676318145 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98304 : ∀ i : Fin 128,
    levelEleven.lookup (98304 + i.val) ≤ levelElevenRoots.lookup (98304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98432 128 =
      23655598611429445485020521612941 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98432 128 =
      725334037309226114852484 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98432 : ∀ i : Fin 128,
    levelEleven.lookup (98432 + i.val) ≤ levelElevenRoots.lookup (98432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98560 128 =
      79003736003388429061298740846986 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98560 128 =
      1684271971678436764640592 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98560 : ∀ i : Fin 128,
    levelEleven.lookup (98560 + i.val) ≤ levelElevenRoots.lookup (98560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98688 128 =
      38250259434866977594865588187655 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98688 128 =
      975255047126394913666378 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98688 : ∀ i : Fin 128,
    levelEleven.lookup (98688 + i.val) ≤ levelElevenRoots.lookup (98688 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98304 512 =
      256956503366011253513992805230540 := by
  have h0 := levelEleven_energy_98304
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98304 256 =
      139702507927755846857828476195899 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98304 128 128
      116046909316326401372807954582958 23655598611429445485020521612941 h0 levelEleven_energy_98432
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98304 384 =
      218706243931144275919127217042885 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98304 256 128
      139702507927755846857828476195899 79003736003388429061298740846986 h1 levelEleven_energy_98560
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98304 512 =
      256956503366011253513992805230540 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98304 384 128
      218706243931144275919127217042885 38250259434866977594865588187655 h2 levelEleven_energy_98688
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 512 =
      5371901329499975469477599 := by
  have h0 := levelEleven_fractional_98304
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 256 =
      2712374310695143791170629 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 128 128
      1987040273385917676318145 725334037309226114852484 h0 levelEleven_fractional_98432
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 384 =
      4396646282373580555811221 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 256 128
      2712374310695143791170629 1684271971678436764640592 h1 levelEleven_fractional_98560
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 512 =
      5371901329499975469477599 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98304 384 128
      4396646282373580555811221 975255047126394913666378 h2 levelEleven_fractional_98688
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_192 : ∀ i : Fin 512,
    levelEleven.lookup (98304 + i.val) ≤ levelElevenRoots.lookup (98304 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_98304
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98304 128 128
    h0 levelEleven_squares_98432
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98304 256 128
    h1 levelEleven_squares_98560
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98304 384 128
    h2 levelEleven_squares_98688
  exact h3

end WordCertDensity.Certificates
