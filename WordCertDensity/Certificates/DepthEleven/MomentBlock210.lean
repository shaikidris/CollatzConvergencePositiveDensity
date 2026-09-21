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
theorem levelEleven_energy_107520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107520 128 =
      39459389376183799045653775098897 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 128 =
      1065375570613588890868411 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107520 : ∀ i : Fin 128,
    levelEleven.lookup (107520 + i.val) ≤ levelElevenRoots.lookup (107520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107648 128 =
      24278825171142759086745651270669 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107648 128 =
      791967869053414827539848 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107648 : ∀ i : Fin 128,
    levelEleven.lookup (107648 + i.val) ≤ levelElevenRoots.lookup (107648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107776 128 =
      53233584242145294079350329330227 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107776 128 =
      1254151826552156939773410 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107776 : ∀ i : Fin 128,
    levelEleven.lookup (107776 + i.val) ≤ levelElevenRoots.lookup (107776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_107904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107904 128 =
      18418829578506448259280028581073 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_107904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107904 128 =
      685573599513732777106348 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_107904 : ∀ i : Fin 128,
    levelEleven.lookup (107904 + i.val) ≤ levelElevenRoots.lookup (107904 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_210 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 107520 512 =
      135390628367978300471029784280866 := by
  have h0 := levelEleven_energy_107520
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107520 256 =
      63738214547326558132399426369566 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107520 128 128
      39459389376183799045653775098897 24278825171142759086745651270669 h0 levelEleven_energy_107648
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107520 384 =
      116971798789471852211749755699793 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107520 256 128
      63738214547326558132399426369566 53233584242145294079350329330227 h1 levelEleven_energy_107776
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 107520 512 =
      135390628367978300471029784280866 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 107520 384 128
      116971798789471852211749755699793 18418829578506448259280028581073 h2 levelEleven_energy_107904
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_210 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 512 =
      3797068865732893435288017 := by
  have h0 := levelEleven_fractional_107520
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 256 =
      1857343439667003718408259 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 128 128
      1065375570613588890868411 791967869053414827539848 h0 levelEleven_fractional_107648
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 384 =
      3111495266219160658181669 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 256 128
      1857343439667003718408259 1254151826552156939773410 h1 levelEleven_fractional_107776
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 512 =
      3797068865732893435288017 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 107520 384 128
      3111495266219160658181669 685573599513732777106348 h2 levelEleven_fractional_107904
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_210 : ∀ i : Fin 512,
    levelEleven.lookup (107520 + i.val) ≤ levelElevenRoots.lookup (107520 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_107520
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107520 128 128
    h0 levelEleven_squares_107648
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107520 256 128
    h1 levelEleven_squares_107776
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 107520 384 128
    h2 levelEleven_squares_107904
  exact h3

end WordCertDensity.Certificates
