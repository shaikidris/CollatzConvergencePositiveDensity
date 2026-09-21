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
theorem levelEleven_energy_125952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125952 128 =
      32280722501875777517273855743167 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_125952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 128 =
      926175235701143289993734 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_125952 : ∀ i : Fin 128,
    levelEleven.lookup (125952 + i.val) ≤ levelElevenRoots.lookup (125952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126080 128 =
      24393340342527128430627205728025 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126080 128 =
      711078411893987395085226 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126080 : ∀ i : Fin 128,
    levelEleven.lookup (126080 + i.val) ≤ levelElevenRoots.lookup (126080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126208 128 =
      63591631726402381731693524892504 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126208 128 =
      1475702880034565363029521 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126208 : ∀ i : Fin 128,
    levelEleven.lookup (126208 + i.val) ≤ levelElevenRoots.lookup (126208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_126336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126336 128 =
      26879866592404999290183898763847 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126336 128 =
      874983335717549227801398 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126336 : ∀ i : Fin 128,
    levelEleven.lookup (126336 + i.val) ≤ levelElevenRoots.lookup (126336 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_246 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 125952 512 =
      147145561163210286969778485127543 := by
  have h0 := levelEleven_energy_125952
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125952 256 =
      56674062844402905947901061471192 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125952 128 128
      32280722501875777517273855743167 24393340342527128430627205728025 h0 levelEleven_energy_126080
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125952 384 =
      120265694570805287679594586363696 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125952 256 128
      56674062844402905947901061471192 63591631726402381731693524892504 h1 levelEleven_energy_126208
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 125952 512 =
      147145561163210286969778485127543 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 125952 384 128
      120265694570805287679594586363696 26879866592404999290183898763847 h2 levelEleven_energy_126336
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_246 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 512 =
      3987939863347245275909879 := by
  have h0 := levelEleven_fractional_125952
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 256 =
      1637253647595130685078960 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 128 128
      926175235701143289993734 711078411893987395085226 h0 levelEleven_fractional_126080
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 384 =
      3112956527629696048108481 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 256 128
      1637253647595130685078960 1475702880034565363029521 h1 levelEleven_fractional_126208
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 512 =
      3987939863347245275909879 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 125952 384 128
      3112956527629696048108481 874983335717549227801398 h2 levelEleven_fractional_126336
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_246 : ∀ i : Fin 512,
    levelEleven.lookup (125952 + i.val) ≤ levelElevenRoots.lookup (125952 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_125952
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125952 128 128
    h0 levelEleven_squares_126080
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125952 256 128
    h1 levelEleven_squares_126208
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 125952 384 128
    h2 levelEleven_squares_126336
  exact h3

end WordCertDensity.Certificates
