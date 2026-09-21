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
theorem levelEleven_energy_135168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135168 128 =
      46606095006595609128351722215391 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 128 =
      1182420036623342632932817 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135168 : ∀ i : Fin 128,
    levelEleven.lookup (135168 + i.val) ≤ levelElevenRoots.lookup (135168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135296 128 =
      30951220717711757588402299561990 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135296 128 =
      915059881463518885409203 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135296 : ∀ i : Fin 128,
    levelEleven.lookup (135296 + i.val) ≤ levelElevenRoots.lookup (135296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135424 128 =
      120945859537006587284741405790187 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135424 128 =
      2016526830280509837074810 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135424 : ∀ i : Fin 128,
    levelEleven.lookup (135424 + i.val) ≤ levelElevenRoots.lookup (135424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135552 128 =
      26130176597636827771555018704045 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135552 128 =
      783232609691691610609971 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135552 : ∀ i : Fin 128,
    levelEleven.lookup (135552 + i.val) ≤ levelElevenRoots.lookup (135552 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135168 512 =
      224633351858950781773050446271613 := by
  have h0 := levelEleven_energy_135168
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135168 256 =
      77557315724307366716754021777381 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135168 128 128
      46606095006595609128351722215391 30951220717711757588402299561990 h0 levelEleven_energy_135296
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135168 384 =
      198503175261313954001495427567568 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135168 256 128
      77557315724307366716754021777381 120945859537006587284741405790187 h1 levelEleven_energy_135424
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135168 512 =
      224633351858950781773050446271613 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135168 384 128
      198503175261313954001495427567568 26130176597636827771555018704045 h2 levelEleven_energy_135552
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 512 =
      4897239358059062966026801 := by
  have h0 := levelEleven_fractional_135168
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 256 =
      2097479918086861518342020 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 128 128
      1182420036623342632932817 915059881463518885409203 h0 levelEleven_fractional_135296
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 384 =
      4114006748367371355416830 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 256 128
      2097479918086861518342020 2016526830280509837074810 h1 levelEleven_fractional_135424
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 512 =
      4897239358059062966026801 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135168 384 128
      4114006748367371355416830 783232609691691610609971 h2 levelEleven_fractional_135552
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_264 : ∀ i : Fin 512,
    levelEleven.lookup (135168 + i.val) ≤ levelElevenRoots.lookup (135168 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_135168
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135168 128 128
    h0 levelEleven_squares_135296
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135168 256 128
    h1 levelEleven_squares_135424
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135168 384 128
    h2 levelEleven_squares_135552
  exact h3

end WordCertDensity.Certificates
