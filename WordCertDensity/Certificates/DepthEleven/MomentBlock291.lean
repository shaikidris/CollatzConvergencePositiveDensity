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
theorem levelEleven_energy_148992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148992 128 =
      22258340985968030619217737651081 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 128 =
      706042209244197874270893 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148992 : ∀ i : Fin 128,
    levelEleven.lookup (148992 + i.val) ≤ levelElevenRoots.lookup (148992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149120 128 =
      43426206188558700168880539206493 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149120 128 =
      1120016492733007810418531 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149120 : ∀ i : Fin 128,
    levelEleven.lookup (149120 + i.val) ≤ levelElevenRoots.lookup (149120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149248 128 =
      39134203215012532919132174616297 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149248 128 =
      982996921832458965290068 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149248 : ∀ i : Fin 128,
    levelEleven.lookup (149248 + i.val) ≤ levelElevenRoots.lookup (149248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149376 128 =
      40576393055314658232335459253821 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149376 128 =
      1022422433060190764450791 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149376 : ∀ i : Fin 128,
    levelEleven.lookup (149376 + i.val) ≤ levelElevenRoots.lookup (149376 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_291 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148992 512 =
      145395143444853921939565910727692 := by
  have h0 := levelEleven_energy_148992
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148992 256 =
      65684547174526730788098276857574 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148992 128 128
      22258340985968030619217737651081 43426206188558700168880539206493 h0 levelEleven_energy_149120
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148992 384 =
      104818750389539263707230451473871 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148992 256 128
      65684547174526730788098276857574 39134203215012532919132174616297 h1 levelEleven_energy_149248
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148992 512 =
      145395143444853921939565910727692 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148992 384 128
      104818750389539263707230451473871 40576393055314658232335459253821 h2 levelEleven_energy_149376
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_291 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 512 =
      3831478056869855414430283 := by
  have h0 := levelEleven_fractional_148992
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 256 =
      1826058701977205684689424 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 128 128
      706042209244197874270893 1120016492733007810418531 h0 levelEleven_fractional_149120
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 384 =
      2809055623809664649979492 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 256 128
      1826058701977205684689424 982996921832458965290068 h1 levelEleven_fractional_149248
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 512 =
      3831478056869855414430283 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148992 384 128
      2809055623809664649979492 1022422433060190764450791 h2 levelEleven_fractional_149376
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_291 : ∀ i : Fin 512,
    levelEleven.lookup (148992 + i.val) ≤ levelElevenRoots.lookup (148992 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_148992
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148992 128 128
    h0 levelEleven_squares_149120
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148992 256 128
    h1 levelEleven_squares_149248
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148992 384 128
    h2 levelEleven_squares_149376
  exact h3

end WordCertDensity.Certificates
