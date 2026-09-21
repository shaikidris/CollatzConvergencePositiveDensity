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
theorem levelEleven_energy_67072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67072 128 =
      15322261434460183394189517838296 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 128 =
      589940543557969101489857 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67072 : ∀ i : Fin 128,
    levelEleven.lookup (67072 + i.val) ≤ levelElevenRoots.lookup (67072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67200 128 =
      50632499935071367397640946813339 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67200 128 =
      1256766620362966861009141 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67200 : ∀ i : Fin 128,
    levelEleven.lookup (67200 + i.val) ≤ levelElevenRoots.lookup (67200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67328 128 =
      79283372591440182615184857581792 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67328 128 =
      1435962092526337184063522 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67328 : ∀ i : Fin 128,
    levelEleven.lookup (67328 + i.val) ≤ levelElevenRoots.lookup (67328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67456 128 =
      49681976065219067440542520023154 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67456 128 =
      1232708973928190648064415 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67456 : ∀ i : Fin 128,
    levelEleven.lookup (67456 + i.val) ≤ levelElevenRoots.lookup (67456 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_131 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67072 512 =
      194920110026190800847557842256581 := by
  have h0 := levelEleven_energy_67072
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67072 256 =
      65954761369531550791830464651635 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67072 128 128
      15322261434460183394189517838296 50632499935071367397640946813339 h0 levelEleven_energy_67200
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67072 384 =
      145238133960971733407015322233427 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67072 256 128
      65954761369531550791830464651635 79283372591440182615184857581792 h1 levelEleven_energy_67328
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67072 512 =
      194920110026190800847557842256581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67072 384 128
      145238133960971733407015322233427 49681976065219067440542520023154 h2 levelEleven_energy_67456
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_131 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 512 =
      4515378230375463794626935 := by
  have h0 := levelEleven_fractional_67072
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 256 =
      1846707163920935962498998 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 128 128
      589940543557969101489857 1256766620362966861009141 h0 levelEleven_fractional_67200
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 384 =
      3282669256447273146562520 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 256 128
      1846707163920935962498998 1435962092526337184063522 h1 levelEleven_fractional_67328
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 512 =
      4515378230375463794626935 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67072 384 128
      3282669256447273146562520 1232708973928190648064415 h2 levelEleven_fractional_67456
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_131 : ∀ i : Fin 512,
    levelEleven.lookup (67072 + i.val) ≤ levelElevenRoots.lookup (67072 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_67072
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67072 128 128
    h0 levelEleven_squares_67200
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67072 256 128
    h1 levelEleven_squares_67328
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67072 384 128
    h2 levelEleven_squares_67456
  exact h3

end WordCertDensity.Certificates
