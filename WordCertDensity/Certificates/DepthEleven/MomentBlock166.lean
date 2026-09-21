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
theorem levelEleven_energy_84992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84992 128 =
      23321396532936831142167462644051 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_84992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 128 =
      769994795046234539638698 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_84992 : ∀ i : Fin 128,
    levelEleven.lookup (84992 + i.val) ≤ levelElevenRoots.lookup (84992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85120 128 =
      58844009753414805589846195898489 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85120 128 =
      1332534378804945420077927 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85120 : ∀ i : Fin 128,
    levelEleven.lookup (85120 + i.val) ≤ levelElevenRoots.lookup (85120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85248 128 =
      41263960841803391687477967057869 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85248 128 =
      1030190623160963838368177 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85248 : ∀ i : Fin 128,
    levelEleven.lookup (85248 + i.val) ≤ levelElevenRoots.lookup (85248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85376 128 =
      80158035107836209230019168281757 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85376 128 =
      1748002094713315556079773 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85376 : ∀ i : Fin 128,
    levelEleven.lookup (85376 + i.val) ≤ levelElevenRoots.lookup (85376 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_166 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 84992 512 =
      203587402235991237649510793882166 := by
  have h0 := levelEleven_energy_84992
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84992 256 =
      82165406286351636732013658542540 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84992 128 128
      23321396532936831142167462644051 58844009753414805589846195898489 h0 levelEleven_energy_85120
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84992 384 =
      123429367128155028419491625600409 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84992 256 128
      82165406286351636732013658542540 41263960841803391687477967057869 h1 levelEleven_energy_85248
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 84992 512 =
      203587402235991237649510793882166 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 84992 384 128
      123429367128155028419491625600409 80158035107836209230019168281757 h2 levelEleven_energy_85376
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_166 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 512 =
      4880721891725459354164575 := by
  have h0 := levelEleven_fractional_84992
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 256 =
      2102529173851179959716625 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 128 128
      769994795046234539638698 1332534378804945420077927 h0 levelEleven_fractional_85120
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 384 =
      3132719797012143798084802 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 256 128
      2102529173851179959716625 1030190623160963838368177 h1 levelEleven_fractional_85248
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 512 =
      4880721891725459354164575 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 84992 384 128
      3132719797012143798084802 1748002094713315556079773 h2 levelEleven_fractional_85376
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_166 : ∀ i : Fin 512,
    levelEleven.lookup (84992 + i.val) ≤ levelElevenRoots.lookup (84992 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_84992
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84992 128 128
    h0 levelEleven_squares_85120
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84992 256 128
    h1 levelEleven_squares_85248
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 84992 384 128
    h2 levelEleven_squares_85376
  exact h3

end WordCertDensity.Certificates
