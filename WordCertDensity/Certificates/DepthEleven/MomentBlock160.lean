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
theorem levelEleven_energy_81920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81920 128 =
      25284589490371897722660500510524 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 128 =
      792533501362522025093785 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81920 : ∀ i : Fin 128,
    levelEleven.lookup (81920 + i.val) ≤ levelElevenRoots.lookup (81920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82048 128 =
      32306911380424326750493722703733 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82048 128 =
      1006322655718210464285288 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82048 : ∀ i : Fin 128,
    levelEleven.lookup (82048 + i.val) ≤ levelElevenRoots.lookup (82048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82176 128 =
      27241785278219929541417499613300 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82176 128 =
      848282632035192104838070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82176 : ∀ i : Fin 128,
    levelEleven.lookup (82176 + i.val) ≤ levelElevenRoots.lookup (82176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82304 128 =
      86425182038717346899107769484991 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82304 128 =
      1570889147221211591469247 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82304 : ∀ i : Fin 128,
    levelEleven.lookup (82304 + i.val) ≤ levelElevenRoots.lookup (82304 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81920 512 =
      171258468187733500913679492312548 := by
  have h0 := levelEleven_energy_81920
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81920 256 =
      57591500870796224473154223214257 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81920 128 128
      25284589490371897722660500510524 32306911380424326750493722703733 h0 levelEleven_energy_82048
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81920 384 =
      84833286149016154014571722827557 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81920 256 128
      57591500870796224473154223214257 27241785278219929541417499613300 h1 levelEleven_energy_82176
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 81920 512 =
      171258468187733500913679492312548 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 81920 384 128
      84833286149016154014571722827557 86425182038717346899107769484991 h2 levelEleven_energy_82304
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 512 =
      4218027936337136185686390 := by
  have h0 := levelEleven_fractional_81920
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 256 =
      1798856157080732489379073 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 128 128
      792533501362522025093785 1006322655718210464285288 h0 levelEleven_fractional_82048
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 384 =
      2647138789115924594217143 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 256 128
      1798856157080732489379073 848282632035192104838070 h1 levelEleven_fractional_82176
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 512 =
      4218027936337136185686390 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81920 384 128
      2647138789115924594217143 1570889147221211591469247 h2 levelEleven_fractional_82304
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_160 : ∀ i : Fin 512,
    levelEleven.lookup (81920 + i.val) ≤ levelElevenRoots.lookup (81920 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_81920
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81920 128 128
    h0 levelEleven_squares_82048
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81920 256 128
    h1 levelEleven_squares_82176
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 81920 384 128
    h2 levelEleven_squares_82304
  exact h3

end WordCertDensity.Certificates
