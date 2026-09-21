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
theorem levelEleven_energy_65536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65536 128 =
      51417466126058532451375766397823 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 128 =
      1200587821060590269401819 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65536 : ∀ i : Fin 128,
    levelEleven.lookup (65536 + i.val) ≤ levelElevenRoots.lookup (65536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65664 128 =
      42561532176279607114140296453925 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65664 128 =
      1140868157093238064874345 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65664 : ∀ i : Fin 128,
    levelEleven.lookup (65664 + i.val) ≤ levelElevenRoots.lookup (65664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65792 128 =
      42354013514834638122680570756779 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65792 128 =
      1082630637501159080983599 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65792 : ∀ i : Fin 128,
    levelEleven.lookup (65792 + i.val) ≤ levelElevenRoots.lookup (65792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65920 128 =
      44869082637600318130583848599558 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65920 128 =
      1147565774480031584385726 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65920 : ∀ i : Fin 128,
    levelEleven.lookup (65920 + i.val) ≤ levelElevenRoots.lookup (65920 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65536 512 =
      181202094454773095818780482208085 := by
  have h0 := levelEleven_energy_65536
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65536 256 =
      93978998302338139565516062851748 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65536 128 128
      51417466126058532451375766397823 42561532176279607114140296453925 h0 levelEleven_energy_65664
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65536 384 =
      136333011817172777688196633608527 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65536 256 128
      93978998302338139565516062851748 42354013514834638122680570756779 h1 levelEleven_energy_65792
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65536 512 =
      181202094454773095818780482208085 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65536 384 128
      136333011817172777688196633608527 44869082637600318130583848599558 h2 levelEleven_energy_65920
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 512 =
      4571652390135018999645489 := by
  have h0 := levelEleven_fractional_65536
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 256 =
      2341455978153828334276164 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 128 128
      1200587821060590269401819 1140868157093238064874345 h0 levelEleven_fractional_65664
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 384 =
      3424086615654987415259763 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 256 128
      2341455978153828334276164 1082630637501159080983599 h1 levelEleven_fractional_65792
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 512 =
      4571652390135018999645489 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65536 384 128
      3424086615654987415259763 1147565774480031584385726 h2 levelEleven_fractional_65920
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_128 : ∀ i : Fin 512,
    levelEleven.lookup (65536 + i.val) ≤ levelElevenRoots.lookup (65536 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_65536
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65536 128 128
    h0 levelEleven_squares_65664
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65536 256 128
    h1 levelEleven_squares_65792
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65536 384 128
    h2 levelEleven_squares_65920
  exact h3

end WordCertDensity.Certificates
