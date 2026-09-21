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
theorem levelEleven_energy_130048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130048 128 =
      25576127116520926157424707660514 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 128 =
      801238303038707721000930 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130048 : ∀ i : Fin 128,
    levelEleven.lookup (130048 + i.val) ≤ levelElevenRoots.lookup (130048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130176 128 =
      38832569845187201163065299181640 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130176 128 =
      1033604165562981015993524 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130176 : ∀ i : Fin 128,
    levelEleven.lookup (130176 + i.val) ≤ levelElevenRoots.lookup (130176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130304 128 =
      132557030910015531410151703072057 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130304 128 =
      2055430611368264442395591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130304 : ∀ i : Fin 128,
    levelEleven.lookup (130304 + i.val) ≤ levelElevenRoots.lookup (130304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130432 128 =
      41325632773959134860474409588536 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130432 128 =
      1013677712185385440814484 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130432 : ∀ i : Fin 128,
    levelEleven.lookup (130432 + i.val) ≤ levelElevenRoots.lookup (130432 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_254 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130048 512 =
      238291360645682793591116119502747 := by
  have h0 := levelEleven_energy_130048
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130048 256 =
      64408696961708127320490006842154 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130048 128 128
      25576127116520926157424707660514 38832569845187201163065299181640 h0 levelEleven_energy_130176
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130048 384 =
      196965727871723658730641709914211 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130048 256 128
      64408696961708127320490006842154 132557030910015531410151703072057 h1 levelEleven_energy_130304
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130048 512 =
      238291360645682793591116119502747 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130048 384 128
      196965727871723658730641709914211 41325632773959134860474409588536 h2 levelEleven_energy_130432
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_254 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 512 =
      4903950792155338620204529 := by
  have h0 := levelEleven_fractional_130048
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 256 =
      1834842468601688736994454 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 128 128
      801238303038707721000930 1033604165562981015993524 h0 levelEleven_fractional_130176
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 384 =
      3890273079969953179390045 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 256 128
      1834842468601688736994454 2055430611368264442395591 h1 levelEleven_fractional_130304
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 512 =
      4903950792155338620204529 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130048 384 128
      3890273079969953179390045 1013677712185385440814484 h2 levelEleven_fractional_130432
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_254 : ∀ i : Fin 512,
    levelEleven.lookup (130048 + i.val) ≤ levelElevenRoots.lookup (130048 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_130048
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130048 128 128
    h0 levelEleven_squares_130176
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130048 256 128
    h1 levelEleven_squares_130304
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130048 384 128
    h2 levelEleven_squares_130432
  exact h3

end WordCertDensity.Certificates
