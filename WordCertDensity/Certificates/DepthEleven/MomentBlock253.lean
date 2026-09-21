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
theorem levelEleven_energy_129536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129536 128 =
      32335388410569857257400671267897 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 128 =
      876956667051159115232597 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129536 : ∀ i : Fin 128,
    levelEleven.lookup (129536 + i.val) ≤ levelElevenRoots.lookup (129536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129664 128 =
      40784060618307614142267379986982 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129664 128 =
      1112798971886981555257762 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129664 : ∀ i : Fin 128,
    levelEleven.lookup (129664 + i.val) ≤ levelElevenRoots.lookup (129664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129792 128 =
      25044136358084263780208760708983 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129792 128 =
      783502635410063871588483 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129792 : ∀ i : Fin 128,
    levelEleven.lookup (129792 + i.val) ≤ levelElevenRoots.lookup (129792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129920 128 =
      93778966414428490284396946063415 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129920 128 =
      1628003622049559486391428 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129920 : ∀ i : Fin 128,
    levelEleven.lookup (129920 + i.val) ≤ levelElevenRoots.lookup (129920 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_253 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129536 512 =
      191942551801390225464273758027277 := by
  have h0 := levelEleven_energy_129536
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129536 256 =
      73119449028877471399668051254879 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129536 128 128
      32335388410569857257400671267897 40784060618307614142267379986982 h0 levelEleven_energy_129664
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129536 384 =
      98163585386961735179876811963862 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129536 256 128
      73119449028877471399668051254879 25044136358084263780208760708983 h1 levelEleven_energy_129792
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129536 512 =
      191942551801390225464273758027277 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129536 384 128
      98163585386961735179876811963862 93778966414428490284396946063415 h2 levelEleven_energy_129920
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_253 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 512 =
      4401261896397764028470270 := by
  have h0 := levelEleven_fractional_129536
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 256 =
      1989755638938140670490359 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 128 128
      876956667051159115232597 1112798971886981555257762 h0 levelEleven_fractional_129664
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 384 =
      2773258274348204542078842 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 256 128
      1989755638938140670490359 783502635410063871588483 h1 levelEleven_fractional_129792
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 512 =
      4401261896397764028470270 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129536 384 128
      2773258274348204542078842 1628003622049559486391428 h2 levelEleven_fractional_129920
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_253 : ∀ i : Fin 512,
    levelEleven.lookup (129536 + i.val) ≤ levelElevenRoots.lookup (129536 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_129536
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129536 128 128
    h0 levelEleven_squares_129664
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129536 256 128
    h1 levelEleven_squares_129792
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129536 384 128
    h2 levelEleven_squares_129920
  exact h3

end WordCertDensity.Certificates
