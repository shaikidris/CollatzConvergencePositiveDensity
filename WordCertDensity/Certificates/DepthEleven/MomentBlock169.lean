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
theorem levelEleven_energy_86528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86528 128 =
      30326071851203128369500287640767 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 128 =
      863139949817169169920742 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86528 : ∀ i : Fin 128,
    levelEleven.lookup (86528 + i.val) ≤ levelElevenRoots.lookup (86528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86656 128 =
      74580843284838731946473214795192 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86656 128 =
      1562209334703971689714892 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86656 : ∀ i : Fin 128,
    levelEleven.lookup (86656 + i.val) ≤ levelElevenRoots.lookup (86656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86784 128 =
      34524801159371873212089220777846 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86784 128 =
      938234229987403275149437 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86784 : ∀ i : Fin 128,
    levelEleven.lookup (86784 + i.val) ≤ levelElevenRoots.lookup (86784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86912 128 =
      102809908540489814967692670253452 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86912 128 =
      1741821788427821776617428 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86912 : ∀ i : Fin 128,
    levelEleven.lookup (86912 + i.val) ≤ levelElevenRoots.lookup (86912 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_169 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86528 512 =
      242241624835903548495755393467257 := by
  have h0 := levelEleven_energy_86528
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86528 256 =
      104906915136041860315973502435959 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86528 128 128
      30326071851203128369500287640767 74580843284838731946473214795192 h0 levelEleven_energy_86656
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86528 384 =
      139431716295413733528062723213805 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86528 256 128
      104906915136041860315973502435959 34524801159371873212089220777846 h1 levelEleven_energy_86784
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86528 512 =
      242241624835903548495755393467257 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86528 384 128
      139431716295413733528062723213805 102809908540489814967692670253452 h2 levelEleven_energy_86912
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_169 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 512 =
      5105405302936365911402499 := by
  have h0 := levelEleven_fractional_86528
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 256 =
      2425349284521140859635634 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 128 128
      863139949817169169920742 1562209334703971689714892 h0 levelEleven_fractional_86656
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 384 =
      3363583514508544134785071 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 256 128
      2425349284521140859635634 938234229987403275149437 h1 levelEleven_fractional_86784
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 512 =
      5105405302936365911402499 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86528 384 128
      3363583514508544134785071 1741821788427821776617428 h2 levelEleven_fractional_86912
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_169 : ∀ i : Fin 512,
    levelEleven.lookup (86528 + i.val) ≤ levelElevenRoots.lookup (86528 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_86528
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86528 128 128
    h0 levelEleven_squares_86656
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86528 256 128
    h1 levelEleven_squares_86784
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86528 384 128
    h2 levelEleven_squares_86912
  exact h3

end WordCertDensity.Certificates
