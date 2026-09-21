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
theorem levelEleven_energy_23552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23552 128 =
      25024213512674809554499113426287 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 128 =
      845329603947140570269616 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23552 : ∀ i : Fin 128,
    levelEleven.lookup (23552 + i.val) ≤ levelElevenRoots.lookup (23552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23680 128 =
      34292393833273655351760867476695 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23680 128 =
      1018092388637896697829592 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23680 : ∀ i : Fin 128,
    levelEleven.lookup (23680 + i.val) ≤ levelElevenRoots.lookup (23680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23808 128 =
      49087863841141356988407254703456 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23808 128 =
      1123901034057895940211515 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23808 : ∀ i : Fin 128,
    levelEleven.lookup (23808 + i.val) ≤ levelElevenRoots.lookup (23808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23936 128 =
      202138210693305761074964876461055 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23936 128 =
      2877100837055344760516280 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23936 : ∀ i : Fin 128,
    levelEleven.lookup (23936 + i.val) ≤ levelElevenRoots.lookup (23936 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_46 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23552 512 =
      310542681880395582969632112067493 := by
  have h0 := levelEleven_energy_23552
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23552 256 =
      59316607345948464906259980902982 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23552 128 128
      25024213512674809554499113426287 34292393833273655351760867476695 h0 levelEleven_energy_23680
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23552 384 =
      108404471187089821894667235606438 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23552 256 128
      59316607345948464906259980902982 49087863841141356988407254703456 h1 levelEleven_energy_23808
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23552 512 =
      310542681880395582969632112067493 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23552 384 128
      108404471187089821894667235606438 202138210693305761074964876461055 h2 levelEleven_energy_23936
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_46 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 512 =
      5864423863698277968827003 := by
  have h0 := levelEleven_fractional_23552
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 256 =
      1863421992585037268099208 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 128 128
      845329603947140570269616 1018092388637896697829592 h0 levelEleven_fractional_23680
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 384 =
      2987323026642933208310723 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 256 128
      1863421992585037268099208 1123901034057895940211515 h1 levelEleven_fractional_23808
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 512 =
      5864423863698277968827003 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23552 384 128
      2987323026642933208310723 2877100837055344760516280 h2 levelEleven_fractional_23936
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_46 : ∀ i : Fin 512,
    levelEleven.lookup (23552 + i.val) ≤ levelElevenRoots.lookup (23552 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_23552
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23552 128 128
    h0 levelEleven_squares_23680
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23552 256 128
    h1 levelEleven_squares_23808
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23552 384 128
    h2 levelEleven_squares_23936
  exact h3

end WordCertDensity.Certificates
