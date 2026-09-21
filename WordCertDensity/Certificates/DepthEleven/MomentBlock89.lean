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
theorem levelEleven_energy_45568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45568 128 =
      26266677522307627145541848409554 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 128 =
      850817718295599733069378 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45568 : ∀ i : Fin 128,
    levelEleven.lookup (45568 + i.val) ≤ levelElevenRoots.lookup (45568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45696 128 =
      96164834460735671828599603711609 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45696 128 =
      1551084919634141418436238 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45696 : ∀ i : Fin 128,
    levelEleven.lookup (45696 + i.val) ≤ levelElevenRoots.lookup (45696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45824 128 =
      70529316623638734215253036363987 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45824 128 =
      1532721014973532037344200 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45824 : ∀ i : Fin 128,
    levelEleven.lookup (45824 + i.val) ≤ levelElevenRoots.lookup (45824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45952 128 =
      82311046256582428020687257897635 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45952 128 =
      1457068400017909841844666 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45952 : ∀ i : Fin 128,
    levelEleven.lookup (45952 + i.val) ≤ levelElevenRoots.lookup (45952 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_89 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45568 512 =
      275271874863264461210081746382785 := by
  have h0 := levelEleven_energy_45568
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45568 256 =
      122431511983043298974141452121163 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45568 128 128
      26266677522307627145541848409554 96164834460735671828599603711609 h0 levelEleven_energy_45696
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45568 384 =
      192960828606682033189394488485150 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45568 256 128
      122431511983043298974141452121163 70529316623638734215253036363987 h1 levelEleven_energy_45824
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45568 512 =
      275271874863264461210081746382785 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45568 384 128
      192960828606682033189394488485150 82311046256582428020687257897635 h2 levelEleven_energy_45952
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_89 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 512 =
      5391692052921183030694482 := by
  have h0 := levelEleven_fractional_45568
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 256 =
      2401902637929741151505616 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 128 128
      850817718295599733069378 1551084919634141418436238 h0 levelEleven_fractional_45696
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 384 =
      3934623652903273188849816 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 256 128
      2401902637929741151505616 1532721014973532037344200 h1 levelEleven_fractional_45824
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 512 =
      5391692052921183030694482 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45568 384 128
      3934623652903273188849816 1457068400017909841844666 h2 levelEleven_fractional_45952
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_89 : ∀ i : Fin 512,
    levelEleven.lookup (45568 + i.val) ≤ levelElevenRoots.lookup (45568 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_45568
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45568 128 128
    h0 levelEleven_squares_45696
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45568 256 128
    h1 levelEleven_squares_45824
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45568 384 128
    h2 levelEleven_squares_45952
  exact h3

end WordCertDensity.Certificates
