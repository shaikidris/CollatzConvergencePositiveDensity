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
theorem levelEleven_energy_25600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25600 128 =
      104479210106709862826612845698090 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 128 =
      1817380150861148229664407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25600 : ∀ i : Fin 128,
    levelEleven.lookup (25600 + i.val) ≤ levelElevenRoots.lookup (25600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25728 128 =
      67315501166745275398903137391902 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25728 128 =
      1364813988492618453195856 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25728 : ∀ i : Fin 128,
    levelEleven.lookup (25728 + i.val) ≤ levelElevenRoots.lookup (25728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25856 128 =
      33421940477301748563827689670721 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25856 128 =
      993511428238967005929243 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25856 : ∀ i : Fin 128,
    levelEleven.lookup (25856 + i.val) ≤ levelElevenRoots.lookup (25856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25984 128 =
      45562220008520121668524614226290 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25984 128 =
      1054923591371471976834960 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25984 : ∀ i : Fin 128,
    levelEleven.lookup (25984 + i.val) ≤ levelElevenRoots.lookup (25984 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_50 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25600 512 =
      250778871759277008457868286987003 := by
  have h0 := levelEleven_energy_25600
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25600 256 =
      171794711273455138225515983089992 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25600 128 128
      104479210106709862826612845698090 67315501166745275398903137391902 h0 levelEleven_energy_25728
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25600 384 =
      205216651750756886789343672760713 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25600 256 128
      171794711273455138225515983089992 33421940477301748563827689670721 h1 levelEleven_energy_25856
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25600 512 =
      250778871759277008457868286987003 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25600 384 128
      205216651750756886789343672760713 45562220008520121668524614226290 h2 levelEleven_energy_25984
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_50 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 512 =
      5230629158964205665624466 := by
  have h0 := levelEleven_fractional_25600
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 256 =
      3182194139353766682860263 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 128 128
      1817380150861148229664407 1364813988492618453195856 h0 levelEleven_fractional_25728
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 384 =
      4175705567592733688789506 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 256 128
      3182194139353766682860263 993511428238967005929243 h1 levelEleven_fractional_25856
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 512 =
      5230629158964205665624466 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25600 384 128
      4175705567592733688789506 1054923591371471976834960 h2 levelEleven_fractional_25984
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_50 : ∀ i : Fin 512,
    levelEleven.lookup (25600 + i.val) ≤ levelElevenRoots.lookup (25600 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_25600
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25600 128 128
    h0 levelEleven_squares_25728
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25600 256 128
    h1 levelEleven_squares_25856
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25600 384 128
    h2 levelEleven_squares_25984
  exact h3

end WordCertDensity.Certificates
