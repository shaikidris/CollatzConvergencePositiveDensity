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
theorem levelEleven_energy_79360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79360 128 =
      51602750512965509576012051198839 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 128 =
      1225128330361060825696097 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79360 : ∀ i : Fin 128,
    levelEleven.lookup (79360 + i.val) ≤ levelElevenRoots.lookup (79360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_79488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79488 128 =
      32786591881005978174140136174732 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79488 128 =
      843531851234179371509976 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79488 : ∀ i : Fin 128,
    levelEleven.lookup (79488 + i.val) ≤ levelElevenRoots.lookup (79488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_79616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79616 128 =
      43189121874322972283532576600423 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79616 128 =
      1106500403922034483249196 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79616 : ∀ i : Fin 128,
    levelEleven.lookup (79616 + i.val) ≤ levelElevenRoots.lookup (79616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_79744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79744 128 =
      68614551896258918725708628217321 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79744 128 =
      1338696809684952899806554 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79744 : ∀ i : Fin 128,
    levelEleven.lookup (79744 + i.val) ≤ levelElevenRoots.lookup (79744 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_155 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79360 512 =
      196193016164553378759393392191315 := by
  have h0 := levelEleven_energy_79360
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79360 256 =
      84389342393971487750152187373571 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79360 128 128
      51602750512965509576012051198839 32786591881005978174140136174732 h0 levelEleven_energy_79488
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79360 384 =
      127578464268294460033684763973994 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79360 256 128
      84389342393971487750152187373571 43189121874322972283532576600423 h1 levelEleven_energy_79616
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79360 512 =
      196193016164553378759393392191315 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79360 384 128
      127578464268294460033684763973994 68614551896258918725708628217321 h2 levelEleven_energy_79744
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_155 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 512 =
      4513857395202227580261823 := by
  have h0 := levelEleven_fractional_79360
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 256 =
      2068660181595240197206073 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 128 128
      1225128330361060825696097 843531851234179371509976 h0 levelEleven_fractional_79488
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 384 =
      3175160585517274680455269 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 256 128
      2068660181595240197206073 1106500403922034483249196 h1 levelEleven_fractional_79616
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 512 =
      4513857395202227580261823 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79360 384 128
      3175160585517274680455269 1338696809684952899806554 h2 levelEleven_fractional_79744
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_155 : ∀ i : Fin 512,
    levelEleven.lookup (79360 + i.val) ≤ levelElevenRoots.lookup (79360 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_79360
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79360 128 128
    h0 levelEleven_squares_79488
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79360 256 128
    h1 levelEleven_squares_79616
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79360 384 128
    h2 levelEleven_squares_79744
  exact h3

end WordCertDensity.Certificates
