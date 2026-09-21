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
theorem levelEleven_energy_95744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95744 128 =
      30139228961669478858482771582875 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 128 =
      928975065328681547484063 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95744 : ∀ i : Fin 128,
    levelEleven.lookup (95744 + i.val) ≤ levelElevenRoots.lookup (95744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_95872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95872 128 =
      30129918242051226241726920938163 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95872 128 =
      941532453906047352089294 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95872 : ∀ i : Fin 128,
    levelEleven.lookup (95872 + i.val) ≤ levelElevenRoots.lookup (95872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96000 128 =
      38748536501821247287463792106582 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96000 128 =
      1027672687810671732270392 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96000 : ∀ i : Fin 128,
    levelEleven.lookup (96000 + i.val) ≤ levelElevenRoots.lookup (96000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96128 128 =
      100753290883968187982642213354569 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96128 128 =
      1829424987591112239292995 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96128 : ∀ i : Fin 128,
    levelEleven.lookup (96128 + i.val) ≤ levelElevenRoots.lookup (96128 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_187 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95744 512 =
      199770974589510140370315697982189 := by
  have h0 := levelEleven_energy_95744
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95744 256 =
      60269147203720705100209692521038 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95744 128 128
      30139228961669478858482771582875 30129918242051226241726920938163 h0 levelEleven_energy_95872
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95744 384 =
      99017683705541952387673484627620 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95744 256 128
      60269147203720705100209692521038 38748536501821247287463792106582 h1 levelEleven_energy_96000
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95744 512 =
      199770974589510140370315697982189 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95744 384 128
      99017683705541952387673484627620 100753290883968187982642213354569 h2 levelEleven_energy_96128
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_187 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 512 =
      4727605194636512871136744 := by
  have h0 := levelEleven_fractional_95744
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 256 =
      1870507519234728899573357 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 128 128
      928975065328681547484063 941532453906047352089294 h0 levelEleven_fractional_95872
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 384 =
      2898180207045400631843749 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 256 128
      1870507519234728899573357 1027672687810671732270392 h1 levelEleven_fractional_96000
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 512 =
      4727605194636512871136744 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95744 384 128
      2898180207045400631843749 1829424987591112239292995 h2 levelEleven_fractional_96128
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_187 : ∀ i : Fin 512,
    levelEleven.lookup (95744 + i.val) ≤ levelElevenRoots.lookup (95744 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_95744
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95744 128 128
    h0 levelEleven_squares_95872
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95744 256 128
    h1 levelEleven_squares_96000
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95744 384 128
    h2 levelEleven_squares_96128
  exact h3

end WordCertDensity.Certificates
