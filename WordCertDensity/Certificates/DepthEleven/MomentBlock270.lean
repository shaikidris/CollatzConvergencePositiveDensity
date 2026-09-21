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
theorem levelEleven_energy_138240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138240 128 =
      25264861666434523047448382526319 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 128 =
      819136261374260216318225 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138240 : ∀ i : Fin 128,
    levelEleven.lookup (138240 + i.val) ≤ levelElevenRoots.lookup (138240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_138368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138368 128 =
      49251331983162904403353792634060 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138368 128 =
      1194314445584817113743035 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138368 : ∀ i : Fin 128,
    levelEleven.lookup (138368 + i.val) ≤ levelElevenRoots.lookup (138368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_138496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138496 128 =
      31819165510942071730740750044334 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138496 128 =
      891747611160398376050462 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138496 : ∀ i : Fin 128,
    levelEleven.lookup (138496 + i.val) ≤ levelElevenRoots.lookup (138496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_138624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138624 128 =
      61272012852203215564133908886982 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138624 128 =
      1383233780884952078967953 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138624 : ∀ i : Fin 128,
    levelEleven.lookup (138624 + i.val) ≤ levelElevenRoots.lookup (138624 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_270 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138240 512 =
      167607372012742714745676834091695 := by
  have h0 := levelEleven_energy_138240
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138240 256 =
      74516193649597427450802175160379 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138240 128 128
      25264861666434523047448382526319 49251331983162904403353792634060 h0 levelEleven_energy_138368
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138240 384 =
      106335359160539499181542925204713 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138240 256 128
      74516193649597427450802175160379 31819165510942071730740750044334 h1 levelEleven_energy_138496
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138240 512 =
      167607372012742714745676834091695 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138240 384 128
      106335359160539499181542925204713 61272012852203215564133908886982 h2 levelEleven_energy_138624
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_270 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 512 =
      4288432099004427785079675 := by
  have h0 := levelEleven_fractional_138240
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 256 =
      2013450706959077330061260 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 128 128
      819136261374260216318225 1194314445584817113743035 h0 levelEleven_fractional_138368
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 384 =
      2905198318119475706111722 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 256 128
      2013450706959077330061260 891747611160398376050462 h1 levelEleven_fractional_138496
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 512 =
      4288432099004427785079675 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138240 384 128
      2905198318119475706111722 1383233780884952078967953 h2 levelEleven_fractional_138624
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_270 : ∀ i : Fin 512,
    levelEleven.lookup (138240 + i.val) ≤ levelElevenRoots.lookup (138240 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_138240
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138240 128 128
    h0 levelEleven_squares_138368
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138240 256 128
    h1 levelEleven_squares_138496
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138240 384 128
    h2 levelEleven_squares_138624
  exact h3

end WordCertDensity.Certificates
