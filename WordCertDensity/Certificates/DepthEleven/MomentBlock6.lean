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
theorem levelEleven_energy_3072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3072 128 =
      113110318585043369289028642400618 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 128 =
      1780639690636895474700505 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3072 : ∀ i : Fin 128,
    levelEleven.lookup (3072 + i.val) ≤ levelElevenRoots.lookup (3072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3200 128 =
      32905585063186444026073813892442 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3200 128 =
      928937129319773109103850 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3200 : ∀ i : Fin 128,
    levelEleven.lookup (3200 + i.val) ≤ levelElevenRoots.lookup (3200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3328 128 =
      24732223489996149877946548448931 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3328 128 =
      836687334356829371964538 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3328 : ∀ i : Fin 128,
    levelEleven.lookup (3328 + i.val) ≤ levelElevenRoots.lookup (3328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3456 128 =
      87165131163166392758771803043364 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3456 128 =
      1484821913077186138592548 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3456 : ∀ i : Fin 128,
    levelEleven.lookup (3456 + i.val) ≤ levelElevenRoots.lookup (3456 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_6 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3072 512 =
      257913258301392355951820807785355 := by
  have h0 := levelEleven_energy_3072
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3072 256 =
      146015903648229813315102456293060 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3072 128 128
      113110318585043369289028642400618 32905585063186444026073813892442 h0 levelEleven_energy_3200
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3072 384 =
      170748127138225963193049004741991 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3072 256 128
      146015903648229813315102456293060 24732223489996149877946548448931 h1 levelEleven_energy_3328
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3072 512 =
      257913258301392355951820807785355 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3072 384 128
      170748127138225963193049004741991 87165131163166392758771803043364 h2 levelEleven_energy_3456
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_6 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 512 =
      5031086067390684094361441 := by
  have h0 := levelEleven_fractional_3072
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 256 =
      2709576819956668583804355 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 128 128
      1780639690636895474700505 928937129319773109103850 h0 levelEleven_fractional_3200
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 384 =
      3546264154313497955768893 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 256 128
      2709576819956668583804355 836687334356829371964538 h1 levelEleven_fractional_3328
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 512 =
      5031086067390684094361441 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3072 384 128
      3546264154313497955768893 1484821913077186138592548 h2 levelEleven_fractional_3456
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_6 : ∀ i : Fin 512,
    levelEleven.lookup (3072 + i.val) ≤ levelElevenRoots.lookup (3072 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_3072
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3072 128 128
    h0 levelEleven_squares_3200
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3072 256 128
    h1 levelEleven_squares_3328
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3072 384 128
    h2 levelEleven_squares_3456
  exact h3

end WordCertDensity.Certificates
