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
theorem levelEleven_energy_136192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136192 128 =
      33406234208195961823439125912292 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 128 =
      969047202191086180991453 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136192 : ∀ i : Fin 128,
    levelEleven.lookup (136192 + i.val) ≤ levelElevenRoots.lookup (136192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136320 128 =
      16375697229916089587847782270380 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136320 128 =
      616481702095675979069203 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136320 : ∀ i : Fin 128,
    levelEleven.lookup (136320 + i.val) ≤ levelElevenRoots.lookup (136320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136448 128 =
      53936104584662314547360063273704 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136448 128 =
      1264885609004196423575419 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136448 : ∀ i : Fin 128,
    levelEleven.lookup (136448 + i.val) ≤ levelElevenRoots.lookup (136448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136576 128 =
      39552247613423555508667089577537 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136576 128 =
      1013553724492770266356799 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136576 : ∀ i : Fin 128,
    levelEleven.lookup (136576 + i.val) ≤ levelElevenRoots.lookup (136576 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_266 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136192 512 =
      143270283636197921467314061033913 := by
  have h0 := levelEleven_energy_136192
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136192 256 =
      49781931438112051411286908182672 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136192 128 128
      33406234208195961823439125912292 16375697229916089587847782270380 h0 levelEleven_energy_136320
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136192 384 =
      103718036022774365958646971456376 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136192 256 128
      49781931438112051411286908182672 53936104584662314547360063273704 h1 levelEleven_energy_136448
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136192 512 =
      143270283636197921467314061033913 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136192 384 128
      103718036022774365958646971456376 39552247613423555508667089577537 h2 levelEleven_energy_136576
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_266 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 512 =
      3863968237783728849992874 := by
  have h0 := levelEleven_fractional_136192
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 256 =
      1585528904286762160060656 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 128 128
      969047202191086180991453 616481702095675979069203 h0 levelEleven_fractional_136320
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 384 =
      2850414513290958583636075 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 256 128
      1585528904286762160060656 1264885609004196423575419 h1 levelEleven_fractional_136448
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 512 =
      3863968237783728849992874 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136192 384 128
      2850414513290958583636075 1013553724492770266356799 h2 levelEleven_fractional_136576
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_266 : ∀ i : Fin 512,
    levelEleven.lookup (136192 + i.val) ≤ levelElevenRoots.lookup (136192 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_136192
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136192 128 128
    h0 levelEleven_squares_136320
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136192 256 128
    h1 levelEleven_squares_136448
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136192 384 128
    h2 levelEleven_squares_136576
  exact h3

end WordCertDensity.Certificates
