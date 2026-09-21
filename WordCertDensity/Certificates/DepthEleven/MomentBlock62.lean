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
theorem levelEleven_energy_31744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31744 128 =
      28339614919022823214128583622981 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 128 =
      907671681752874715856642 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31744 : ∀ i : Fin 128,
    levelEleven.lookup (31744 + i.val) ≤ levelElevenRoots.lookup (31744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_31872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31872 128 =
      65355204377112226491384590136995 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31872 128 =
      1299208134843170798837679 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31872 : ∀ i : Fin 128,
    levelEleven.lookup (31872 + i.val) ≤ levelElevenRoots.lookup (31872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32000 128 =
      26063931022513007560323994408601 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32000 128 =
      838676358611646502322257 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32000 : ∀ i : Fin 128,
    levelEleven.lookup (32000 + i.val) ≤ levelElevenRoots.lookup (32000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32128 128 =
      26042699115739395131835037422883 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32128 128 =
      852821109012026442744287 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32128 : ∀ i : Fin 128,
    levelEleven.lookup (32128 + i.val) ≤ levelElevenRoots.lookup (32128 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_62 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31744 512 =
      145801449434387452397672205591460 := by
  have h0 := levelEleven_energy_31744
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31744 256 =
      93694819296135049705513173759976 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31744 128 128
      28339614919022823214128583622981 65355204377112226491384590136995 h0 levelEleven_energy_31872
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31744 384 =
      119758750318648057265837168168577 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31744 256 128
      93694819296135049705513173759976 26063931022513007560323994408601 h1 levelEleven_energy_32000
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31744 512 =
      145801449434387452397672205591460 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31744 384 128
      119758750318648057265837168168577 26042699115739395131835037422883 h2 levelEleven_energy_32128
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_62 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 512 =
      3898377284219718459760865 := by
  have h0 := levelEleven_fractional_31744
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 256 =
      2206879816596045514694321 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 128 128
      907671681752874715856642 1299208134843170798837679 h0 levelEleven_fractional_31872
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 384 =
      3045556175207692017016578 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 256 128
      2206879816596045514694321 838676358611646502322257 h1 levelEleven_fractional_32000
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 512 =
      3898377284219718459760865 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31744 384 128
      3045556175207692017016578 852821109012026442744287 h2 levelEleven_fractional_32128
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_62 : ∀ i : Fin 512,
    levelEleven.lookup (31744 + i.val) ≤ levelElevenRoots.lookup (31744 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_31744
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31744 128 128
    h0 levelEleven_squares_31872
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31744 256 128
    h1 levelEleven_squares_32000
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31744 384 128
    h2 levelEleven_squares_32128
  exact h3

end WordCertDensity.Certificates
