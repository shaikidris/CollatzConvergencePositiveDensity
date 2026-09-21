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
theorem levelEleven_energy_48640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48640 128 =
      22172096122910655168532540777641 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 128 =
      756692134524770606623069 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48640 : ∀ i : Fin 128,
    levelEleven.lookup (48640 + i.val) ≤ levelElevenRoots.lookup (48640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48768 128 =
      90982985348414590938332607926169 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48768 128 =
      1659585303813307438459843 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48768 : ∀ i : Fin 128,
    levelEleven.lookup (48768 + i.val) ≤ levelElevenRoots.lookup (48768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48896 128 =
      31940541422729143460239708637709 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48896 128 =
      871080206570049448527124 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48896 : ∀ i : Fin 128,
    levelEleven.lookup (48896 + i.val) ≤ levelElevenRoots.lookup (48896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49024 128 =
      55054797312819452215079230386868 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49024 128 =
      1264796207156025198464482 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49024 : ∀ i : Fin 128,
    levelEleven.lookup (49024 + i.val) ≤ levelElevenRoots.lookup (49024 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_95 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48640 512 =
      200150420206873841782184087728387 := by
  have h0 := levelEleven_energy_48640
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48640 256 =
      113155081471325246106865148703810 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48640 128 128
      22172096122910655168532540777641 90982985348414590938332607926169 h0 levelEleven_energy_48768
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48640 384 =
      145095622894054389567104857341519 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48640 256 128
      113155081471325246106865148703810 31940541422729143460239708637709 h1 levelEleven_energy_48896
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48640 512 =
      200150420206873841782184087728387 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48640 384 128
      145095622894054389567104857341519 55054797312819452215079230386868 h2 levelEleven_energy_49024
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_95 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 512 =
      4552153852064152692074518 := by
  have h0 := levelEleven_fractional_48640
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 256 =
      2416277438338078045082912 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 128 128
      756692134524770606623069 1659585303813307438459843 h0 levelEleven_fractional_48768
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 384 =
      3287357644908127493610036 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 256 128
      2416277438338078045082912 871080206570049448527124 h1 levelEleven_fractional_48896
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 512 =
      4552153852064152692074518 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48640 384 128
      3287357644908127493610036 1264796207156025198464482 h2 levelEleven_fractional_49024
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_95 : ∀ i : Fin 512,
    levelEleven.lookup (48640 + i.val) ≤ levelElevenRoots.lookup (48640 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_48640
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48640 128 128
    h0 levelEleven_squares_48768
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48640 256 128
    h1 levelEleven_squares_48896
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48640 384 128
    h2 levelEleven_squares_49024
  exact h3

end WordCertDensity.Certificates
