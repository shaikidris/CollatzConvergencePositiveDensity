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
theorem levelEleven_energy_10752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10752 128 =
      97520060305346024074361351580852 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 128 =
      1654443314033709888305901 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10752 : ∀ i : Fin 128,
    levelEleven.lookup (10752 + i.val) ≤ levelElevenRoots.lookup (10752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_10880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10880 128 =
      26408264204172215178669414169055 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10880 128 =
      814883114921213055124963 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10880 : ∀ i : Fin 128,
    levelEleven.lookup (10880 + i.val) ≤ levelElevenRoots.lookup (10880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11008 128 =
      216538106171756547541699018653646 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11008 128 =
      2561850500204051182701376 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11008 : ∀ i : Fin 128,
    levelEleven.lookup (11008 + i.val) ≤ levelElevenRoots.lookup (11008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11136 128 =
      46863529450274079707402696310263 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11136 128 =
      1209761221998768739266051 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11136 : ∀ i : Fin 128,
    levelEleven.lookup (11136 + i.val) ≤ levelElevenRoots.lookup (11136 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_21 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10752 512 =
      387329960131548866502132480713816 := by
  have h0 := levelEleven_energy_10752
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10752 256 =
      123928324509518239253030765749907 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10752 128 128
      97520060305346024074361351580852 26408264204172215178669414169055 h0 levelEleven_energy_10880
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10752 384 =
      340466430681274786794729784403553 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10752 256 128
      123928324509518239253030765749907 216538106171756547541699018653646 h1 levelEleven_energy_11008
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10752 512 =
      387329960131548866502132480713816 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10752 384 128
      340466430681274786794729784403553 46863529450274079707402696310263 h2 levelEleven_energy_11136
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_21 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 512 =
      6240938151157742865398291 := by
  have h0 := levelEleven_fractional_10752
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 256 =
      2469326428954922943430864 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 128 128
      1654443314033709888305901 814883114921213055124963 h0 levelEleven_fractional_10880
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 384 =
      5031176929158974126132240 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 256 128
      2469326428954922943430864 2561850500204051182701376 h1 levelEleven_fractional_11008
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 512 =
      6240938151157742865398291 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10752 384 128
      5031176929158974126132240 1209761221998768739266051 h2 levelEleven_fractional_11136
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_21 : ∀ i : Fin 512,
    levelEleven.lookup (10752 + i.val) ≤ levelElevenRoots.lookup (10752 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_10752
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10752 128 128
    h0 levelEleven_squares_10880
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10752 256 128
    h1 levelEleven_squares_11008
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10752 384 128
    h2 levelEleven_squares_11136
  exact h3

end WordCertDensity.Certificates
