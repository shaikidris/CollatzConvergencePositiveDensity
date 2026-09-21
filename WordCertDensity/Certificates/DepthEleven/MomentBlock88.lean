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
theorem levelEleven_energy_45056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45056 128 =
      48115760185038116914423686817438 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 128 =
      1152612450037410330281376 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45056 : ∀ i : Fin 128,
    levelEleven.lookup (45056 + i.val) ≤ levelElevenRoots.lookup (45056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45184 128 =
      20083041371612661498341032732756 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45184 128 =
      714370146529093938985051 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45184 : ∀ i : Fin 128,
    levelEleven.lookup (45184 + i.val) ≤ levelElevenRoots.lookup (45184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45312 128 =
      44411284826213271218742381838843 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45312 128 =
      1164109379148315589850025 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45312 : ∀ i : Fin 128,
    levelEleven.lookup (45312 + i.val) ≤ levelElevenRoots.lookup (45312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_45440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45440 128 =
      52345925443081452365797332366061 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_45440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45440 128 =
      1213364321931499498170801 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_45440 : ∀ i : Fin 128,
    levelEleven.lookup (45440 + i.val) ≤ levelElevenRoots.lookup (45440 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_88 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 45056 512 =
      164956011825945501997304433755098 := by
  have h0 := levelEleven_energy_45056
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45056 256 =
      68198801556650778412764719550194 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45056 128 128
      48115760185038116914423686817438 20083041371612661498341032732756 h0 levelEleven_energy_45184
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45056 384 =
      112610086382864049631507101389037 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45056 256 128
      68198801556650778412764719550194 44411284826213271218742381838843 h1 levelEleven_energy_45312
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 45056 512 =
      164956011825945501997304433755098 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 45056 384 128
      112610086382864049631507101389037 52345925443081452365797332366061 h2 levelEleven_energy_45440
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_88 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 512 =
      4244456297646319357287253 := by
  have h0 := levelEleven_fractional_45056
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 256 =
      1866982596566504269266427 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 128 128
      1152612450037410330281376 714370146529093938985051 h0 levelEleven_fractional_45184
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 384 =
      3031091975714819859116452 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 256 128
      1866982596566504269266427 1164109379148315589850025 h1 levelEleven_fractional_45312
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 512 =
      4244456297646319357287253 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 45056 384 128
      3031091975714819859116452 1213364321931499498170801 h2 levelEleven_fractional_45440
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_88 : ∀ i : Fin 512,
    levelEleven.lookup (45056 + i.val) ≤ levelElevenRoots.lookup (45056 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_45056
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45056 128 128
    h0 levelEleven_squares_45184
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45056 256 128
    h1 levelEleven_squares_45312
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 45056 384 128
    h2 levelEleven_squares_45440
  exact h3

end WordCertDensity.Certificates
