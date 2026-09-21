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
theorem levelEleven_energy_41984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41984 128 =
      33061724411464238817500154640974 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 128 =
      968395511648840924841961 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41984 : ∀ i : Fin 128,
    levelEleven.lookup (41984 + i.val) ≤ levelElevenRoots.lookup (41984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42112 128 =
      46506740909281795602984507829113 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42112 128 =
      1163244491249617064339372 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42112 : ∀ i : Fin 128,
    levelEleven.lookup (42112 + i.val) ≤ levelElevenRoots.lookup (42112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42240 128 =
      37162755846851423243907963663537 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42240 128 =
      930960672960268697678419 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42240 : ∀ i : Fin 128,
    levelEleven.lookup (42240 + i.val) ≤ levelElevenRoots.lookup (42240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_42368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 42368 128 =
      286834630268831681774296014871422 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_42368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 42368 128 =
      3105096257263673630772382 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_42368 : ∀ i : Fin 128,
    levelEleven.lookup (42368 + i.val) ≤ levelElevenRoots.lookup (42368 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_82 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41984 512 =
      403565851436429139438688641005046 := by
  have h0 := levelEleven_energy_41984
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41984 256 =
      79568465320746034420484662470087 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41984 128 128
      33061724411464238817500154640974 46506740909281795602984507829113 h0 levelEleven_energy_42112
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41984 384 =
      116731221167597457664392626133624 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41984 256 128
      79568465320746034420484662470087 37162755846851423243907963663537 h1 levelEleven_energy_42240
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41984 512 =
      403565851436429139438688641005046 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41984 384 128
      116731221167597457664392626133624 286834630268831681774296014871422 h2 levelEleven_energy_42368
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_82 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 512 =
      6167696933122400317632134 := by
  have h0 := levelEleven_fractional_41984
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 256 =
      2131640002898457989181333 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 128 128
      968395511648840924841961 1163244491249617064339372 h0 levelEleven_fractional_42112
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 384 =
      3062600675858726686859752 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 256 128
      2131640002898457989181333 930960672960268697678419 h1 levelEleven_fractional_42240
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 512 =
      6167696933122400317632134 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41984 384 128
      3062600675858726686859752 3105096257263673630772382 h2 levelEleven_fractional_42368
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_82 : ∀ i : Fin 512,
    levelEleven.lookup (41984 + i.val) ≤ levelElevenRoots.lookup (41984 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_41984
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41984 128 128
    h0 levelEleven_squares_42112
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41984 256 128
    h1 levelEleven_squares_42240
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41984 384 128
    h2 levelEleven_squares_42368
  exact h3

end WordCertDensity.Certificates
