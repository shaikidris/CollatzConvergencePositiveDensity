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
theorem levelEleven_energy_16896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16896 128 =
      51792688161046682709132431175637 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 128 =
      1278460037580188999202897 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16896 : ∀ i : Fin 128,
    levelEleven.lookup (16896 + i.val) ≤ levelElevenRoots.lookup (16896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17024 128 =
      78656314475570356546544028126045 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17024 128 =
      1492650595504233088645169 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17024 : ∀ i : Fin 128,
    levelEleven.lookup (17024 + i.val) ≤ levelElevenRoots.lookup (17024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17152 128 =
      46505857050308239491792969030480 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17152 128 =
      1231368064512519504742861 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17152 : ∀ i : Fin 128,
    levelEleven.lookup (17152 + i.val) ≤ levelElevenRoots.lookup (17152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17280 128 =
      74439541093081463949318888420229 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17280 128 =
      1489123988990444277003207 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17280 : ∀ i : Fin 128,
    levelEleven.lookup (17280 + i.val) ≤ levelElevenRoots.lookup (17280 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_33 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16896 512 =
      251394400780006742696788316752391 := by
  have h0 := levelEleven_energy_16896
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16896 256 =
      130449002636617039255676459301682 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16896 128 128
      51792688161046682709132431175637 78656314475570356546544028126045 h0 levelEleven_energy_17024
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16896 384 =
      176954859686925278747469428332162 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16896 256 128
      130449002636617039255676459301682 46505857050308239491792969030480 h1 levelEleven_energy_17152
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16896 512 =
      251394400780006742696788316752391 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16896 384 128
      176954859686925278747469428332162 74439541093081463949318888420229 h2 levelEleven_energy_17280
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_33 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 512 =
      5491602686587385869594134 := by
  have h0 := levelEleven_fractional_16896
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 256 =
      2771110633084422087848066 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 128 128
      1278460037580188999202897 1492650595504233088645169 h0 levelEleven_fractional_17024
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 384 =
      4002478697596941592590927 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 256 128
      2771110633084422087848066 1231368064512519504742861 h1 levelEleven_fractional_17152
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 512 =
      5491602686587385869594134 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16896 384 128
      4002478697596941592590927 1489123988990444277003207 h2 levelEleven_fractional_17280
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_33 : ∀ i : Fin 512,
    levelEleven.lookup (16896 + i.val) ≤ levelElevenRoots.lookup (16896 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_16896
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16896 128 128
    h0 levelEleven_squares_17024
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16896 256 128
    h1 levelEleven_squares_17152
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16896 384 128
    h2 levelEleven_squares_17280
  exact h3

end WordCertDensity.Certificates
