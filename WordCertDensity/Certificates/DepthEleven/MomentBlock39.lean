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
theorem levelEleven_energy_19968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19968 128 =
      38551893556617077574414379140803 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 128 =
      1065033252743400136326575 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19968 : ∀ i : Fin 128,
    levelEleven.lookup (19968 + i.val) ≤ levelElevenRoots.lookup (19968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20096 128 =
      39404009561018526488609195207054 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20096 128 =
      1033038681530000259627994 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20096 : ∀ i : Fin 128,
    levelEleven.lookup (20096 + i.val) ≤ levelElevenRoots.lookup (20096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20224 128 =
      43759231903989806982902744534684 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20224 128 =
      1128225935574026373104670 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20224 : ∀ i : Fin 128,
    levelEleven.lookup (20224 + i.val) ≤ levelElevenRoots.lookup (20224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20352 128 =
      26184918246496744369252130228693 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20352 128 =
      774930861500647912741016 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20352 : ∀ i : Fin 128,
    levelEleven.lookup (20352 + i.val) ≤ levelElevenRoots.lookup (20352 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_39 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19968 512 =
      147900053268122155415178449111234 := by
  have h0 := levelEleven_energy_19968
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19968 256 =
      77955903117635604063023574347857 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19968 128 128
      38551893556617077574414379140803 39404009561018526488609195207054 h0 levelEleven_energy_20096
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19968 384 =
      121715135021625411045926318882541 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19968 256 128
      77955903117635604063023574347857 43759231903989806982902744534684 h1 levelEleven_energy_20224
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19968 512 =
      147900053268122155415178449111234 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19968 384 128
      121715135021625411045926318882541 26184918246496744369252130228693 h2 levelEleven_energy_20352
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_39 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 512 =
      4001228731348074681800255 := by
  have h0 := levelEleven_fractional_19968
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 256 =
      2098071934273400395954569 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 128 128
      1065033252743400136326575 1033038681530000259627994 h0 levelEleven_fractional_20096
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 384 =
      3226297869847426769059239 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 256 128
      2098071934273400395954569 1128225935574026373104670 h1 levelEleven_fractional_20224
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 512 =
      4001228731348074681800255 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19968 384 128
      3226297869847426769059239 774930861500647912741016 h2 levelEleven_fractional_20352
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_39 : ∀ i : Fin 512,
    levelEleven.lookup (19968 + i.val) ≤ levelElevenRoots.lookup (19968 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_19968
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19968 128 128
    h0 levelEleven_squares_20096
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19968 256 128
    h1 levelEleven_squares_20224
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19968 384 128
    h2 levelEleven_squares_20352
  exact h3

end WordCertDensity.Certificates
