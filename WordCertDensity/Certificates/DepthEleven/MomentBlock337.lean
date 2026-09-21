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
theorem levelEleven_energy_172544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172544 128 =
      53270209367920651920119786439106 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 128 =
      1177246360936611592521384 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172544 : ∀ i : Fin 128,
    levelEleven.lookup (172544 + i.val) ≤ levelElevenRoots.lookup (172544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172672 128 =
      172459388182499888962160559189537 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172672 128 =
      2378818972685194448312669 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172672 : ∀ i : Fin 128,
    levelEleven.lookup (172672 + i.val) ≤ levelElevenRoots.lookup (172672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172800 128 =
      47522408571389549940197671681596 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172800 128 =
      1070919019159716674852070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172800 : ∀ i : Fin 128,
    levelEleven.lookup (172800 + i.val) ≤ levelElevenRoots.lookup (172800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_172928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172928 128 =
      64996296522959305057913417955133 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_172928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172928 128 =
      1444304970901443600606674 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_172928 : ∀ i : Fin 128,
    levelEleven.lookup (172928 + i.val) ≤ levelElevenRoots.lookup (172928 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_337 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 172544 512 =
      338248302644769395880391435265372 := by
  have h0 := levelEleven_energy_172544
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172544 256 =
      225729597550420540882280345628643 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172544 128 128
      53270209367920651920119786439106 172459388182499888962160559189537 h0 levelEleven_energy_172672
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172544 384 =
      273252006121810090822478017310239 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172544 256 128
      225729597550420540882280345628643 47522408571389549940197671681596 h1 levelEleven_energy_172800
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 172544 512 =
      338248302644769395880391435265372 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 172544 384 128
      273252006121810090822478017310239 64996296522959305057913417955133 h2 levelEleven_energy_172928
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_337 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 512 =
      6071289323682966316292797 := by
  have h0 := levelEleven_fractional_172544
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 256 =
      3556065333621806040834053 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 128 128
      1177246360936611592521384 2378818972685194448312669 h0 levelEleven_fractional_172672
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 384 =
      4626984352781522715686123 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 256 128
      3556065333621806040834053 1070919019159716674852070 h1 levelEleven_fractional_172800
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 512 =
      6071289323682966316292797 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 172544 384 128
      4626984352781522715686123 1444304970901443600606674 h2 levelEleven_fractional_172928
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_337 : ∀ i : Fin 512,
    levelEleven.lookup (172544 + i.val) ≤ levelElevenRoots.lookup (172544 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_172544
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172544 128 128
    h0 levelEleven_squares_172672
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172544 256 128
    h1 levelEleven_squares_172800
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 172544 384 128
    h2 levelEleven_squares_172928
  exact h3

end WordCertDensity.Certificates
