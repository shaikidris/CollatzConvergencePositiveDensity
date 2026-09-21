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
theorem levelEleven_energy_141824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141824 128 =
      29315500886845726596846555697625 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 128 =
      945482458948189754483224 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141824 : ∀ i : Fin 128,
    levelEleven.lookup (141824 + i.val) ≤ levelElevenRoots.lookup (141824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141952 128 =
      59863780354405202933475234387915 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141952 128 =
      1348245053959800772089836 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141952 : ∀ i : Fin 128,
    levelEleven.lookup (141952 + i.val) ≤ levelElevenRoots.lookup (141952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142080 128 =
      67309634773714696763306194103317 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142080 128 =
      1409796853768492521342259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142080 : ∀ i : Fin 128,
    levelEleven.lookup (142080 + i.val) ≤ levelElevenRoots.lookup (142080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142208 128 =
      78890321750279087707292176046959 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142208 128 =
      1422243314885776456865108 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142208 : ∀ i : Fin 128,
    levelEleven.lookup (142208 + i.val) ≤ levelElevenRoots.lookup (142208 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_277 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141824 512 =
      235379237765244714000920160235816 := by
  have h0 := levelEleven_energy_141824
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141824 256 =
      89179281241250929530321790085540 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141824 128 128
      29315500886845726596846555697625 59863780354405202933475234387915 h0 levelEleven_energy_141952
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141824 384 =
      156488916014965626293627984188857 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141824 256 128
      89179281241250929530321790085540 67309634773714696763306194103317 h1 levelEleven_energy_142080
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141824 512 =
      235379237765244714000920160235816 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141824 384 128
      156488916014965626293627984188857 78890321750279087707292176046959 h2 levelEleven_energy_142208
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_277 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 512 =
      5125767681562259504780427 := by
  have h0 := levelEleven_fractional_141824
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 256 =
      2293727512907990526573060 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 128 128
      945482458948189754483224 1348245053959800772089836 h0 levelEleven_fractional_141952
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 384 =
      3703524366676483047915319 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 256 128
      2293727512907990526573060 1409796853768492521342259 h1 levelEleven_fractional_142080
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 512 =
      5125767681562259504780427 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141824 384 128
      3703524366676483047915319 1422243314885776456865108 h2 levelEleven_fractional_142208
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_277 : ∀ i : Fin 512,
    levelEleven.lookup (141824 + i.val) ≤ levelElevenRoots.lookup (141824 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_141824
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141824 128 128
    h0 levelEleven_squares_141952
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141824 256 128
    h1 levelEleven_squares_142080
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141824 384 128
    h2 levelEleven_squares_142208
  exact h3

end WordCertDensity.Certificates
