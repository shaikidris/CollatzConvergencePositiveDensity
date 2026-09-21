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
theorem levelEleven_energy_113664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113664 128 =
      281374711533421578041972073203074 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 128 =
      2889680056628539278932292 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113664 : ∀ i : Fin 128,
    levelEleven.lookup (113664 + i.val) ≤ levelElevenRoots.lookup (113664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113792 128 =
      41402651030513617882006007571483 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113792 128 =
      1100857118166454145282954 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113792 : ∀ i : Fin 128,
    levelEleven.lookup (113792 + i.val) ≤ levelElevenRoots.lookup (113792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113920 128 =
      59800440266236990267366993661006 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113920 128 =
      1340232163253192750301509 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113920 : ∀ i : Fin 128,
    levelEleven.lookup (113920 + i.val) ≤ levelElevenRoots.lookup (113920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114048 128 =
      43676467104138971062185051930310 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114048 128 =
      1184208804442876783333841 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114048 : ∀ i : Fin 128,
    levelEleven.lookup (114048 + i.val) ≤ levelElevenRoots.lookup (114048 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_222 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113664 512 =
      426254269934311157253530126365873 := by
  have h0 := levelEleven_energy_113664
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113664 256 =
      322777362563935195923978080774557 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113664 128 128
      281374711533421578041972073203074 41402651030513617882006007571483 h0 levelEleven_energy_113792
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113664 384 =
      382577802830172186191345074435563 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113664 256 128
      322777362563935195923978080774557 59800440266236990267366993661006 h1 levelEleven_energy_113920
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113664 512 =
      426254269934311157253530126365873 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113664 384 128
      382577802830172186191345074435563 43676467104138971062185051930310 h2 levelEleven_energy_114048
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_222 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 512 =
      6514978142491062957850596 := by
  have h0 := levelEleven_fractional_113664
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 256 =
      3990537174794993424215246 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 128 128
      2889680056628539278932292 1100857118166454145282954 h0 levelEleven_fractional_113792
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 384 =
      5330769338048186174516755 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 256 128
      3990537174794993424215246 1340232163253192750301509 h1 levelEleven_fractional_113920
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 512 =
      6514978142491062957850596 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113664 384 128
      5330769338048186174516755 1184208804442876783333841 h2 levelEleven_fractional_114048
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_222 : ∀ i : Fin 512,
    levelEleven.lookup (113664 + i.val) ≤ levelElevenRoots.lookup (113664 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_113664
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113664 128 128
    h0 levelEleven_squares_113792
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113664 256 128
    h1 levelEleven_squares_113920
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113664 384 128
    h2 levelEleven_squares_114048
  exact h3

end WordCertDensity.Certificates
