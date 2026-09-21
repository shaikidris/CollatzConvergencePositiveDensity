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
theorem levelEleven_energy_64000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64000 128 =
      32003319747830256112803301685447 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 128 =
      973007622054945741400017 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64000 : ∀ i : Fin 128,
    levelEleven.lookup (64000 + i.val) ≤ levelElevenRoots.lookup (64000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64128 128 =
      22180200736572279558179367011940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64128 128 =
      732146509596650579913506 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64128 : ∀ i : Fin 128,
    levelEleven.lookup (64128 + i.val) ≤ levelElevenRoots.lookup (64128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64256 128 =
      31529842040309030166402473149564 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64256 128 =
      940421424501378913723003 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64256 : ∀ i : Fin 128,
    levelEleven.lookup (64256 + i.val) ≤ levelElevenRoots.lookup (64256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64384 128 =
      56772745753216122981199450114793 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64384 128 =
      1322710320005323952362983 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64384 : ∀ i : Fin 128,
    levelEleven.lookup (64384 + i.val) ≤ levelElevenRoots.lookup (64384 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_125 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64000 512 =
      142486108277927688818584591961744 := by
  have h0 := levelEleven_energy_64000
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64000 256 =
      54183520484402535670982668697387 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64000 128 128
      32003319747830256112803301685447 22180200736572279558179367011940 h0 levelEleven_energy_64128
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64000 384 =
      85713362524711565837385141846951 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64000 256 128
      54183520484402535670982668697387 31529842040309030166402473149564 h1 levelEleven_energy_64256
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64000 512 =
      142486108277927688818584591961744 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64000 384 128
      85713362524711565837385141846951 56772745753216122981199450114793 h2 levelEleven_energy_64384
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_125 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 512 =
      3968285876158299187399509 := by
  have h0 := levelEleven_fractional_64000
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 256 =
      1705154131651596321313523 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 128 128
      973007622054945741400017 732146509596650579913506 h0 levelEleven_fractional_64128
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 384 =
      2645575556152975235036526 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 256 128
      1705154131651596321313523 940421424501378913723003 h1 levelEleven_fractional_64256
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 512 =
      3968285876158299187399509 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64000 384 128
      2645575556152975235036526 1322710320005323952362983 h2 levelEleven_fractional_64384
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_125 : ∀ i : Fin 512,
    levelEleven.lookup (64000 + i.val) ≤ levelElevenRoots.lookup (64000 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_64000
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64000 128 128
    h0 levelEleven_squares_64128
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64000 256 128
    h1 levelEleven_squares_64256
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64000 384 128
    h2 levelEleven_squares_64384
  exact h3

end WordCertDensity.Certificates
