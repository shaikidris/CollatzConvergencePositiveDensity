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
theorem levelEleven_energy_96256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96256 128 =
      30729640246183890749993611518257 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 128 =
      884508775688392419424956 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96256 : ∀ i : Fin 128,
    levelEleven.lookup (96256 + i.val) ≤ levelElevenRoots.lookup (96256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96384 128 =
      37575652984427384097106679768450 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96384 128 =
      1051495616437919622940874 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96384 : ∀ i : Fin 128,
    levelEleven.lookup (96384 + i.val) ≤ levelElevenRoots.lookup (96384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96512 128 =
      86646211630389280949514798859631 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96512 128 =
      1570909351295568780272859 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96512 : ∀ i : Fin 128,
    levelEleven.lookup (96512 + i.val) ≤ levelElevenRoots.lookup (96512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96640 128 =
      71625592686201950609215218866443 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96640 128 =
      1343201599110407171445523 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96640 : ∀ i : Fin 128,
    levelEleven.lookup (96640 + i.val) ≤ levelElevenRoots.lookup (96640 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_188 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96256 512 =
      226577097547202506405830309012781 := by
  have h0 := levelEleven_energy_96256
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96256 256 =
      68305293230611274847100291286707 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96256 128 128
      30729640246183890749993611518257 37575652984427384097106679768450 h0 levelEleven_energy_96384
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96256 384 =
      154951504861000555796615090146338 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96256 256 128
      68305293230611274847100291286707 86646211630389280949514798859631 h1 levelEleven_energy_96512
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96256 512 =
      226577097547202506405830309012781 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96256 384 128
      154951504861000555796615090146338 71625592686201950609215218866443 h2 levelEleven_energy_96640
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_188 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 512 =
      4850115342532287994084212 := by
  have h0 := levelEleven_fractional_96256
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 256 =
      1936004392126312042365830 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 128 128
      884508775688392419424956 1051495616437919622940874 h0 levelEleven_fractional_96384
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 384 =
      3506913743421880822638689 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 256 128
      1936004392126312042365830 1570909351295568780272859 h1 levelEleven_fractional_96512
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 512 =
      4850115342532287994084212 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96256 384 128
      3506913743421880822638689 1343201599110407171445523 h2 levelEleven_fractional_96640
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_188 : ∀ i : Fin 512,
    levelEleven.lookup (96256 + i.val) ≤ levelElevenRoots.lookup (96256 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_96256
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96256 128 128
    h0 levelEleven_squares_96384
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96256 256 128
    h1 levelEleven_squares_96512
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96256 384 128
    h2 levelEleven_squares_96640
  exact h3

end WordCertDensity.Certificates
