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
theorem levelEleven_energy_154112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154112 128 =
      27477583826158229217780565841372 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 128 =
      832172492522607668179788 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154112 : ∀ i : Fin 128,
    levelEleven.lookup (154112 + i.val) ≤ levelElevenRoots.lookup (154112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_154240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154240 128 =
      19657803372139365471211697892887 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154240 128 =
      705937328531117374589417 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154240 : ∀ i : Fin 128,
    levelEleven.lookup (154240 + i.val) ≤ levelElevenRoots.lookup (154240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_154368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154368 128 =
      47821954668770355684306302312352 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154368 128 =
      1231038436197079946396710 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154368 : ∀ i : Fin 128,
    levelEleven.lookup (154368 + i.val) ≤ levelElevenRoots.lookup (154368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_154496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154496 128 =
      269166883081799199720190772289589 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154496 128 =
      2683833154412993907469505 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154496 : ∀ i : Fin 128,
    levelEleven.lookup (154496 + i.val) ≤ levelElevenRoots.lookup (154496 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_301 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154112 512 =
      364124224948867150093489338336200 := by
  have h0 := levelEleven_energy_154112
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154112 256 =
      47135387198297594688992263734259 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154112 128 128
      27477583826158229217780565841372 19657803372139365471211697892887 h0 levelEleven_energy_154240
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154112 384 =
      94957341867067950373298566046611 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154112 256 128
      47135387198297594688992263734259 47821954668770355684306302312352 h1 levelEleven_energy_154368
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154112 512 =
      364124224948867150093489338336200 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154112 384 128
      94957341867067950373298566046611 269166883081799199720190772289589 h2 levelEleven_energy_154496
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_301 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 512 =
      5452981411663798896635420 := by
  have h0 := levelEleven_fractional_154112
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 256 =
      1538109821053725042769205 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 128 128
      832172492522607668179788 705937328531117374589417 h0 levelEleven_fractional_154240
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 384 =
      2769148257250804989165915 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 256 128
      1538109821053725042769205 1231038436197079946396710 h1 levelEleven_fractional_154368
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 512 =
      5452981411663798896635420 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154112 384 128
      2769148257250804989165915 2683833154412993907469505 h2 levelEleven_fractional_154496
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_301 : ∀ i : Fin 512,
    levelEleven.lookup (154112 + i.val) ≤ levelElevenRoots.lookup (154112 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_154112
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154112 128 128
    h0 levelEleven_squares_154240
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154112 256 128
    h1 levelEleven_squares_154368
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154112 384 128
    h2 levelEleven_squares_154496
  exact h3

end WordCertDensity.Certificates
