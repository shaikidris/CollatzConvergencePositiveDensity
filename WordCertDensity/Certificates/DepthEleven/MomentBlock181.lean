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
theorem levelEleven_energy_92672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92672 128 =
      67681461235331620237567232970280 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 128 =
      1519874418422631460531437 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92672 : ∀ i : Fin 128,
    levelEleven.lookup (92672 + i.val) ≤ levelElevenRoots.lookup (92672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92800 128 =
      17747685769919379714228985321923 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92800 128 =
      668784356353242311284947 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92800 : ∀ i : Fin 128,
    levelEleven.lookup (92800 + i.val) ≤ levelElevenRoots.lookup (92800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92928 128 =
      61161343577607977139793840880304 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92928 128 =
      1378771668486305168615105 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92928 : ∀ i : Fin 128,
    levelEleven.lookup (92928 + i.val) ≤ levelElevenRoots.lookup (92928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93056 128 =
      22670707949810081953096650261933 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93056 128 =
      764013950199964504262657 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93056 : ∀ i : Fin 128,
    levelEleven.lookup (93056 + i.val) ≤ levelElevenRoots.lookup (93056 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_181 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92672 512 =
      169261198532669059044686709434440 := by
  have h0 := levelEleven_energy_92672
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92672 256 =
      85429147005250999951796218292203 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92672 128 128
      67681461235331620237567232970280 17747685769919379714228985321923 h0 levelEleven_energy_92800
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92672 384 =
      146590490582858977091590059172507 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92672 256 128
      85429147005250999951796218292203 61161343577607977139793840880304 h1 levelEleven_energy_92928
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92672 512 =
      169261198532669059044686709434440 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92672 384 128
      146590490582858977091590059172507 22670707949810081953096650261933 h2 levelEleven_energy_93056
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_181 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 512 =
      4331444393462143444694146 := by
  have h0 := levelEleven_fractional_92672
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 256 =
      2188658774775873771816384 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 128 128
      1519874418422631460531437 668784356353242311284947 h0 levelEleven_fractional_92800
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 384 =
      3567430443262178940431489 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 256 128
      2188658774775873771816384 1378771668486305168615105 h1 levelEleven_fractional_92928
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 512 =
      4331444393462143444694146 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92672 384 128
      3567430443262178940431489 764013950199964504262657 h2 levelEleven_fractional_93056
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_181 : ∀ i : Fin 512,
    levelEleven.lookup (92672 + i.val) ≤ levelElevenRoots.lookup (92672 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_92672
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92672 128 128
    h0 levelEleven_squares_92800
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92672 256 128
    h1 levelEleven_squares_92928
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92672 384 128
    h2 levelEleven_squares_93056
  exact h3

end WordCertDensity.Certificates
