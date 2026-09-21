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
theorem levelEleven_energy_71680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71680 128 =
      24758641321546550134081239703801 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 128 =
      818398351940006118970923 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71680 : ∀ i : Fin 128,
    levelEleven.lookup (71680 + i.val) ≤ levelElevenRoots.lookup (71680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71808 128 =
      33273603464135538926681063821463 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71808 128 =
      987721834412196198976820 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71808 : ∀ i : Fin 128,
    levelEleven.lookup (71808 + i.val) ≤ levelElevenRoots.lookup (71808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71936 128 =
      65475978317378275631494225484178 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71936 128 =
      1244261982535512554089349 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71936 : ∀ i : Fin 128,
    levelEleven.lookup (71936 + i.val) ≤ levelElevenRoots.lookup (71936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72064 128 =
      89516314089641489716982141365285 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72064 128 =
      1797125881574201478814009 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72064 : ∀ i : Fin 128,
    levelEleven.lookup (72064 + i.val) ≤ levelElevenRoots.lookup (72064 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_140 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71680 512 =
      213024537192701854409238670374727 := by
  have h0 := levelEleven_energy_71680
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71680 256 =
      58032244785682089060762303525264 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71680 128 128
      24758641321546550134081239703801 33273603464135538926681063821463 h0 levelEleven_energy_71808
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71680 384 =
      123508223103060364692256529009442 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71680 256 128
      58032244785682089060762303525264 65475978317378275631494225484178 h1 levelEleven_energy_71936
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71680 512 =
      213024537192701854409238670374727 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71680 384 128
      123508223103060364692256529009442 89516314089641489716982141365285 h2 levelEleven_energy_72064
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_140 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 512 =
      4847508050461916350851101 := by
  have h0 := levelEleven_fractional_71680
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 256 =
      1806120186352202317947743 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 128 128
      818398351940006118970923 987721834412196198976820 h0 levelEleven_fractional_71808
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 384 =
      3050382168887714872037092 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 256 128
      1806120186352202317947743 1244261982535512554089349 h1 levelEleven_fractional_71936
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 512 =
      4847508050461916350851101 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71680 384 128
      3050382168887714872037092 1797125881574201478814009 h2 levelEleven_fractional_72064
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_140 : ∀ i : Fin 512,
    levelEleven.lookup (71680 + i.val) ≤ levelElevenRoots.lookup (71680 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_71680
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71680 128 128
    h0 levelEleven_squares_71808
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71680 256 128
    h1 levelEleven_squares_71936
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71680 384 128
    h2 levelEleven_squares_72064
  exact h3

end WordCertDensity.Certificates
