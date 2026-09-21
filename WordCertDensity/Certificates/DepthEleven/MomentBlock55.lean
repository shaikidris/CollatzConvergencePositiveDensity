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
theorem levelEleven_energy_28160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28160 128 =
      45790268001944854920801046155161 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 128 =
      1090792540927804996842395 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28160 : ∀ i : Fin 128,
    levelEleven.lookup (28160 + i.val) ≤ levelElevenRoots.lookup (28160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28288 128 =
      281679042320245731323157844568331 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28288 128 =
      3173162680193003879103428 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28288 : ∀ i : Fin 128,
    levelEleven.lookup (28288 + i.val) ≤ levelElevenRoots.lookup (28288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28416 128 =
      40089933148637986556917744608588 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28416 128 =
      939868461429430513408246 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28416 : ∀ i : Fin 128,
    levelEleven.lookup (28416 + i.val) ≤ levelElevenRoots.lookup (28416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28544 128 =
      52842758337983078392373642590372 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28544 128 =
      1283563595027897483883726 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28544 : ∀ i : Fin 128,
    levelEleven.lookup (28544 + i.val) ≤ levelElevenRoots.lookup (28544 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_55 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28160 512 =
      420402001808811651193250277922452 := by
  have h0 := levelEleven_energy_28160
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28160 256 =
      327469310322190586243958890723492 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28160 128 128
      45790268001944854920801046155161 281679042320245731323157844568331 h0 levelEleven_energy_28288
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28160 384 =
      367559243470828572800876635332080 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28160 256 128
      327469310322190586243958890723492 40089933148637986556917744608588 h1 levelEleven_energy_28416
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28160 512 =
      420402001808811651193250277922452 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28160 384 128
      367559243470828572800876635332080 52842758337983078392373642590372 h2 levelEleven_energy_28544
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_55 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 512 =
      6487387277578136873237795 := by
  have h0 := levelEleven_fractional_28160
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 256 =
      4263955221120808875945823 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 128 128
      1090792540927804996842395 3173162680193003879103428 h0 levelEleven_fractional_28288
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 384 =
      5203823682550239389354069 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 256 128
      4263955221120808875945823 939868461429430513408246 h1 levelEleven_fractional_28416
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 512 =
      6487387277578136873237795 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28160 384 128
      5203823682550239389354069 1283563595027897483883726 h2 levelEleven_fractional_28544
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_55 : ∀ i : Fin 512,
    levelEleven.lookup (28160 + i.val) ≤ levelElevenRoots.lookup (28160 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_28160
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28160 128 128
    h0 levelEleven_squares_28288
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28160 256 128
    h1 levelEleven_squares_28416
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28160 384 128
    h2 levelEleven_squares_28544
  exact h3

end WordCertDensity.Certificates
