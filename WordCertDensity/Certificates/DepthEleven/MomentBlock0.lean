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
theorem levelEleven_energy_0 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 0 128 =
      14812324565542389626228083698654 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_0 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 128 =
      556815136438997354940371 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_0 : ∀ i : Fin 128,
    levelEleven.lookup (0 + i.val) ≤ levelElevenRoots.lookup (0 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128 128 =
      96363102340818933067111895393401 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128 128 =
      1949129827538279852293777 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128 : ∀ i : Fin 128,
    levelEleven.lookup (128 + i.val) ≤ levelElevenRoots.lookup (128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 256 128 =
      96001288283307257188791639277408 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 256 128 =
      1766135497083149635029223 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_256 : ∀ i : Fin 128,
    levelEleven.lookup (256 + i.val) ≤ levelElevenRoots.lookup (256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 384 128 =
      57229586901505339447403666149207 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 384 128 =
      1364381417977080199093686 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_384 : ∀ i : Fin 128,
    levelEleven.lookup (384 + i.val) ≤ levelElevenRoots.lookup (384 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_0 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 0 512 =
      264406302091173919329535284518670 := by
  have h0 := levelEleven_energy_0
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 0 256 =
      111175426906361322693339979092055 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 0 128 128
      14812324565542389626228083698654 96363102340818933067111895393401 h0 levelEleven_energy_128
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 0 384 =
      207176715189668579882131618369463 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 0 256 128
      111175426906361322693339979092055 96001288283307257188791639277408 h1 levelEleven_energy_256
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 0 512 =
      264406302091173919329535284518670 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 0 384 128
      207176715189668579882131618369463 57229586901505339447403666149207 h2 levelEleven_energy_384
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_0 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 512 =
      5636461879037507041357057 := by
  have h0 := levelEleven_fractional_0
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 256 =
      2505944963977277207234148 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 128 128
      556815136438997354940371 1949129827538279852293777 h0 levelEleven_fractional_128
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 384 =
      4272080461060426842263371 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 256 128
      2505944963977277207234148 1766135497083149635029223 h1 levelEleven_fractional_256
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 512 =
      5636461879037507041357057 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 0 384 128
      4272080461060426842263371 1364381417977080199093686 h2 levelEleven_fractional_384
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_0 : ∀ i : Fin 512,
    levelEleven.lookup (0 + i.val) ≤ levelElevenRoots.lookup (0 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_0
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 0 128 128
    h0 levelEleven_squares_128
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 0 256 128
    h1 levelEleven_squares_256
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 0 384 128
    h2 levelEleven_squares_384
  exact h3

end WordCertDensity.Certificates
