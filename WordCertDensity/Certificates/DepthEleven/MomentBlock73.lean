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
theorem levelEleven_energy_37376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37376 128 =
      53109287679805774754794930158815 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 128 =
      1219774197968491787997187 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37376 : ∀ i : Fin 128,
    levelEleven.lookup (37376 + i.val) ≤ levelElevenRoots.lookup (37376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_37504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37504 128 =
      62324694339091604612778479576323 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37504 128 =
      1500709032880682805238269 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37504 : ∀ i : Fin 128,
    levelEleven.lookup (37504 + i.val) ≤ levelElevenRoots.lookup (37504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_37632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37632 128 =
      30010205483954722149616071156044 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37632 128 =
      840533970174916802708403 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37632 : ∀ i : Fin 128,
    levelEleven.lookup (37632 + i.val) ≤ levelElevenRoots.lookup (37632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_37760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37760 128 =
      39822090945327553822143005290787 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37760 128 =
      1075651727829794763681098 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37760 : ∀ i : Fin 128,
    levelEleven.lookup (37760 + i.val) ≤ levelElevenRoots.lookup (37760 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_73 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37376 512 =
      185266278448179655339332486181969 := by
  have h0 := levelEleven_energy_37376
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37376 256 =
      115433982018897379367573409735138 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37376 128 128
      53109287679805774754794930158815 62324694339091604612778479576323 h0 levelEleven_energy_37504
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37376 384 =
      145444187502852101517189480891182 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37376 256 128
      115433982018897379367573409735138 30010205483954722149616071156044 h1 levelEleven_energy_37632
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37376 512 =
      185266278448179655339332486181969 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37376 384 128
      145444187502852101517189480891182 39822090945327553822143005290787 h2 levelEleven_energy_37760
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_73 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 512 =
      4636668928853886159624957 := by
  have h0 := levelEleven_fractional_37376
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 256 =
      2720483230849174593235456 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 128 128
      1219774197968491787997187 1500709032880682805238269 h0 levelEleven_fractional_37504
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 384 =
      3561017201024091395943859 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 256 128
      2720483230849174593235456 840533970174916802708403 h1 levelEleven_fractional_37632
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 512 =
      4636668928853886159624957 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37376 384 128
      3561017201024091395943859 1075651727829794763681098 h2 levelEleven_fractional_37760
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_73 : ∀ i : Fin 512,
    levelEleven.lookup (37376 + i.val) ≤ levelElevenRoots.lookup (37376 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_37376
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37376 128 128
    h0 levelEleven_squares_37504
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37376 256 128
    h1 levelEleven_squares_37632
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37376 384 128
    h2 levelEleven_squares_37760
  exact h3

end WordCertDensity.Certificates
