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
theorem levelEleven_energy_36864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36864 128 =
      39776826892330979877579153746812 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 128 =
      1070866152719089879317796 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36864 : ∀ i : Fin 128,
    levelEleven.lookup (36864 + i.val) ≤ levelElevenRoots.lookup (36864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36992 128 =
      88172263277515793763141325586701 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36992 128 =
      1622338116098890153144487 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36992 : ∀ i : Fin 128,
    levelEleven.lookup (36992 + i.val) ≤ levelElevenRoots.lookup (36992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_37120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37120 128 =
      27584221284548153297980935851809 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37120 128 =
      817357070739081996790916 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37120 : ∀ i : Fin 128,
    levelEleven.lookup (37120 + i.val) ≤ levelElevenRoots.lookup (37120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_37248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37248 128 =
      55289815454640958402384900492601 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37248 128 =
      1352655557256917300539984 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37248 : ∀ i : Fin 128,
    levelEleven.lookup (37248 + i.val) ≤ levelElevenRoots.lookup (37248 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_72 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36864 512 =
      210823126909035885341086315677923 := by
  have h0 := levelEleven_energy_36864
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36864 256 =
      127949090169846773640720479333513 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36864 128 128
      39776826892330979877579153746812 88172263277515793763141325586701 h0 levelEleven_energy_36992
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36864 384 =
      155533311454394926938701415185322 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36864 256 128
      127949090169846773640720479333513 27584221284548153297980935851809 h1 levelEleven_energy_37120
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36864 512 =
      210823126909035885341086315677923 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36864 384 128
      155533311454394926938701415185322 55289815454640958402384900492601 h2 levelEleven_energy_37248
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_72 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 512 =
      4863216896813979329793183 := by
  have h0 := levelEleven_fractional_36864
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 256 =
      2693204268817980032462283 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 128 128
      1070866152719089879317796 1622338116098890153144487 h0 levelEleven_fractional_36992
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 384 =
      3510561339557062029253199 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 256 128
      2693204268817980032462283 817357070739081996790916 h1 levelEleven_fractional_37120
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 512 =
      4863216896813979329793183 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36864 384 128
      3510561339557062029253199 1352655557256917300539984 h2 levelEleven_fractional_37248
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_72 : ∀ i : Fin 512,
    levelEleven.lookup (36864 + i.val) ≤ levelElevenRoots.lookup (36864 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_36864
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36864 128 128
    h0 levelEleven_squares_36992
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36864 256 128
    h1 levelEleven_squares_37120
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36864 384 128
    h2 levelEleven_squares_37248
  exact h3

end WordCertDensity.Certificates
