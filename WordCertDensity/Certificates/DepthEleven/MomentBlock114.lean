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
theorem levelEleven_energy_58368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58368 128 =
      25770522466432089406502790543600 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 128 =
      850378387855626828082207 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58368 : ∀ i : Fin 128,
    levelEleven.lookup (58368 + i.val) ≤ levelElevenRoots.lookup (58368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_58496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58496 128 =
      40566634538964990129286285498349 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58496 128 =
      1057049177809920931487904 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58496 : ∀ i : Fin 128,
    levelEleven.lookup (58496 + i.val) ≤ levelElevenRoots.lookup (58496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_58624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58624 128 =
      33072527186122569924188856599838 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58624 128 =
      990596177965685247708883 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58624 : ∀ i : Fin 128,
    levelEleven.lookup (58624 + i.val) ≤ levelElevenRoots.lookup (58624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_58752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58752 128 =
      31089192627162382246023398149523 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58752 128 =
      860607862353175788155875 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58752 : ∀ i : Fin 128,
    levelEleven.lookup (58752 + i.val) ≤ levelElevenRoots.lookup (58752 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_114 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58368 512 =
      130498876818682031706001330791310 := by
  have h0 := levelEleven_energy_58368
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58368 256 =
      66337157005397079535789076041949 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58368 128 128
      25770522466432089406502790543600 40566634538964990129286285498349 h0 levelEleven_energy_58496
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58368 384 =
      99409684191519649459977932641787 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58368 256 128
      66337157005397079535789076041949 33072527186122569924188856599838 h1 levelEleven_energy_58624
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58368 512 =
      130498876818682031706001330791310 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58368 384 128
      99409684191519649459977932641787 31089192627162382246023398149523 h2 levelEleven_energy_58752
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_114 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 512 =
      3758631605984408795434869 := by
  have h0 := levelEleven_fractional_58368
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 256 =
      1907427565665547759570111 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 128 128
      850378387855626828082207 1057049177809920931487904 h0 levelEleven_fractional_58496
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 384 =
      2898023743631233007278994 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 256 128
      1907427565665547759570111 990596177965685247708883 h1 levelEleven_fractional_58624
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 512 =
      3758631605984408795434869 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58368 384 128
      2898023743631233007278994 860607862353175788155875 h2 levelEleven_fractional_58752
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_114 : ∀ i : Fin 512,
    levelEleven.lookup (58368 + i.val) ≤ levelElevenRoots.lookup (58368 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_58368
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58368 128 128
    h0 levelEleven_squares_58496
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58368 256 128
    h1 levelEleven_squares_58624
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58368 384 128
    h2 levelEleven_squares_58752
  exact h3

end WordCertDensity.Certificates
