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
theorem levelEleven_energy_58880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58880 128 =
      110695023511967359621113595658641 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 128 =
      1913855295401850452795714 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58880 : ∀ i : Fin 128,
    levelEleven.lookup (58880 + i.val) ≤ levelElevenRoots.lookup (58880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59008 128 =
      113642211469691131310252651718411 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59008 128 =
      1704306169999497886151280 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59008 : ∀ i : Fin 128,
    levelEleven.lookup (59008 + i.val) ≤ levelElevenRoots.lookup (59008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59136 128 =
      97140565485633043269100994038417 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59136 128 =
      1815578832813469433671849 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59136 : ∀ i : Fin 128,
    levelEleven.lookup (59136 + i.val) ≤ levelElevenRoots.lookup (59136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59264 128 =
      51733898948753172715486180709378 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59264 128 =
      1240266685455299603744682 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59264 : ∀ i : Fin 128,
    levelEleven.lookup (59264 + i.val) ≤ levelElevenRoots.lookup (59264 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_115 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58880 512 =
      373211699416044706915953422124847 := by
  have h0 := levelEleven_energy_58880
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58880 256 =
      224337234981658490931366247377052 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58880 128 128
      110695023511967359621113595658641 113642211469691131310252651718411 h0 levelEleven_energy_59008
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58880 384 =
      321477800467291534200467241415469 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58880 256 128
      224337234981658490931366247377052 97140565485633043269100994038417 h1 levelEleven_energy_59136
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 58880 512 =
      373211699416044706915953422124847 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 58880 384 128
      321477800467291534200467241415469 51733898948753172715486180709378 h2 levelEleven_energy_59264
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_115 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 512 =
      6674006983670117376363525 := by
  have h0 := levelEleven_fractional_58880
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 256 =
      3618161465401348338946994 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 128 128
      1913855295401850452795714 1704306169999497886151280 h0 levelEleven_fractional_59008
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 384 =
      5433740298214817772618843 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 256 128
      3618161465401348338946994 1815578832813469433671849 h1 levelEleven_fractional_59136
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 512 =
      6674006983670117376363525 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58880 384 128
      5433740298214817772618843 1240266685455299603744682 h2 levelEleven_fractional_59264
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_115 : ∀ i : Fin 512,
    levelEleven.lookup (58880 + i.val) ≤ levelElevenRoots.lookup (58880 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_58880
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58880 128 128
    h0 levelEleven_squares_59008
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58880 256 128
    h1 levelEleven_squares_59136
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 58880 384 128
    h2 levelEleven_squares_59264
  exact h3

end WordCertDensity.Certificates
