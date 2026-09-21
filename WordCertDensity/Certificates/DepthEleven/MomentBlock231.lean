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
theorem levelEleven_energy_118272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118272 128 =
      107594408901385305217591484881917 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 128 =
      1897638317987050587639848 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118272 : ∀ i : Fin 128,
    levelEleven.lookup (118272 + i.val) ≤ levelElevenRoots.lookup (118272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118400 128 =
      53435955804092143534232027762517 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118400 128 =
      1362559091129986326511897 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118400 : ∀ i : Fin 128,
    levelEleven.lookup (118400 + i.val) ≤ levelElevenRoots.lookup (118400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118528 128 =
      24497150903903301057562635184346 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118528 128 =
      803003982874164315837268 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118528 : ∀ i : Fin 128,
    levelEleven.lookup (118528 + i.val) ≤ levelElevenRoots.lookup (118528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_118656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118656 128 =
      108700437396240350674208944115596 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_118656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118656 128 =
      1876763688610223953581041 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_118656 : ∀ i : Fin 128,
    levelEleven.lookup (118656 + i.val) ≤ levelElevenRoots.lookup (118656 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_231 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 118272 512 =
      294227953005621100483595091944376 := by
  have h0 := levelEleven_energy_118272
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118272 256 =
      161030364705477448751823512644434 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118272 128 128
      107594408901385305217591484881917 53435955804092143534232027762517 h0 levelEleven_energy_118400
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118272 384 =
      185527515609380749809386147828780 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118272 256 128
      161030364705477448751823512644434 24497150903903301057562635184346 h1 levelEleven_energy_118528
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 118272 512 =
      294227953005621100483595091944376 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 118272 384 128
      185527515609380749809386147828780 108700437396240350674208944115596 h2 levelEleven_energy_118656
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_231 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 512 =
      5939965080601425183570054 := by
  have h0 := levelEleven_fractional_118272
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 256 =
      3260197409117036914151745 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 128 128
      1897638317987050587639848 1362559091129986326511897 h0 levelEleven_fractional_118400
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 384 =
      4063201391991201229989013 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 256 128
      3260197409117036914151745 803003982874164315837268 h1 levelEleven_fractional_118528
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 512 =
      5939965080601425183570054 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 118272 384 128
      4063201391991201229989013 1876763688610223953581041 h2 levelEleven_fractional_118656
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_231 : ∀ i : Fin 512,
    levelEleven.lookup (118272 + i.val) ≤ levelElevenRoots.lookup (118272 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_118272
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118272 128 128
    h0 levelEleven_squares_118400
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118272 256 128
    h1 levelEleven_squares_118528
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 118272 384 128
    h2 levelEleven_squares_118656
  exact h3

end WordCertDensity.Certificates
