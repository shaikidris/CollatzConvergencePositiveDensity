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
theorem levelEleven_energy_109056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109056 128 =
      32253215932128380004786166644913 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 128 =
      935074572481479312314943 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109056 : ∀ i : Fin 128,
    levelEleven.lookup (109056 + i.val) ≤ levelElevenRoots.lookup (109056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109184 128 =
      53970376947352728036933728629325 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109184 128 =
      1292425911836984758622305 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109184 : ∀ i : Fin 128,
    levelEleven.lookup (109184 + i.val) ≤ levelElevenRoots.lookup (109184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109312 128 =
      33985107467150858306613666053731 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109312 128 =
      910663952669093230900693 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109312 : ∀ i : Fin 128,
    levelEleven.lookup (109312 + i.val) ≤ levelElevenRoots.lookup (109312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109440 128 =
      70525617778109426205469297414907 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109440 128 =
      1558836487396217375954425 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109440 : ∀ i : Fin 128,
    levelEleven.lookup (109440 + i.val) ≤ levelElevenRoots.lookup (109440 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_213 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109056 512 =
      190734318124741392553802858742876 := by
  have h0 := levelEleven_energy_109056
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109056 256 =
      86223592879481108041719895274238 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109056 128 128
      32253215932128380004786166644913 53970376947352728036933728629325 h0 levelEleven_energy_109184
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109056 384 =
      120208700346631966348333561327969 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109056 256 128
      86223592879481108041719895274238 33985107467150858306613666053731 h1 levelEleven_energy_109312
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109056 512 =
      190734318124741392553802858742876 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109056 384 128
      120208700346631966348333561327969 70525617778109426205469297414907 h2 levelEleven_energy_109440
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_213 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 512 =
      4697000924383774677792366 := by
  have h0 := levelEleven_fractional_109056
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 256 =
      2227500484318464070937248 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 128 128
      935074572481479312314943 1292425911836984758622305 h0 levelEleven_fractional_109184
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 384 =
      3138164436987557301837941 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 256 128
      2227500484318464070937248 910663952669093230900693 h1 levelEleven_fractional_109312
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 512 =
      4697000924383774677792366 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109056 384 128
      3138164436987557301837941 1558836487396217375954425 h2 levelEleven_fractional_109440
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_213 : ∀ i : Fin 512,
    levelEleven.lookup (109056 + i.val) ≤ levelElevenRoots.lookup (109056 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_109056
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109056 128 128
    h0 levelEleven_squares_109184
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109056 256 128
    h1 levelEleven_squares_109312
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109056 384 128
    h2 levelEleven_squares_109440
  exact h3

end WordCertDensity.Certificates
