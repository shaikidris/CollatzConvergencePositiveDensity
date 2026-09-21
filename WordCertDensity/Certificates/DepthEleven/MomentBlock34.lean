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
theorem levelEleven_energy_17408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17408 128 =
      45675063400982428360425519480182 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 128 =
      1150505997402002636585037 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17408 : ∀ i : Fin 128,
    levelEleven.lookup (17408 + i.val) ≤ levelElevenRoots.lookup (17408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17536 128 =
      39590396615275476958474267128617 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17536 128 =
      1022439465355321630166547 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17536 : ∀ i : Fin 128,
    levelEleven.lookup (17536 + i.val) ≤ levelElevenRoots.lookup (17536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17664 128 =
      96833839876874783292991802023499 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17664 128 =
      1591161359712813609255355 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17664 : ∀ i : Fin 128,
    levelEleven.lookup (17664 + i.val) ≤ levelElevenRoots.lookup (17664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_17792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17792 128 =
      60727608714496529152894440536558 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17792 128 =
      1393917942754051412590780 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17792 : ∀ i : Fin 128,
    levelEleven.lookup (17792 + i.val) ≤ levelElevenRoots.lookup (17792 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_34 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17408 512 =
      242826908607629217764786029168856 := by
  have h0 := levelEleven_energy_17408
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17408 256 =
      85265460016257905318899786608799 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17408 128 128
      45675063400982428360425519480182 39590396615275476958474267128617 h0 levelEleven_energy_17536
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17408 384 =
      182099299893132688611891588632298 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17408 256 128
      85265460016257905318899786608799 96833839876874783292991802023499 h1 levelEleven_energy_17664
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17408 512 =
      242826908607629217764786029168856 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17408 384 128
      182099299893132688611891588632298 60727608714496529152894440536558 h2 levelEleven_energy_17792
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_34 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 512 =
      5158024765224189288597719 := by
  have h0 := levelEleven_fractional_17408
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 256 =
      2172945462757324266751584 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 128 128
      1150505997402002636585037 1022439465355321630166547 h0 levelEleven_fractional_17536
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 384 =
      3764106822470137876006939 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 256 128
      2172945462757324266751584 1591161359712813609255355 h1 levelEleven_fractional_17664
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 512 =
      5158024765224189288597719 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17408 384 128
      3764106822470137876006939 1393917942754051412590780 h2 levelEleven_fractional_17792
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_34 : ∀ i : Fin 512,
    levelEleven.lookup (17408 + i.val) ≤ levelElevenRoots.lookup (17408 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_17408
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17408 128 128
    h0 levelEleven_squares_17536
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17408 256 128
    h1 levelEleven_squares_17664
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17408 384 128
    h2 levelEleven_squares_17792
  exact h3

end WordCertDensity.Certificates
