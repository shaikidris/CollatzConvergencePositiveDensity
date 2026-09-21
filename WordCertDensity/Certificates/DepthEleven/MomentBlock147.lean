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
theorem levelEleven_energy_75264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75264 128 =
      53373655006284783266154296922784 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 128 =
      1178370029520448989313766 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75264 : ∀ i : Fin 128,
    levelEleven.lookup (75264 + i.val) ≤ levelElevenRoots.lookup (75264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75392 128 =
      52197609593553179879723744988723 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75392 128 =
      1214385516379279407878379 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75392 : ∀ i : Fin 128,
    levelEleven.lookup (75392 + i.val) ≤ levelElevenRoots.lookup (75392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75520 128 =
      17434741443311735391086118280122 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75520 128 =
      683403145999989891013099 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75520 : ∀ i : Fin 128,
    levelEleven.lookup (75520 + i.val) ≤ levelElevenRoots.lookup (75520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75648 128 =
      46801007692330429250517075162295 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75648 128 =
      1225183925772025515977556 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75648 : ∀ i : Fin 128,
    levelEleven.lookup (75648 + i.val) ≤ levelElevenRoots.lookup (75648 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_147 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75264 512 =
      169807013735480127787481235353924 := by
  have h0 := levelEleven_energy_75264
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75264 256 =
      105571264599837963145878041911507 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75264 128 128
      53373655006284783266154296922784 52197609593553179879723744988723 h0 levelEleven_energy_75392
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75264 384 =
      123006006043149698536964160191629 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75264 256 128
      105571264599837963145878041911507 17434741443311735391086118280122 h1 levelEleven_energy_75520
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75264 512 =
      169807013735480127787481235353924 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75264 384 128
      123006006043149698536964160191629 46801007692330429250517075162295 h2 levelEleven_energy_75648
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_147 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 512 =
      4301342617671743804182800 := by
  have h0 := levelEleven_fractional_75264
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 256 =
      2392755545899728397192145 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 128 128
      1178370029520448989313766 1214385516379279407878379 h0 levelEleven_fractional_75392
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 384 =
      3076158691899718288205244 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 256 128
      2392755545899728397192145 683403145999989891013099 h1 levelEleven_fractional_75520
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 512 =
      4301342617671743804182800 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75264 384 128
      3076158691899718288205244 1225183925772025515977556 h2 levelEleven_fractional_75648
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_147 : ∀ i : Fin 512,
    levelEleven.lookup (75264 + i.val) ≤ levelElevenRoots.lookup (75264 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_75264
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75264 128 128
    h0 levelEleven_squares_75392
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75264 256 128
    h1 levelEleven_squares_75520
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75264 384 128
    h2 levelEleven_squares_75648
  exact h3

end WordCertDensity.Certificates
