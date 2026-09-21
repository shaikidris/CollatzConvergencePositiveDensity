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
theorem levelEleven_energy_15872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15872 128 =
      74661723443366760241922008063189 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 128 =
      1543113064053150339604959 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15872 : ∀ i : Fin 128,
    levelEleven.lookup (15872 + i.val) ≤ levelElevenRoots.lookup (15872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16000 128 =
      28680671923494586945455017653985 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16000 128 =
      828770029135988774008356 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16000 : ∀ i : Fin 128,
    levelEleven.lookup (16000 + i.val) ≤ levelElevenRoots.lookup (16000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16128 128 =
      42357835105279640012702498711770 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16128 128 =
      1108297301930070820108993 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16128 : ∀ i : Fin 128,
    levelEleven.lookup (16128 + i.val) ≤ levelElevenRoots.lookup (16128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16256 128 =
      45157938958759231110552286015636 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16256 128 =
      1085449109020311978234647 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16256 : ∀ i : Fin 128,
    levelEleven.lookup (16256 + i.val) ≤ levelElevenRoots.lookup (16256 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_31 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15872 512 =
      190858169430900218310631810444580 := by
  have h0 := levelEleven_energy_15872
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15872 256 =
      103342395366861347187377025717174 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15872 128 128
      74661723443366760241922008063189 28680671923494586945455017653985 h0 levelEleven_energy_16000
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15872 384 =
      145700230472140987200079524428944 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15872 256 128
      103342395366861347187377025717174 42357835105279640012702498711770 h1 levelEleven_energy_16128
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15872 512 =
      190858169430900218310631810444580 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15872 384 128
      145700230472140987200079524428944 45157938958759231110552286015636 h2 levelEleven_energy_16256
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_31 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 512 =
      4565629504139521911956955 := by
  have h0 := levelEleven_fractional_15872
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 256 =
      2371883093189139113613315 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 128 128
      1543113064053150339604959 828770029135988774008356 h0 levelEleven_fractional_16000
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 384 =
      3480180395119209933722308 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 256 128
      2371883093189139113613315 1108297301930070820108993 h1 levelEleven_fractional_16128
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 512 =
      4565629504139521911956955 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15872 384 128
      3480180395119209933722308 1085449109020311978234647 h2 levelEleven_fractional_16256
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_31 : ∀ i : Fin 512,
    levelEleven.lookup (15872 + i.val) ≤ levelElevenRoots.lookup (15872 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_15872
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15872 128 128
    h0 levelEleven_squares_16000
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15872 256 128
    h1 levelEleven_squares_16128
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15872 384 128
    h2 levelEleven_squares_16256
  exact h3

end WordCertDensity.Certificates
