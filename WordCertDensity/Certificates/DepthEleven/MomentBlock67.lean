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
theorem levelEleven_energy_34304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34304 128 =
      41251580888841485792046909313164 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 128 =
      1065629855926724686740400 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34304 : ∀ i : Fin 128,
    levelEleven.lookup (34304 + i.val) ≤ levelElevenRoots.lookup (34304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34432 128 =
      81906107159994765069981744070337 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34432 128 =
      1529110726000467893726316 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34432 : ∀ i : Fin 128,
    levelEleven.lookup (34432 + i.val) ≤ levelElevenRoots.lookup (34432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34560 128 =
      92762332733477978095074766717499 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34560 128 =
      1736175948336156083083587 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34560 : ∀ i : Fin 128,
    levelEleven.lookup (34560 + i.val) ≤ levelElevenRoots.lookup (34560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34688 128 =
      29417898118675944019330139296053 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34688 128 =
      893971672961635180652812 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34688 : ∀ i : Fin 128,
    levelEleven.lookup (34688 + i.val) ≤ levelElevenRoots.lookup (34688 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_67 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34304 512 =
      245337918900990172976433559397053 := by
  have h0 := levelEleven_energy_34304
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34304 256 =
      123157688048836250862028653383501 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34304 128 128
      41251580888841485792046909313164 81906107159994765069981744070337 h0 levelEleven_energy_34432
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34304 384 =
      215920020782314228957103420101000 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34304 256 128
      123157688048836250862028653383501 92762332733477978095074766717499 h1 levelEleven_energy_34560
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34304 512 =
      245337918900990172976433559397053 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34304 384 128
      215920020782314228957103420101000 29417898118675944019330139296053 h2 levelEleven_energy_34688
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_67 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 512 =
      5224888203224983844203115 := by
  have h0 := levelEleven_fractional_34304
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 256 =
      2594740581927192580466716 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 128 128
      1065629855926724686740400 1529110726000467893726316 h0 levelEleven_fractional_34432
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 384 =
      4330916530263348663550303 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 256 128
      2594740581927192580466716 1736175948336156083083587 h1 levelEleven_fractional_34560
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 512 =
      5224888203224983844203115 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34304 384 128
      4330916530263348663550303 893971672961635180652812 h2 levelEleven_fractional_34688
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_67 : ∀ i : Fin 512,
    levelEleven.lookup (34304 + i.val) ≤ levelElevenRoots.lookup (34304 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_34304
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34304 128 128
    h0 levelEleven_squares_34432
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34304 256 128
    h1 levelEleven_squares_34560
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34304 384 128
    h2 levelEleven_squares_34688
  exact h3

end WordCertDensity.Certificates
