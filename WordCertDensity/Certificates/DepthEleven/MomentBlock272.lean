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
theorem levelEleven_energy_139264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139264 128 =
      23060345672834169613016152135098 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 128 =
      730053162047993377655373 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139264 : ∀ i : Fin 128,
    levelEleven.lookup (139264 + i.val) ≤ levelElevenRoots.lookup (139264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139392 128 =
      112007532546766165213719223495190 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139392 128 =
      1857831221848838810931792 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139392 : ∀ i : Fin 128,
    levelEleven.lookup (139392 + i.val) ≤ levelElevenRoots.lookup (139392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139520 128 =
      40685174882748158873614002074247 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139520 128 =
      1122113618056865689557379 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139520 : ∀ i : Fin 128,
    levelEleven.lookup (139520 + i.val) ≤ levelElevenRoots.lookup (139520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139648 128 =
      26031115103399331125842993154211 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139648 128 =
      819670281302917016481803 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139648 : ∀ i : Fin 128,
    levelEleven.lookup (139648 + i.val) ≤ levelElevenRoots.lookup (139648 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139264 512 =
      201784168205747824826192370858746 := by
  have h0 := levelEleven_energy_139264
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139264 256 =
      135067878219600334826735375630288 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139264 128 128
      23060345672834169613016152135098 112007532546766165213719223495190 h0 levelEleven_energy_139392
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139264 384 =
      175753053102348493700349377704535 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139264 256 128
      135067878219600334826735375630288 40685174882748158873614002074247 h1 levelEleven_energy_139520
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139264 512 =
      201784168205747824826192370858746 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139264 384 128
      175753053102348493700349377704535 26031115103399331125842993154211 h2 levelEleven_energy_139648
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 512 =
      4529668283256614894626347 := by
  have h0 := levelEleven_fractional_139264
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 256 =
      2587884383896832188587165 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 128 128
      730053162047993377655373 1857831221848838810931792 h0 levelEleven_fractional_139392
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 384 =
      3709998001953697878144544 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 256 128
      2587884383896832188587165 1122113618056865689557379 h1 levelEleven_fractional_139520
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 512 =
      4529668283256614894626347 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139264 384 128
      3709998001953697878144544 819670281302917016481803 h2 levelEleven_fractional_139648
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_272 : ∀ i : Fin 512,
    levelEleven.lookup (139264 + i.val) ≤ levelElevenRoots.lookup (139264 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_139264
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139264 128 128
    h0 levelEleven_squares_139392
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139264 256 128
    h1 levelEleven_squares_139520
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139264 384 128
    h2 levelEleven_squares_139648
  exact h3

end WordCertDensity.Certificates
