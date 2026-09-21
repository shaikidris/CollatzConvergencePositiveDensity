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
theorem levelEleven_energy_155136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155136 128 =
      78313202975121933873616714396875 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 128 =
      1660301847433068916627591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155136 : ∀ i : Fin 128,
    levelEleven.lookup (155136 + i.val) ≤ levelElevenRoots.lookup (155136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155264 128 =
      34199666704071808579016659937987 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155264 128 =
      891941806103116682385811 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155264 : ∀ i : Fin 128,
    levelEleven.lookup (155264 + i.val) ≤ levelElevenRoots.lookup (155264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155392 128 =
      68021361283528831933126092742481 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155392 128 =
      1512006890018625536153745 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155392 : ∀ i : Fin 128,
    levelEleven.lookup (155392 + i.val) ≤ levelElevenRoots.lookup (155392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155520 128 =
      36326135337662656402588286153238 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155520 128 =
      1011252587640297751098246 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155520 : ∀ i : Fin 128,
    levelEleven.lookup (155520 + i.val) ≤ levelElevenRoots.lookup (155520 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_303 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155136 512 =
      216860366300385230788347753230581 := by
  have h0 := levelEleven_energy_155136
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155136 256 =
      112512869679193742452633374334862 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155136 128 128
      78313202975121933873616714396875 34199666704071808579016659937987 h0 levelEleven_energy_155264
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155136 384 =
      180534230962722574385759467077343 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155136 256 128
      112512869679193742452633374334862 68021361283528831933126092742481 h1 levelEleven_energy_155392
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155136 512 =
      216860366300385230788347753230581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155136 384 128
      180534230962722574385759467077343 36326135337662656402588286153238 h2 levelEleven_energy_155520
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_303 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 512 =
      5075503131195108886265393 := by
  have h0 := levelEleven_fractional_155136
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 256 =
      2552243653536185599013402 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 128 128
      1660301847433068916627591 891941806103116682385811 h0 levelEleven_fractional_155264
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 384 =
      4064250543554811135167147 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 256 128
      2552243653536185599013402 1512006890018625536153745 h1 levelEleven_fractional_155392
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 512 =
      5075503131195108886265393 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155136 384 128
      4064250543554811135167147 1011252587640297751098246 h2 levelEleven_fractional_155520
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_303 : ∀ i : Fin 512,
    levelEleven.lookup (155136 + i.val) ≤ levelElevenRoots.lookup (155136 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_155136
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155136 128 128
    h0 levelEleven_squares_155264
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155136 256 128
    h1 levelEleven_squares_155392
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155136 384 128
    h2 levelEleven_squares_155520
  exact h3

end WordCertDensity.Certificates
