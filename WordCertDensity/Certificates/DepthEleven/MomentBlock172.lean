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
theorem levelEleven_energy_88064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88064 128 =
      31424335177598505111052420079413 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 128 =
      924770489907276990559580 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88064 : ∀ i : Fin 128,
    levelEleven.lookup (88064 + i.val) ≤ levelElevenRoots.lookup (88064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88192 128 =
      35063134951928515071346158186402 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88192 128 =
      937595861803487431356578 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88192 : ∀ i : Fin 128,
    levelEleven.lookup (88192 + i.val) ≤ levelElevenRoots.lookup (88192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88320 128 =
      94535533744464746646799581498868 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88320 128 =
      1549246870453821547667995 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88320 : ∀ i : Fin 128,
    levelEleven.lookup (88320 + i.val) ≤ levelElevenRoots.lookup (88320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88448 128 =
      397198711662779118168343659456472 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88448 128 =
      4002461197257173240764101 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88448 : ∀ i : Fin 128,
    levelEleven.lookup (88448 + i.val) ≤ levelElevenRoots.lookup (88448 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_172 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88064 512 =
      558221715536770884997541819221155 := by
  have h0 := levelEleven_energy_88064
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88064 256 =
      66487470129527020182398578265815 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88064 128 128
      31424335177598505111052420079413 35063134951928515071346158186402 h0 levelEleven_energy_88192
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88064 384 =
      161023003873991766829198159764683 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88064 256 128
      66487470129527020182398578265815 94535533744464746646799581498868 h1 levelEleven_energy_88320
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88064 512 =
      558221715536770884997541819221155 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88064 384 128
      161023003873991766829198159764683 397198711662779118168343659456472 h2 levelEleven_energy_88448
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_172 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 512 =
      7414074419421759210348254 := by
  have h0 := levelEleven_fractional_88064
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 256 =
      1862366351710764421916158 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 128 128
      924770489907276990559580 937595861803487431356578 h0 levelEleven_fractional_88192
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 384 =
      3411613222164585969584153 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 256 128
      1862366351710764421916158 1549246870453821547667995 h1 levelEleven_fractional_88320
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 512 =
      7414074419421759210348254 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88064 384 128
      3411613222164585969584153 4002461197257173240764101 h2 levelEleven_fractional_88448
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_172 : ∀ i : Fin 512,
    levelEleven.lookup (88064 + i.val) ≤ levelElevenRoots.lookup (88064 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_88064
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88064 128 128
    h0 levelEleven_squares_88192
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88064 256 128
    h1 levelEleven_squares_88320
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88064 384 128
    h2 levelEleven_squares_88448
  exact h3

end WordCertDensity.Certificates
