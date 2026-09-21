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
theorem levelEleven_energy_120832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120832 128 =
      42586580222872682071269695305356 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 128 =
      1132571883139387643937356 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120832 : ∀ i : Fin 128,
    levelEleven.lookup (120832 + i.val) ≤ levelElevenRoots.lookup (120832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120960 128 =
      27099007063539829630167448519589 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120960 128 =
      789576137387789476640493 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120960 : ∀ i : Fin 128,
    levelEleven.lookup (120960 + i.val) ≤ levelElevenRoots.lookup (120960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121088 128 =
      69473871116913792296515962633753 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121088 128 =
      1349477399422353446022650 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121088 : ∀ i : Fin 128,
    levelEleven.lookup (121088 + i.val) ≤ levelElevenRoots.lookup (121088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121216 128 =
      63501635243865320880484499084105 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121216 128 =
      1336770917268186921086791 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121216 : ∀ i : Fin 128,
    levelEleven.lookup (121216 + i.val) ≤ levelElevenRoots.lookup (121216 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_236 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120832 512 =
      202661093647191624878437605542803 := by
  have h0 := levelEleven_energy_120832
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120832 256 =
      69685587286412511701437143824945 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120832 128 128
      42586580222872682071269695305356 27099007063539829630167448519589 h0 levelEleven_energy_120960
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120832 384 =
      139159458403326303997953106458698 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120832 256 128
      69685587286412511701437143824945 69473871116913792296515962633753 h1 levelEleven_energy_121088
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120832 512 =
      202661093647191624878437605542803 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120832 384 128
      139159458403326303997953106458698 63501635243865320880484499084105 h2 levelEleven_energy_121216
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_236 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 512 =
      4608396337217717487687290 := by
  have h0 := levelEleven_fractional_120832
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 256 =
      1922148020527177120577849 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 128 128
      1132571883139387643937356 789576137387789476640493 h0 levelEleven_fractional_120960
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 384 =
      3271625419949530566600499 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 256 128
      1922148020527177120577849 1349477399422353446022650 h1 levelEleven_fractional_121088
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 512 =
      4608396337217717487687290 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120832 384 128
      3271625419949530566600499 1336770917268186921086791 h2 levelEleven_fractional_121216
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_236 : ∀ i : Fin 512,
    levelEleven.lookup (120832 + i.val) ≤ levelElevenRoots.lookup (120832 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_120832
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120832 128 128
    h0 levelEleven_squares_120960
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120832 256 128
    h1 levelEleven_squares_121088
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120832 384 128
    h2 levelEleven_squares_121216
  exact h3

end WordCertDensity.Certificates
