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
theorem levelEleven_energy_56832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56832 128 =
      19414582233739590950212053916893 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 128 =
      655991855945255528151995 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56832 : ∀ i : Fin 128,
    levelEleven.lookup (56832 + i.val) ≤ levelElevenRoots.lookup (56832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56960 128 =
      33106186762619691983456022251942 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56960 128 =
      1008733912027364454579355 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56960 : ∀ i : Fin 128,
    levelEleven.lookup (56960 + i.val) ≤ levelElevenRoots.lookup (56960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57088 128 =
      48937039798616483285390337558691 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57088 128 =
      1241677625670757692934717 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57088 : ∀ i : Fin 128,
    levelEleven.lookup (57088 + i.val) ≤ levelElevenRoots.lookup (57088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57216 128 =
      57469508086688024443207661630495 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57216 128 =
      1380625500239253459138616 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57216 : ∀ i : Fin 128,
    levelEleven.lookup (57216 + i.val) ≤ levelElevenRoots.lookup (57216 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_111 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56832 512 =
      158927316881663790662266075358021 := by
  have h0 := levelEleven_energy_56832
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56832 256 =
      52520768996359282933668076168835 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56832 128 128
      19414582233739590950212053916893 33106186762619691983456022251942 h0 levelEleven_energy_56960
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56832 384 =
      101457808794975766219058413727526 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56832 256 128
      52520768996359282933668076168835 48937039798616483285390337558691 h1 levelEleven_energy_57088
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 56832 512 =
      158927316881663790662266075358021 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 56832 384 128
      101457808794975766219058413727526 57469508086688024443207661630495 h2 levelEleven_energy_57216
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_111 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 512 =
      4287028893882631134804683 := by
  have h0 := levelEleven_fractional_56832
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 256 =
      1664725767972619982731350 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 128 128
      655991855945255528151995 1008733912027364454579355 h0 levelEleven_fractional_56960
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 384 =
      2906403393643377675666067 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 256 128
      1664725767972619982731350 1241677625670757692934717 h1 levelEleven_fractional_57088
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 512 =
      4287028893882631134804683 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56832 384 128
      2906403393643377675666067 1380625500239253459138616 h2 levelEleven_fractional_57216
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_111 : ∀ i : Fin 512,
    levelEleven.lookup (56832 + i.val) ≤ levelElevenRoots.lookup (56832 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_56832
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56832 128 128
    h0 levelEleven_squares_56960
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56832 256 128
    h1 levelEleven_squares_57088
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 56832 384 128
    h2 levelEleven_squares_57216
  exact h3

end WordCertDensity.Certificates
