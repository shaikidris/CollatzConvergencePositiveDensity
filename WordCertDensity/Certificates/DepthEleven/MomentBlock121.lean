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
theorem levelEleven_energy_61952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61952 128 =
      27888266325366548457456136163026 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 128 =
      845216108272132832158494 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61952 : ∀ i : Fin 128,
    levelEleven.lookup (61952 + i.val) ≤ levelElevenRoots.lookup (61952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62080 128 =
      100161618840157326687692404548419 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62080 128 =
      1787605172022934348423966 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62080 : ∀ i : Fin 128,
    levelEleven.lookup (62080 + i.val) ≤ levelElevenRoots.lookup (62080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62208 128 =
      89897195327748387752608577200025 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62208 128 =
      1607861650319347360094032 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62208 : ∀ i : Fin 128,
    levelEleven.lookup (62208 + i.val) ≤ levelElevenRoots.lookup (62208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62336 128 =
      30678953346745705687026667792580 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62336 128 =
      922258039917271986288896 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62336 : ∀ i : Fin 128,
    levelEleven.lookup (62336 + i.val) ≤ levelElevenRoots.lookup (62336 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_121 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61952 512 =
      248626033840017968584783785704050 := by
  have h0 := levelEleven_energy_61952
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61952 256 =
      128049885165523875145148540711445 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61952 128 128
      27888266325366548457456136163026 100161618840157326687692404548419 h0 levelEleven_energy_62080
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61952 384 =
      217947080493272262897757117911470 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61952 256 128
      128049885165523875145148540711445 89897195327748387752608577200025 h1 levelEleven_energy_62208
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61952 512 =
      248626033840017968584783785704050 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61952 384 128
      217947080493272262897757117911470 30678953346745705687026667792580 h2 levelEleven_energy_62336
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_121 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 512 =
      5162940970531686526965388 := by
  have h0 := levelEleven_fractional_61952
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 256 =
      2632821280295067180582460 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 128 128
      845216108272132832158494 1787605172022934348423966 h0 levelEleven_fractional_62080
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 384 =
      4240682930614414540676492 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 256 128
      2632821280295067180582460 1607861650319347360094032 h1 levelEleven_fractional_62208
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 512 =
      5162940970531686526965388 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61952 384 128
      4240682930614414540676492 922258039917271986288896 h2 levelEleven_fractional_62336
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_121 : ∀ i : Fin 512,
    levelEleven.lookup (61952 + i.val) ≤ levelElevenRoots.lookup (61952 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_61952
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61952 128 128
    h0 levelEleven_squares_62080
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61952 256 128
    h1 levelEleven_squares_62208
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61952 384 128
    h2 levelEleven_squares_62336
  exact h3

end WordCertDensity.Certificates
