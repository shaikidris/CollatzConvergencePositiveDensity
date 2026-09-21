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
theorem levelEleven_energy_52224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52224 128 =
      23871729679518428911329534546909 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 128 =
      790934015692840249834380 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52224 : ∀ i : Fin 128,
    levelEleven.lookup (52224 + i.val) ≤ levelElevenRoots.lookup (52224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52352 128 =
      97661716384911856933074006603249 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52352 128 =
      1790303924426173456013682 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52352 : ∀ i : Fin 128,
    levelEleven.lookup (52352 + i.val) ≤ levelElevenRoots.lookup (52352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52480 128 =
      302481664646721226382068567304454 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52480 128 =
      3117028886923049325767865 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52480 : ∀ i : Fin 128,
    levelEleven.lookup (52480 + i.val) ≤ levelElevenRoots.lookup (52480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52608 128 =
      50315834237942336217700996925390 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52608 128 =
      1299672273299088771494040 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52608 : ∀ i : Fin 128,
    levelEleven.lookup (52608 + i.val) ≤ levelElevenRoots.lookup (52608 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_102 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52224 512 =
      474330944949093848444173105380002 := by
  have h0 := levelEleven_energy_52224
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52224 256 =
      121533446064430285844403541150158 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52224 128 128
      23871729679518428911329534546909 97661716384911856933074006603249 h0 levelEleven_energy_52352
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52224 384 =
      424015110711151512226472108454612 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52224 256 128
      121533446064430285844403541150158 302481664646721226382068567304454 h1 levelEleven_energy_52480
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52224 512 =
      474330944949093848444173105380002 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52224 384 128
      424015110711151512226472108454612 50315834237942336217700996925390 h2 levelEleven_energy_52608
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_102 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 512 =
      6997939100341151803109967 := by
  have h0 := levelEleven_fractional_52224
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 256 =
      2581237940119013705848062 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 128 128
      790934015692840249834380 1790303924426173456013682 h0 levelEleven_fractional_52352
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 384 =
      5698266827042063031615927 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 256 128
      2581237940119013705848062 3117028886923049325767865 h1 levelEleven_fractional_52480
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 512 =
      6997939100341151803109967 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52224 384 128
      5698266827042063031615927 1299672273299088771494040 h2 levelEleven_fractional_52608
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_102 : ∀ i : Fin 512,
    levelEleven.lookup (52224 + i.val) ≤ levelElevenRoots.lookup (52224 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_52224
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52224 128 128
    h0 levelEleven_squares_52352
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52224 256 128
    h1 levelEleven_squares_52480
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52224 384 128
    h2 levelEleven_squares_52608
  exact h3

end WordCertDensity.Certificates
