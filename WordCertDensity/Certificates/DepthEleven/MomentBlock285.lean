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
theorem levelEleven_energy_145920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145920 128 =
      71960288839165473496231019242081 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 128 =
      1527871406811885753934781 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145920 : ∀ i : Fin 128,
    levelEleven.lookup (145920 + i.val) ≤ levelElevenRoots.lookup (145920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146048 128 =
      42253232860994857894838641640588 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146048 128 =
      1080329446433507562626956 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146048 : ∀ i : Fin 128,
    levelEleven.lookup (146048 + i.val) ≤ levelElevenRoots.lookup (146048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146176 128 =
      32605666523460687830457007651429 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146176 128 =
      971573477029874177538375 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146176 : ∀ i : Fin 128,
    levelEleven.lookup (146176 + i.val) ≤ levelElevenRoots.lookup (146176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146304 128 =
      117277090087088033652846422056960 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146304 128 =
      1675315923961078250654524 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146304 : ∀ i : Fin 128,
    levelEleven.lookup (146304 + i.val) ≤ levelElevenRoots.lookup (146304 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_285 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145920 512 =
      264096278310709052874373090591058 := by
  have h0 := levelEleven_energy_145920
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145920 256 =
      114213521700160331391069660882669 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145920 128 128
      71960288839165473496231019242081 42253232860994857894838641640588 h0 levelEleven_energy_146048
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145920 384 =
      146819188223621019221526668534098 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145920 256 128
      114213521700160331391069660882669 32605666523460687830457007651429 h1 levelEleven_energy_146176
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 145920 512 =
      264096278310709052874373090591058 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 145920 384 128
      146819188223621019221526668534098 117277090087088033652846422056960 h2 levelEleven_energy_146304
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_285 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 512 =
      5255090254236345744754636 := by
  have h0 := levelEleven_fractional_145920
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 256 =
      2608200853245393316561737 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 128 128
      1527871406811885753934781 1080329446433507562626956 h0 levelEleven_fractional_146048
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 384 =
      3579774330275267494100112 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 256 128
      2608200853245393316561737 971573477029874177538375 h1 levelEleven_fractional_146176
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 512 =
      5255090254236345744754636 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145920 384 128
      3579774330275267494100112 1675315923961078250654524 h2 levelEleven_fractional_146304
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_285 : ∀ i : Fin 512,
    levelEleven.lookup (145920 + i.val) ≤ levelElevenRoots.lookup (145920 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_145920
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145920 128 128
    h0 levelEleven_squares_146048
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145920 256 128
    h1 levelEleven_squares_146176
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 145920 384 128
    h2 levelEleven_squares_146304
  exact h3

end WordCertDensity.Certificates
