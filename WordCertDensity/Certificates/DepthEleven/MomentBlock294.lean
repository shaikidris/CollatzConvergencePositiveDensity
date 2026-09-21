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
theorem levelEleven_energy_150528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150528 128 =
      34399092203893144063802748378941 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 128 =
      991262283271203347016964 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150528 : ∀ i : Fin 128,
    levelEleven.lookup (150528 + i.val) ≤ levelElevenRoots.lookup (150528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150656 128 =
      27538449962410170442905421632648 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150656 128 =
      847520564005645975059168 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150656 : ∀ i : Fin 128,
    levelEleven.lookup (150656 + i.val) ≤ levelElevenRoots.lookup (150656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150784 128 =
      148710858730921265289551412424570 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150784 128 =
      2262323383969972002316605 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150784 : ∀ i : Fin 128,
    levelEleven.lookup (150784 + i.val) ≤ levelElevenRoots.lookup (150784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150912 128 =
      29925383602582562774073525992273 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150912 128 =
      821636492628779336461441 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150912 : ∀ i : Fin 128,
    levelEleven.lookup (150912 + i.val) ≤ levelElevenRoots.lookup (150912 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_294 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150528 512 =
      240573784499807142570333108428432 := by
  have h0 := levelEleven_energy_150528
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150528 256 =
      61937542166303314506708170011589 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150528 128 128
      34399092203893144063802748378941 27538449962410170442905421632648 h0 levelEleven_energy_150656
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150528 384 =
      210648400897224579796259582436159 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150528 256 128
      61937542166303314506708170011589 148710858730921265289551412424570 h1 levelEleven_energy_150784
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150528 512 =
      240573784499807142570333108428432 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150528 384 128
      210648400897224579796259582436159 29925383602582562774073525992273 h2 levelEleven_energy_150912
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_294 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 512 =
      4922742723875600660854178 := by
  have h0 := levelEleven_fractional_150528
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 256 =
      1838782847276849322076132 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 128 128
      991262283271203347016964 847520564005645975059168 h0 levelEleven_fractional_150656
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 384 =
      4101106231246821324392737 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 256 128
      1838782847276849322076132 2262323383969972002316605 h1 levelEleven_fractional_150784
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 512 =
      4922742723875600660854178 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150528 384 128
      4101106231246821324392737 821636492628779336461441 h2 levelEleven_fractional_150912
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_294 : ∀ i : Fin 512,
    levelEleven.lookup (150528 + i.val) ≤ levelElevenRoots.lookup (150528 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_150528
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150528 128 128
    h0 levelEleven_squares_150656
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150528 256 128
    h1 levelEleven_squares_150784
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150528 384 128
    h2 levelEleven_squares_150912
  exact h3

end WordCertDensity.Certificates
