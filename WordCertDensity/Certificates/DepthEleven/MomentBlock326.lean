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
theorem levelEleven_energy_166912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166912 128 =
      26355876630148104113160636203409 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 128 =
      827139432903734036476706 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166912 : ∀ i : Fin 128,
    levelEleven.lookup (166912 + i.val) ≤ levelElevenRoots.lookup (166912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167040 128 =
      43174884359375315632369487972937 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167040 128 =
      1055517505644269809031906 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167040 : ∀ i : Fin 128,
    levelEleven.lookup (167040 + i.val) ≤ levelElevenRoots.lookup (167040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167168 128 =
      141011575995935996199136275146205 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167168 128 =
      2249002900667324537667423 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167168 : ∀ i : Fin 128,
    levelEleven.lookup (167168 + i.val) ≤ levelElevenRoots.lookup (167168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167296 128 =
      42155268613945177892635607934265 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167296 128 =
      1114295718098623068043334 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167296 : ∀ i : Fin 128,
    levelEleven.lookup (167296 + i.val) ≤ levelElevenRoots.lookup (167296 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_326 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166912 512 =
      252697605599404593837302007256816 := by
  have h0 := levelEleven_energy_166912
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166912 256 =
      69530760989523419745530124176346 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166912 128 128
      26355876630148104113160636203409 43174884359375315632369487972937 h0 levelEleven_energy_167040
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166912 384 =
      210542336985459415944666399322551 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166912 256 128
      69530760989523419745530124176346 141011575995935996199136275146205 h1 levelEleven_energy_167168
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166912 512 =
      252697605599404593837302007256816 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166912 384 128
      210542336985459415944666399322551 42155268613945177892635607934265 h2 levelEleven_energy_167296
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_326 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 512 =
      5245955557313951451219369 := by
  have h0 := levelEleven_fractional_166912
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 256 =
      1882656938548003845508612 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 128 128
      827139432903734036476706 1055517505644269809031906 h0 levelEleven_fractional_167040
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 384 =
      4131659839215328383176035 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 256 128
      1882656938548003845508612 2249002900667324537667423 h1 levelEleven_fractional_167168
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 512 =
      5245955557313951451219369 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166912 384 128
      4131659839215328383176035 1114295718098623068043334 h2 levelEleven_fractional_167296
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_326 : ∀ i : Fin 512,
    levelEleven.lookup (166912 + i.val) ≤ levelElevenRoots.lookup (166912 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_166912
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166912 128 128
    h0 levelEleven_squares_167040
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166912 256 128
    h1 levelEleven_squares_167168
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166912 384 128
    h2 levelEleven_squares_167296
  exact h3

end WordCertDensity.Certificates
