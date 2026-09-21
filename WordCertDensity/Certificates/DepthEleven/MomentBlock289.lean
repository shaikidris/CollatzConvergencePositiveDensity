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
theorem levelEleven_energy_147968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147968 128 =
      61835507828940718727834402903863 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 128 =
      1287582316490810199716365 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147968 : ∀ i : Fin 128,
    levelEleven.lookup (147968 + i.val) ≤ levelElevenRoots.lookup (147968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148096 128 =
      50093142227110136280767844572603 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148096 128 =
      1169068635213258897302680 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148096 : ∀ i : Fin 128,
    levelEleven.lookup (148096 + i.val) ≤ levelElevenRoots.lookup (148096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148224 128 =
      38944294514494180697767016701198 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148224 128 =
      1033267794245818255055590 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148224 : ∀ i : Fin 128,
    levelEleven.lookup (148224 + i.val) ≤ levelElevenRoots.lookup (148224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148352 128 =
      87826494056453931075691124967906 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148352 128 =
      1688379563059389451013976 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148352 : ∀ i : Fin 128,
    levelEleven.lookup (148352 + i.val) ≤ levelElevenRoots.lookup (148352 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_289 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147968 512 =
      238699438626998966782060389145570 := by
  have h0 := levelEleven_energy_147968
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147968 256 =
      111928650056050855008602247476466 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147968 128 128
      61835507828940718727834402903863 50093142227110136280767844572603 h0 levelEleven_energy_148096
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147968 384 =
      150872944570545035706369264177664 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147968 256 128
      111928650056050855008602247476466 38944294514494180697767016701198 h1 levelEleven_energy_148224
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147968 512 =
      238699438626998966782060389145570 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147968 384 128
      150872944570545035706369264177664 87826494056453931075691124967906 h2 levelEleven_energy_148352
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_289 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 512 =
      5178298309009276803088611 := by
  have h0 := levelEleven_fractional_147968
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 256 =
      2456650951704069097019045 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 128 128
      1287582316490810199716365 1169068635213258897302680 h0 levelEleven_fractional_148096
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 384 =
      3489918745949887352074635 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 256 128
      2456650951704069097019045 1033267794245818255055590 h1 levelEleven_fractional_148224
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 512 =
      5178298309009276803088611 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147968 384 128
      3489918745949887352074635 1688379563059389451013976 h2 levelEleven_fractional_148352
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_289 : ∀ i : Fin 512,
    levelEleven.lookup (147968 + i.val) ≤ levelElevenRoots.lookup (147968 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_147968
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147968 128 128
    h0 levelEleven_squares_148096
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147968 256 128
    h1 levelEleven_squares_148224
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147968 384 128
    h2 levelEleven_squares_148352
  exact h3

end WordCertDensity.Certificates
