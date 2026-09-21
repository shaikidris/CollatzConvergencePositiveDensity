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
theorem levelEleven_energy_28672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28672 128 =
      26906633918371301634303138055591 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 128 =
      850302539900382413146901 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28672 : ∀ i : Fin 128,
    levelEleven.lookup (28672 + i.val) ≤ levelElevenRoots.lookup (28672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28800 128 =
      55289836239201944774527141977565 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28800 128 =
      1233448474651154970609344 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28800 : ∀ i : Fin 128,
    levelEleven.lookup (28800 + i.val) ≤ levelElevenRoots.lookup (28800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28928 128 =
      30904058938109230350103864281085 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28928 128 =
      836787092538096174637000 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28928 : ∀ i : Fin 128,
    levelEleven.lookup (28928 + i.val) ≤ levelElevenRoots.lookup (28928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29056 128 =
      32562130746985169849878272182619 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29056 128 =
      969688906933206459364587 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29056 : ∀ i : Fin 128,
    levelEleven.lookup (29056 + i.val) ≤ levelElevenRoots.lookup (29056 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_56 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28672 512 =
      145662659842667646608812416496860 := by
  have h0 := levelEleven_energy_28672
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28672 256 =
      82196470157573246408830280033156 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28672 128 128
      26906633918371301634303138055591 55289836239201944774527141977565 h0 levelEleven_energy_28800
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28672 384 =
      113100529095682476758934144314241 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28672 256 128
      82196470157573246408830280033156 30904058938109230350103864281085 h1 levelEleven_energy_28928
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 28672 512 =
      145662659842667646608812416496860 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 28672 384 128
      113100529095682476758934144314241 32562130746985169849878272182619 h2 levelEleven_energy_29056
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_56 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 512 =
      3890227014022840017757832 := by
  have h0 := levelEleven_fractional_28672
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 256 =
      2083751014551537383756245 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 128 128
      850302539900382413146901 1233448474651154970609344 h0 levelEleven_fractional_28800
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 384 =
      2920538107089633558393245 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 256 128
      2083751014551537383756245 836787092538096174637000 h1 levelEleven_fractional_28928
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 512 =
      3890227014022840017757832 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28672 384 128
      2920538107089633558393245 969688906933206459364587 h2 levelEleven_fractional_29056
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_56 : ∀ i : Fin 512,
    levelEleven.lookup (28672 + i.val) ≤ levelElevenRoots.lookup (28672 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_28672
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28672 128 128
    h0 levelEleven_squares_28800
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28672 256 128
    h1 levelEleven_squares_28928
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 28672 384 128
    h2 levelEleven_squares_29056
  exact h3

end WordCertDensity.Certificates
