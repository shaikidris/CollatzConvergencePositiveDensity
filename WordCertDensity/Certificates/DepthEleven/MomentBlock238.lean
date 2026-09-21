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
theorem levelEleven_energy_121856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121856 128 =
      33334650793240232436893193701652 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 128 =
      962943499698819570315433 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121856 : ∀ i : Fin 128,
    levelEleven.lookup (121856 + i.val) ≤ levelElevenRoots.lookup (121856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121984 128 =
      26954903825912553162412643654650 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121984 128 =
      877040844528689123325741 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121984 : ∀ i : Fin 128,
    levelEleven.lookup (121984 + i.val) ≤ levelElevenRoots.lookup (121984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_122112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122112 128 =
      79418190883227489932903892069309 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122112 128 =
      1496533254418831568663885 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122112 : ∀ i : Fin 128,
    levelEleven.lookup (122112 + i.val) ≤ levelElevenRoots.lookup (122112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_122240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122240 128 =
      43037588731069796373343236415452 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122240 128 =
      1089214371555318897024491 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122240 : ∀ i : Fin 128,
    levelEleven.lookup (122240 + i.val) ≤ levelElevenRoots.lookup (122240 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_238 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121856 512 =
      182745334233450071905552965841063 := by
  have h0 := levelEleven_energy_121856
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121856 256 =
      60289554619152785599305837356302 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121856 128 128
      33334650793240232436893193701652 26954903825912553162412643654650 h0 levelEleven_energy_121984
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121856 384 =
      139707745502380275532209729425611 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121856 256 128
      60289554619152785599305837356302 79418190883227489932903892069309 h1 levelEleven_energy_122112
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121856 512 =
      182745334233450071905552965841063 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121856 384 128
      139707745502380275532209729425611 43037588731069796373343236415452 h2 levelEleven_energy_122240
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_238 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 512 =
      4425731970201659159329550 := by
  have h0 := levelEleven_fractional_121856
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 256 =
      1839984344227508693641174 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 128 128
      962943499698819570315433 877040844528689123325741 h0 levelEleven_fractional_121984
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 384 =
      3336517598646340262305059 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 256 128
      1839984344227508693641174 1496533254418831568663885 h1 levelEleven_fractional_122112
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 512 =
      4425731970201659159329550 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121856 384 128
      3336517598646340262305059 1089214371555318897024491 h2 levelEleven_fractional_122240
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_238 : ∀ i : Fin 512,
    levelEleven.lookup (121856 + i.val) ≤ levelElevenRoots.lookup (121856 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_121856
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121856 128 128
    h0 levelEleven_squares_121984
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121856 256 128
    h1 levelEleven_squares_122112
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121856 384 128
    h2 levelEleven_squares_122240
  exact h3

end WordCertDensity.Certificates
