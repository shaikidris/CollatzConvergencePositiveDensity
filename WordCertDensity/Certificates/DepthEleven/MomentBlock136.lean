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
theorem levelEleven_energy_69632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69632 128 =
      48171474664355853482764015817540 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 128 =
      1228438682381653455116988 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69632 : ∀ i : Fin 128,
    levelEleven.lookup (69632 + i.val) ≤ levelElevenRoots.lookup (69632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_69760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69760 128 =
      26738103370556570809493612969703 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69760 128 =
      843234291254569074085965 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69760 : ∀ i : Fin 128,
    levelEleven.lookup (69760 + i.val) ≤ levelElevenRoots.lookup (69760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_69888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69888 128 =
      236950413296809971734265301856909 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69888 128 =
      2837140267915329190665995 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69888 : ∀ i : Fin 128,
    levelEleven.lookup (69888 + i.val) ≤ levelElevenRoots.lookup (69888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70016 128 =
      51367827164998346692236062008912 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70016 128 =
      1091732748613208178636200 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70016 : ∀ i : Fin 128,
    levelEleven.lookup (70016 + i.val) ≤ levelElevenRoots.lookup (70016 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69632 512 =
      363227818496720742718758992653064 := by
  have h0 := levelEleven_energy_69632
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69632 256 =
      74909578034912424292257628787243 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69632 128 128
      48171474664355853482764015817540 26738103370556570809493612969703 h0 levelEleven_energy_69760
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69632 384 =
      311859991331722396026522930644152 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69632 256 128
      74909578034912424292257628787243 236950413296809971734265301856909 h1 levelEleven_energy_69888
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69632 512 =
      363227818496720742718758992653064 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69632 384 128
      311859991331722396026522930644152 51367827164998346692236062008912 h2 levelEleven_energy_70016
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 512 =
      6000545990164759898505148 := by
  have h0 := levelEleven_fractional_69632
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 256 =
      2071672973636222529202953 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 128 128
      1228438682381653455116988 843234291254569074085965 h0 levelEleven_fractional_69760
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 384 =
      4908813241551551719868948 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 256 128
      2071672973636222529202953 2837140267915329190665995 h1 levelEleven_fractional_69888
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 512 =
      6000545990164759898505148 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69632 384 128
      4908813241551551719868948 1091732748613208178636200 h2 levelEleven_fractional_70016
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_136 : ∀ i : Fin 512,
    levelEleven.lookup (69632 + i.val) ≤ levelElevenRoots.lookup (69632 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_69632
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69632 128 128
    h0 levelEleven_squares_69760
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69632 256 128
    h1 levelEleven_squares_69888
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69632 384 128
    h2 levelEleven_squares_70016
  exact h3

end WordCertDensity.Certificates
