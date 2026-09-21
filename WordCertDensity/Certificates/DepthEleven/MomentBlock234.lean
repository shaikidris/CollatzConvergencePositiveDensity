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
theorem levelEleven_energy_119808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119808 128 =
      36436628932940676477769473730330 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 128 =
      992690200892213760974912 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119808 : ∀ i : Fin 128,
    levelEleven.lookup (119808 + i.val) ≤ levelElevenRoots.lookup (119808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119936 128 =
      26319302095749672040741144702481 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119936 128 =
      853258660977202544488140 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119936 : ∀ i : Fin 128,
    levelEleven.lookup (119936 + i.val) ≤ levelElevenRoots.lookup (119936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120064 128 =
      85413019963170703916628358529746 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120064 128 =
      1340892354705127896098149 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120064 : ∀ i : Fin 128,
    levelEleven.lookup (120064 + i.val) ≤ levelElevenRoots.lookup (120064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120192 128 =
      66147344807661240188114910992360 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120192 128 =
      1494739744393267389988801 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120192 : ∀ i : Fin 128,
    levelEleven.lookup (120192 + i.val) ≤ levelElevenRoots.lookup (120192 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_234 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119808 512 =
      214316295799522292623253887954917 := by
  have h0 := levelEleven_energy_119808
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119808 256 =
      62755931028690348518510618432811 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119808 128 128
      36436628932940676477769473730330 26319302095749672040741144702481 h0 levelEleven_energy_119936
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119808 384 =
      148168950991861052435138976962557 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119808 256 128
      62755931028690348518510618432811 85413019963170703916628358529746 h1 levelEleven_energy_120064
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119808 512 =
      214316295799522292623253887954917 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119808 384 128
      148168950991861052435138976962557 66147344807661240188114910992360 h2 levelEleven_energy_120192
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_234 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 512 =
      4681580960967811591550002 := by
  have h0 := levelEleven_fractional_119808
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 256 =
      1845948861869416305463052 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 128 128
      992690200892213760974912 853258660977202544488140 h0 levelEleven_fractional_119936
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 384 =
      3186841216574544201561201 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 256 128
      1845948861869416305463052 1340892354705127896098149 h1 levelEleven_fractional_120064
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 512 =
      4681580960967811591550002 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119808 384 128
      3186841216574544201561201 1494739744393267389988801 h2 levelEleven_fractional_120192
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_234 : ∀ i : Fin 512,
    levelEleven.lookup (119808 + i.val) ≤ levelElevenRoots.lookup (119808 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_119808
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119808 128 128
    h0 levelEleven_squares_119936
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119808 256 128
    h1 levelEleven_squares_120064
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119808 384 128
    h2 levelEleven_squares_120192
  exact h3

end WordCertDensity.Certificates
