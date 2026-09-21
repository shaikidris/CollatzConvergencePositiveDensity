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
theorem levelEleven_energy_2048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2048 128 =
      63583196237422685930649963889937 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 128 =
      1389250253990527311337664 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2048 : ∀ i : Fin 128,
    levelEleven.lookup (2048 + i.val) ≤ levelElevenRoots.lookup (2048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2176 128 =
      34213921525325959808399880977123 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2176 128 =
      938140274612826508706532 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2176 : ∀ i : Fin 128,
    levelEleven.lookup (2176 + i.val) ≤ levelElevenRoots.lookup (2176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2304 128 =
      278811170603046231231827189533962 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2304 128 =
      3302053847626384890406192 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2304 : ∀ i : Fin 128,
    levelEleven.lookup (2304 + i.val) ≤ levelElevenRoots.lookup (2304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2432 128 =
      19331526685965820604832905634112 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2432 128 =
      714042090866317548189714 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2432 : ∀ i : Fin 128,
    levelEleven.lookup (2432 + i.val) ≤ levelElevenRoots.lookup (2432 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_4 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2048 512 =
      395939815051760697575709940035134 := by
  have h0 := levelEleven_energy_2048
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2048 256 =
      97797117762748645739049844867060 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2048 128 128
      63583196237422685930649963889937 34213921525325959808399880977123 h0 levelEleven_energy_2176
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2048 384 =
      376608288365794876970877034401022 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2048 256 128
      97797117762748645739049844867060 278811170603046231231827189533962 h1 levelEleven_energy_2304
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2048 512 =
      395939815051760697575709940035134 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2048 384 128
      376608288365794876970877034401022 19331526685965820604832905634112 h2 levelEleven_energy_2432
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_4 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 512 =
      6343486467096056258640102 := by
  have h0 := levelEleven_fractional_2048
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 256 =
      2327390528603353820044196 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 128 128
      1389250253990527311337664 938140274612826508706532 h0 levelEleven_fractional_2176
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 384 =
      5629444376229738710450388 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 256 128
      2327390528603353820044196 3302053847626384890406192 h1 levelEleven_fractional_2304
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 512 =
      6343486467096056258640102 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2048 384 128
      5629444376229738710450388 714042090866317548189714 h2 levelEleven_fractional_2432
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_4 : ∀ i : Fin 512,
    levelEleven.lookup (2048 + i.val) ≤ levelElevenRoots.lookup (2048 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_2048
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2048 128 128
    h0 levelEleven_squares_2176
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2048 256 128
    h1 levelEleven_squares_2304
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2048 384 128
    h2 levelEleven_squares_2432
  exact h3

end WordCertDensity.Certificates
