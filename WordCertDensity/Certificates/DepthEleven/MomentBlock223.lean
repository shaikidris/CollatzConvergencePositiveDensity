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
theorem levelEleven_energy_114176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114176 128 =
      22157647443143885942445381250690 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 128 =
      727670481419907531237185 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114176 : ∀ i : Fin 128,
    levelEleven.lookup (114176 + i.val) ≤ levelElevenRoots.lookup (114176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114304 128 =
      48102801333920465287991154535835 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114304 128 =
      1217170444902942087524056 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114304 : ∀ i : Fin 128,
    levelEleven.lookup (114304 + i.val) ≤ levelElevenRoots.lookup (114304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114432 128 =
      45431740603320643500980151064138 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114432 128 =
      1086722619968328427951632 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114432 : ∀ i : Fin 128,
    levelEleven.lookup (114432 + i.val) ≤ levelElevenRoots.lookup (114432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_114560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114560 128 =
      112060638153176824172465865136580 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_114560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114560 128 =
      1880772355684733208854214 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_114560 : ∀ i : Fin 128,
    levelEleven.lookup (114560 + i.val) ≤ levelElevenRoots.lookup (114560 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_223 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 114176 512 =
      227752827533561818903882551987243 := by
  have h0 := levelEleven_energy_114176
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114176 256 =
      70260448777064351230436535786525 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114176 128 128
      22157647443143885942445381250690 48102801333920465287991154535835 h0 levelEleven_energy_114304
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114176 384 =
      115692189380384994731416686850663 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114176 256 128
      70260448777064351230436535786525 45431740603320643500980151064138 h1 levelEleven_energy_114432
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 114176 512 =
      227752827533561818903882551987243 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 114176 384 128
      115692189380384994731416686850663 112060638153176824172465865136580 h2 levelEleven_energy_114560
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_223 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 512 =
      4912335901975911255567087 := by
  have h0 := levelEleven_fractional_114176
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 256 =
      1944840926322849618761241 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 128 128
      727670481419907531237185 1217170444902942087524056 h0 levelEleven_fractional_114304
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 384 =
      3031563546291178046712873 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 256 128
      1944840926322849618761241 1086722619968328427951632 h1 levelEleven_fractional_114432
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 512 =
      4912335901975911255567087 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 114176 384 128
      3031563546291178046712873 1880772355684733208854214 h2 levelEleven_fractional_114560
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_223 : ∀ i : Fin 512,
    levelEleven.lookup (114176 + i.val) ≤ levelElevenRoots.lookup (114176 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_114176
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114176 128 128
    h0 levelEleven_squares_114304
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114176 256 128
    h1 levelEleven_squares_114432
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 114176 384 128
    h2 levelEleven_squares_114560
  exact h3

end WordCertDensity.Certificates
