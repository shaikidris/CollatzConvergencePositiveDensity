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
theorem levelEleven_energy_165376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165376 128 =
      94064102654660207380898550068063 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 128 =
      1673188820935242553624963 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165376 : ∀ i : Fin 128,
    levelEleven.lookup (165376 + i.val) ≤ levelElevenRoots.lookup (165376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_165504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165504 128 =
      30832659247477419947830407935023 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165504 128 =
      842335864532305296173093 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165504 : ∀ i : Fin 128,
    levelEleven.lookup (165504 + i.val) ≤ levelElevenRoots.lookup (165504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_165632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165632 128 =
      54339734523502937741635182011314 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165632 128 =
      1326144189275919874392512 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165632 : ∀ i : Fin 128,
    levelEleven.lookup (165632 + i.val) ≤ levelElevenRoots.lookup (165632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_165760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165760 128 =
      86294648184374887095932504031303 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165760 128 =
      1504369541889556756781623 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165760 : ∀ i : Fin 128,
    levelEleven.lookup (165760 + i.val) ≤ levelElevenRoots.lookup (165760 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_323 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165376 512 =
      265531144610015452166296644045703 := by
  have h0 := levelEleven_energy_165376
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165376 256 =
      124896761902137627328728958003086 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165376 128 128
      94064102654660207380898550068063 30832659247477419947830407935023 h0 levelEleven_energy_165504
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165376 384 =
      179236496425640565070364140014400 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165376 256 128
      124896761902137627328728958003086 54339734523502937741635182011314 h1 levelEleven_energy_165632
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165376 512 =
      265531144610015452166296644045703 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165376 384 128
      179236496425640565070364140014400 86294648184374887095932504031303 h2 levelEleven_energy_165760
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_323 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 512 =
      5346038416633024480972191 := by
  have h0 := levelEleven_fractional_165376
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 256 =
      2515524685467547849798056 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 128 128
      1673188820935242553624963 842335864532305296173093 h0 levelEleven_fractional_165504
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 384 =
      3841668874743467724190568 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 256 128
      2515524685467547849798056 1326144189275919874392512 h1 levelEleven_fractional_165632
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 512 =
      5346038416633024480972191 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165376 384 128
      3841668874743467724190568 1504369541889556756781623 h2 levelEleven_fractional_165760
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_323 : ∀ i : Fin 512,
    levelEleven.lookup (165376 + i.val) ≤ levelElevenRoots.lookup (165376 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_165376
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165376 128 128
    h0 levelEleven_squares_165504
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165376 256 128
    h1 levelEleven_squares_165632
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165376 384 128
    h2 levelEleven_squares_165760
  exact h3

end WordCertDensity.Certificates
