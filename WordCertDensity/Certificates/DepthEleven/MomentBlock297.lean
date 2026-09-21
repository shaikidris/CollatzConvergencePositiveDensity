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
theorem levelEleven_energy_152064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152064 128 =
      15057596081934857183979748468619 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 128 =
      613913768687600405820956 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152064 : ∀ i : Fin 128,
    levelEleven.lookup (152064 + i.val) ≤ levelElevenRoots.lookup (152064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152192 128 =
      84155688123035153240166558561369 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152192 128 =
      1588133037951220466540789 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152192 : ∀ i : Fin 128,
    levelEleven.lookup (152192 + i.val) ≤ levelElevenRoots.lookup (152192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152320 128 =
      94582277304124346115994081489671 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152320 128 =
      1454298722643517941261314 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152320 : ∀ i : Fin 128,
    levelEleven.lookup (152320 + i.val) ≤ levelElevenRoots.lookup (152320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152448 128 =
      137859601142552112317267922706524 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152448 128 =
      2226240196444899131016070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152448 : ∀ i : Fin 128,
    levelEleven.lookup (152448 + i.val) ≤ levelElevenRoots.lookup (152448 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_297 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152064 512 =
      331655162651646468857408311226183 := by
  have h0 := levelEleven_energy_152064
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152064 256 =
      99213284204970010424146307029988 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152064 128 128
      15057596081934857183979748468619 84155688123035153240166558561369 h0 levelEleven_energy_152192
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152064 384 =
      193795561509094356540140388519659 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152064 256 128
      99213284204970010424146307029988 94582277304124346115994081489671 h1 levelEleven_energy_152320
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152064 512 =
      331655162651646468857408311226183 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152064 384 128
      193795561509094356540140388519659 137859601142552112317267922706524 h2 levelEleven_energy_152448
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_297 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 512 =
      5882585725727237944639129 := by
  have h0 := levelEleven_fractional_152064
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 256 =
      2202046806638820872361745 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 128 128
      613913768687600405820956 1588133037951220466540789 h0 levelEleven_fractional_152192
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 384 =
      3656345529282338813623059 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 256 128
      2202046806638820872361745 1454298722643517941261314 h1 levelEleven_fractional_152320
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 512 =
      5882585725727237944639129 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152064 384 128
      3656345529282338813623059 2226240196444899131016070 h2 levelEleven_fractional_152448
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_297 : ∀ i : Fin 512,
    levelEleven.lookup (152064 + i.val) ≤ levelElevenRoots.lookup (152064 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_152064
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152064 128 128
    h0 levelEleven_squares_152192
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152064 256 128
    h1 levelEleven_squares_152320
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152064 384 128
    h2 levelEleven_squares_152448
  exact h3

end WordCertDensity.Certificates
