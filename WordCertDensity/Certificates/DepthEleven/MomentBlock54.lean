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
theorem levelEleven_energy_27648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27648 128 =
      31298704851851757675273565741217 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 128 =
      800137735881352086287678 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27648 : ∀ i : Fin 128,
    levelEleven.lookup (27648 + i.val) ≤ levelElevenRoots.lookup (27648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27776 128 =
      71943657601208870473114995128558 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27776 128 =
      1575357628405651165669221 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27776 : ∀ i : Fin 128,
    levelEleven.lookup (27776 + i.val) ≤ levelElevenRoots.lookup (27776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27904 128 =
      42112226832893606141182311389380 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27904 128 =
      1114039421558942403259407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27904 : ∀ i : Fin 128,
    levelEleven.lookup (27904 + i.val) ≤ levelElevenRoots.lookup (27904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_28032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 28032 128 =
      46001891407526425709766619233545 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_28032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 28032 128 =
      1240162269326159114724819 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_28032 : ∀ i : Fin 128,
    levelEleven.lookup (28032 + i.val) ≤ levelElevenRoots.lookup (28032 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_54 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27648 512 =
      191356480693480659999337491492700 := by
  have h0 := levelEleven_energy_27648
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27648 256 =
      103242362453060628148388560869775 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27648 128 128
      31298704851851757675273565741217 71943657601208870473114995128558 h0 levelEleven_energy_27776
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27648 384 =
      145354589285954234289570872259155 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27648 256 128
      103242362453060628148388560869775 42112226832893606141182311389380 h1 levelEleven_energy_27904
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27648 512 =
      191356480693480659999337491492700 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27648 384 128
      145354589285954234289570872259155 46001891407526425709766619233545 h2 levelEleven_energy_28032
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_54 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 512 =
      4729697055172104769941125 := by
  have h0 := levelEleven_fractional_27648
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 256 =
      2375495364287003251956899 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 128 128
      800137735881352086287678 1575357628405651165669221 h0 levelEleven_fractional_27776
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 384 =
      3489534785845945655216306 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 256 128
      2375495364287003251956899 1114039421558942403259407 h1 levelEleven_fractional_27904
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 512 =
      4729697055172104769941125 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27648 384 128
      3489534785845945655216306 1240162269326159114724819 h2 levelEleven_fractional_28032
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_54 : ∀ i : Fin 512,
    levelEleven.lookup (27648 + i.val) ≤ levelElevenRoots.lookup (27648 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_27648
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27648 128 128
    h0 levelEleven_squares_27776
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27648 256 128
    h1 levelEleven_squares_27904
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27648 384 128
    h2 levelEleven_squares_28032
  exact h3

end WordCertDensity.Certificates
