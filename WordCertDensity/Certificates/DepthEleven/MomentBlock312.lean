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
theorem levelEleven_energy_159744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159744 128 =
      68203891233675165681684077998790 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 128 =
      1489052290323066207076326 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159744 : ∀ i : Fin 128,
    levelEleven.lookup (159744 + i.val) ≤ levelElevenRoots.lookup (159744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_159872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159872 128 =
      33191632779429749589848500340930 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159872 128 =
      903534368309932052025975 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159872 : ∀ i : Fin 128,
    levelEleven.lookup (159872 + i.val) ≤ levelElevenRoots.lookup (159872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160000 128 =
      36102670237881177877716138033593 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160000 128 =
      1026505220564927202783896 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160000 : ∀ i : Fin 128,
    levelEleven.lookup (160000 + i.val) ≤ levelElevenRoots.lookup (160000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160128 128 =
      45233860873182113707219797034080 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160128 128 =
      1136182486885213208863952 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160128 : ∀ i : Fin 128,
    levelEleven.lookup (160128 + i.val) ≤ levelElevenRoots.lookup (160128 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159744 512 =
      182732055124168206856468513407393 := by
  have h0 := levelEleven_energy_159744
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159744 256 =
      101395524013104915271532578339720 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159744 128 128
      68203891233675165681684077998790 33191632779429749589848500340930 h0 levelEleven_energy_159872
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159744 384 =
      137498194250986093149248716373313 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159744 256 128
      101395524013104915271532578339720 36102670237881177877716138033593 h1 levelEleven_energy_160000
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159744 512 =
      182732055124168206856468513407393 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159744 384 128
      137498194250986093149248716373313 45233860873182113707219797034080 h2 levelEleven_energy_160128
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 512 =
      4555274366083138670750149 := by
  have h0 := levelEleven_fractional_159744
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 256 =
      2392586658632998259102301 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 128 128
      1489052290323066207076326 903534368309932052025975 h0 levelEleven_fractional_159872
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 384 =
      3419091879197925461886197 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 256 128
      2392586658632998259102301 1026505220564927202783896 h1 levelEleven_fractional_160000
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 512 =
      4555274366083138670750149 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159744 384 128
      3419091879197925461886197 1136182486885213208863952 h2 levelEleven_fractional_160128
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_312 : ∀ i : Fin 512,
    levelEleven.lookup (159744 + i.val) ≤ levelElevenRoots.lookup (159744 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_159744
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159744 128 128
    h0 levelEleven_squares_159872
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159744 256 128
    h1 levelEleven_squares_160000
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159744 384 128
    h2 levelEleven_squares_160128
  exact h3

end WordCertDensity.Certificates
