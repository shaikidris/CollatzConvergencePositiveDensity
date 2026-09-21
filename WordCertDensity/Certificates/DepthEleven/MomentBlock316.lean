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
theorem levelEleven_energy_161792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161792 128 =
      38227134045293153911975009606300 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 128 =
      957851345254734831821734 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161792 : ∀ i : Fin 128,
    levelEleven.lookup (161792 + i.val) ≤ levelElevenRoots.lookup (161792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161920 128 =
      31846037795135657670587111023293 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161920 128 =
      967399715908059874699267 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161920 : ∀ i : Fin 128,
    levelEleven.lookup (161920 + i.val) ≤ levelElevenRoots.lookup (161920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162048 128 =
      66976878719012972405709856555037 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162048 128 =
      1372001605350943335453584 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162048 : ∀ i : Fin 128,
    levelEleven.lookup (162048 + i.val) ≤ levelElevenRoots.lookup (162048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162176 128 =
      106117449579812388717012973047888 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162176 128 =
      1815666022591316105010743 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162176 : ∀ i : Fin 128,
    levelEleven.lookup (162176 + i.val) ≤ levelElevenRoots.lookup (162176 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_316 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161792 512 =
      243167500139254172705284950232518 := by
  have h0 := levelEleven_energy_161792
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161792 256 =
      70073171840428811582562120629593 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161792 128 128
      38227134045293153911975009606300 31846037795135657670587111023293 h0 levelEleven_energy_161920
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161792 384 =
      137050050559441783988271977184630 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161792 256 128
      70073171840428811582562120629593 66976878719012972405709856555037 h1 levelEleven_energy_162048
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161792 512 =
      243167500139254172705284950232518 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161792 384 128
      137050050559441783988271977184630 106117449579812388717012973047888 h2 levelEleven_energy_162176
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_316 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 512 =
      5112918689105054146985328 := by
  have h0 := levelEleven_fractional_161792
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 256 =
      1925251061162794706521001 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 128 128
      957851345254734831821734 967399715908059874699267 h0 levelEleven_fractional_161920
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 384 =
      3297252666513738041974585 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 256 128
      1925251061162794706521001 1372001605350943335453584 h1 levelEleven_fractional_162048
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 512 =
      5112918689105054146985328 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161792 384 128
      3297252666513738041974585 1815666022591316105010743 h2 levelEleven_fractional_162176
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_316 : ∀ i : Fin 512,
    levelEleven.lookup (161792 + i.val) ≤ levelElevenRoots.lookup (161792 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_161792
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161792 128 128
    h0 levelEleven_squares_161920
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161792 256 128
    h1 levelEleven_squares_162048
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161792 384 128
    h2 levelEleven_squares_162176
  exact h3

end WordCertDensity.Certificates
