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
theorem levelEleven_energy_98816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98816 128 =
      53712752021088406543592900583772 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 128 =
      1335599485285074374693836 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98816 : ∀ i : Fin 128,
    levelEleven.lookup (98816 + i.val) ≤ levelElevenRoots.lookup (98816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98944 128 =
      23375029610479204029812805828354 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98944 128 =
      760978929898349407563171 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98944 : ∀ i : Fin 128,
    levelEleven.lookup (98944 + i.val) ≤ levelElevenRoots.lookup (98944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99072 128 =
      27774103357979487627816061745075 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99072 128 =
      839818472109663748015388 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99072 : ∀ i : Fin 128,
    levelEleven.lookup (99072 + i.val) ≤ levelElevenRoots.lookup (99072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99200 128 =
      216048714800591814082835171257890 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99200 128 =
      2405566721944941327470932 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99200 : ∀ i : Fin 128,
    levelEleven.lookup (99200 + i.val) ≤ levelElevenRoots.lookup (99200 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_193 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98816 512 =
      320910599790138912284056939415091 := by
  have h0 := levelEleven_energy_98816
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98816 256 =
      77087781631567610573405706412126 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98816 128 128
      53712752021088406543592900583772 23375029610479204029812805828354 h0 levelEleven_energy_98944
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98816 384 =
      104861884989547098201221768157201 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98816 256 128
      77087781631567610573405706412126 27774103357979487627816061745075 h1 levelEleven_energy_99072
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 98816 512 =
      320910599790138912284056939415091 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 98816 384 128
      104861884989547098201221768157201 216048714800591814082835171257890 h2 levelEleven_energy_99200
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_193 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 512 =
      5341963609238028857743327 := by
  have h0 := levelEleven_fractional_98816
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 256 =
      2096578415183423782257007 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 128 128
      1335599485285074374693836 760978929898349407563171 h0 levelEleven_fractional_98944
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 384 =
      2936396887293087530272395 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 256 128
      2096578415183423782257007 839818472109663748015388 h1 levelEleven_fractional_99072
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 512 =
      5341963609238028857743327 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98816 384 128
      2936396887293087530272395 2405566721944941327470932 h2 levelEleven_fractional_99200
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_193 : ∀ i : Fin 512,
    levelEleven.lookup (98816 + i.val) ≤ levelElevenRoots.lookup (98816 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_98816
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98816 128 128
    h0 levelEleven_squares_98944
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98816 256 128
    h1 levelEleven_squares_99072
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 98816 384 128
    h2 levelEleven_squares_99200
  exact h3

end WordCertDensity.Certificates
