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
theorem levelEleven_energy_74752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74752 128 =
      27950512079163372331820534218066 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 128 =
      913751883935756535020700 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74752 : ∀ i : Fin 128,
    levelEleven.lookup (74752 + i.val) ≤ levelElevenRoots.lookup (74752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_74880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74880 128 =
      42170138253574992499251719099552 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74880 128 =
      995246671759527107438669 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74880 : ∀ i : Fin 128,
    levelEleven.lookup (74880 + i.val) ≤ levelElevenRoots.lookup (74880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75008 128 =
      87055966746237998005252566047565 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75008 128 =
      1619335622642161779381054 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75008 : ∀ i : Fin 128,
    levelEleven.lookup (75008 + i.val) ≤ levelElevenRoots.lookup (75008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75136 128 =
      50488786477654900444452655757040 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75136 128 =
      1162380547591505975166845 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75136 : ∀ i : Fin 128,
    levelEleven.lookup (75136 + i.val) ≤ levelElevenRoots.lookup (75136 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_146 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74752 512 =
      207665403556631263280777475122223 := by
  have h0 := levelEleven_energy_74752
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74752 256 =
      70120650332738364831072253317618 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74752 128 128
      27950512079163372331820534218066 42170138253574992499251719099552 h0 levelEleven_energy_74880
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74752 384 =
      157176617078976362836324819365183 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74752 256 128
      70120650332738364831072253317618 87055966746237998005252566047565 h1 levelEleven_energy_75008
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74752 512 =
      207665403556631263280777475122223 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74752 384 128
      157176617078976362836324819365183 50488786477654900444452655757040 h2 levelEleven_energy_75136
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_146 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 512 =
      4690714725928951397007268 := by
  have h0 := levelEleven_fractional_74752
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 256 =
      1908998555695283642459369 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 128 128
      913751883935756535020700 995246671759527107438669 h0 levelEleven_fractional_74880
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 384 =
      3528334178337445421840423 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 256 128
      1908998555695283642459369 1619335622642161779381054 h1 levelEleven_fractional_75008
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 512 =
      4690714725928951397007268 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74752 384 128
      3528334178337445421840423 1162380547591505975166845 h2 levelEleven_fractional_75136
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_146 : ∀ i : Fin 512,
    levelEleven.lookup (74752 + i.val) ≤ levelElevenRoots.lookup (74752 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_74752
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74752 128 128
    h0 levelEleven_squares_74880
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74752 256 128
    h1 levelEleven_squares_75008
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74752 384 128
    h2 levelEleven_squares_75136
  exact h3

end WordCertDensity.Certificates
