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
theorem levelEleven_energy_39936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39936 128 =
      49964982111436988284633711375724 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 128 =
      1197391915226159653785323 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39936 : ∀ i : Fin 128,
    levelEleven.lookup (39936 + i.val) ≤ levelElevenRoots.lookup (39936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40064 128 =
      26600263062042690524315619717147 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40064 128 =
      783316999210620999538001 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40064 : ∀ i : Fin 128,
    levelEleven.lookup (40064 + i.val) ≤ levelElevenRoots.lookup (40064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40192 128 =
      94691832528420754192981645352125 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40192 128 =
      1519370241021230808963495 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40192 : ∀ i : Fin 128,
    levelEleven.lookup (40192 + i.val) ≤ levelElevenRoots.lookup (40192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40320 128 =
      88749764398656658905010804132515 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40320 128 =
      1545448413996297569112070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40320 : ∀ i : Fin 128,
    levelEleven.lookup (40320 + i.val) ≤ levelElevenRoots.lookup (40320 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_78 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39936 512 =
      260006842100557091906941780577511 := by
  have h0 := levelEleven_energy_39936
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39936 256 =
      76565245173479678808949331092871 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39936 128 128
      49964982111436988284633711375724 26600263062042690524315619717147 h0 levelEleven_energy_40064
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39936 384 =
      171257077701900433001930976444996 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39936 256 128
      76565245173479678808949331092871 94691832528420754192981645352125 h1 levelEleven_energy_40192
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39936 512 =
      260006842100557091906941780577511 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39936 384 128
      171257077701900433001930976444996 88749764398656658905010804132515 h2 levelEleven_energy_40320
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_78 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 512 =
      5045527569454309031398889 := by
  have h0 := levelEleven_fractional_39936
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 256 =
      1980708914436780653323324 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 128 128
      1197391915226159653785323 783316999210620999538001 h0 levelEleven_fractional_40064
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 384 =
      3500079155458011462286819 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 256 128
      1980708914436780653323324 1519370241021230808963495 h1 levelEleven_fractional_40192
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 512 =
      5045527569454309031398889 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39936 384 128
      3500079155458011462286819 1545448413996297569112070 h2 levelEleven_fractional_40320
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_78 : ∀ i : Fin 512,
    levelEleven.lookup (39936 + i.val) ≤ levelElevenRoots.lookup (39936 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_39936
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39936 128 128
    h0 levelEleven_squares_40064
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39936 256 128
    h1 levelEleven_squares_40192
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39936 384 128
    h2 levelEleven_squares_40320
  exact h3

end WordCertDensity.Certificates
