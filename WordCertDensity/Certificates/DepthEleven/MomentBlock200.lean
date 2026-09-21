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
theorem levelEleven_energy_102400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102400 128 =
      30841494367973693630143766891166 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 128 =
      968642381008841176536591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102400 : ∀ i : Fin 128,
    levelEleven.lookup (102400 + i.val) ≤ levelElevenRoots.lookup (102400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102528 128 =
      26072974211514511780339837621722 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102528 128 =
      838839619281049194269056 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102528 : ∀ i : Fin 128,
    levelEleven.lookup (102528 + i.val) ≤ levelElevenRoots.lookup (102528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102656 128 =
      100551842926130830569230986498308 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102656 128 =
      1795168170165451416199045 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102656 : ∀ i : Fin 128,
    levelEleven.lookup (102656 + i.val) ≤ levelElevenRoots.lookup (102656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102784 128 =
      20323437777773306781862695467589 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102784 128 =
      682693182002672757425223 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102784 : ∀ i : Fin 128,
    levelEleven.lookup (102784 + i.val) ≤ levelElevenRoots.lookup (102784 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102400 512 =
      177789749283392342761577286478785 := by
  have h0 := levelEleven_energy_102400
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102400 256 =
      56914468579488205410483604512888 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102400 128 128
      30841494367973693630143766891166 26072974211514511780339837621722 h0 levelEleven_energy_102528
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102400 384 =
      157466311505619035979714591011196 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102400 256 128
      56914468579488205410483604512888 100551842926130830569230986498308 h1 levelEleven_energy_102656
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102400 512 =
      177789749283392342761577286478785 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102400 384 128
      157466311505619035979714591011196 20323437777773306781862695467589 h2 levelEleven_energy_102784
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 512 =
      4285343352458014544429915 := by
  have h0 := levelEleven_fractional_102400
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 256 =
      1807482000289890370805647 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 128 128
      968642381008841176536591 838839619281049194269056 h0 levelEleven_fractional_102528
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 384 =
      3602650170455341787004692 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 256 128
      1807482000289890370805647 1795168170165451416199045 h1 levelEleven_fractional_102656
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 512 =
      4285343352458014544429915 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102400 384 128
      3602650170455341787004692 682693182002672757425223 h2 levelEleven_fractional_102784
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_200 : ∀ i : Fin 512,
    levelEleven.lookup (102400 + i.val) ≤ levelElevenRoots.lookup (102400 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_102400
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102400 128 128
    h0 levelEleven_squares_102528
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102400 256 128
    h1 levelEleven_squares_102656
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102400 384 128
    h2 levelEleven_squares_102784
  exact h3

end WordCertDensity.Certificates
