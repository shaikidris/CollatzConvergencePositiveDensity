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
theorem levelEleven_energy_174080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174080 128 =
      31754132135160541549726972648830 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 128 =
      950643877022589638430985 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174080 : ∀ i : Fin 128,
    levelEleven.lookup (174080 + i.val) ≤ levelElevenRoots.lookup (174080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174208 128 =
      69167301613640536648178519564083 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174208 128 =
      1269344196891081878482702 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174208 : ∀ i : Fin 128,
    levelEleven.lookup (174208 + i.val) ≤ levelElevenRoots.lookup (174208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174336 128 =
      43318306989898583114553000174892 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174336 128 =
      1118540364926641024810905 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174336 : ∀ i : Fin 128,
    levelEleven.lookup (174336 + i.val) ≤ levelElevenRoots.lookup (174336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174464 128 =
      30150775192405114876225079542400 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174464 128 =
      925811127336722484142560 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174464 : ∀ i : Fin 128,
    levelEleven.lookup (174464 + i.val) ≤ levelElevenRoots.lookup (174464 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_340 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174080 512 =
      174390515931104776188683571930205 := by
  have h0 := levelEleven_energy_174080
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174080 256 =
      100921433748801078197905492212913 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174080 128 128
      31754132135160541549726972648830 69167301613640536648178519564083 h0 levelEleven_energy_174208
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174080 384 =
      144239740738699661312458492387805 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174080 256 128
      100921433748801078197905492212913 43318306989898583114553000174892 h1 levelEleven_energy_174336
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174080 512 =
      174390515931104776188683571930205 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174080 384 128
      144239740738699661312458492387805 30150775192405114876225079542400 h2 levelEleven_energy_174464
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_340 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 512 =
      4264339566177035025867152 := by
  have h0 := levelEleven_fractional_174080
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 256 =
      2219988073913671516913687 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 128 128
      950643877022589638430985 1269344196891081878482702 h0 levelEleven_fractional_174208
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 384 =
      3338528438840312541724592 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 256 128
      2219988073913671516913687 1118540364926641024810905 h1 levelEleven_fractional_174336
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 512 =
      4264339566177035025867152 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174080 384 128
      3338528438840312541724592 925811127336722484142560 h2 levelEleven_fractional_174464
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_340 : ∀ i : Fin 512,
    levelEleven.lookup (174080 + i.val) ≤ levelElevenRoots.lookup (174080 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_174080
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174080 128 128
    h0 levelEleven_squares_174208
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174080 256 128
    h1 levelEleven_squares_174336
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174080 384 128
    h2 levelEleven_squares_174464
  exact h3

end WordCertDensity.Certificates
