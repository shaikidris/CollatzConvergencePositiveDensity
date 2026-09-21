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
theorem levelEleven_energy_18432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18432 128 =
      34079115709613550605453278076509 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 128 =
      966657924787461221829718 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18432 : ∀ i : Fin 128,
    levelEleven.lookup (18432 + i.val) ≤ levelElevenRoots.lookup (18432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18560 128 =
      35624525926521044235525660497464 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18560 128 =
      1047737620484110206359413 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18560 : ∀ i : Fin 128,
    levelEleven.lookup (18560 + i.val) ≤ levelElevenRoots.lookup (18560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18688 128 =
      21525523109705609996931306478775 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18688 128 =
      757303352475647458673373 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18688 : ∀ i : Fin 128,
    levelEleven.lookup (18688 + i.val) ≤ levelElevenRoots.lookup (18688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18816 128 =
      231063395145224540290164502979652 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18816 128 =
      2550864499378856412760259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18816 : ∀ i : Fin 128,
    levelEleven.lookup (18816 + i.val) ≤ levelElevenRoots.lookup (18816 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_36 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18432 512 =
      322292559891064745128074748032400 := by
  have h0 := levelEleven_energy_18432
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18432 256 =
      69703641636134594840978938573973 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18432 128 128
      34079115709613550605453278076509 35624525926521044235525660497464 h0 levelEleven_energy_18560
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18432 384 =
      91229164745840204837910245052748 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18432 256 128
      69703641636134594840978938573973 21525523109705609996931306478775 h1 levelEleven_energy_18688
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18432 512 =
      322292559891064745128074748032400 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18432 384 128
      91229164745840204837910245052748 231063395145224540290164502979652 h2 levelEleven_energy_18816
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_36 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 512 =
      5322563397126075299622763 := by
  have h0 := levelEleven_fractional_18432
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 256 =
      2014395545271571428189131 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 128 128
      966657924787461221829718 1047737620484110206359413 h0 levelEleven_fractional_18560
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 384 =
      2771698897747218886862504 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 256 128
      2014395545271571428189131 757303352475647458673373 h1 levelEleven_fractional_18688
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 512 =
      5322563397126075299622763 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18432 384 128
      2771698897747218886862504 2550864499378856412760259 h2 levelEleven_fractional_18816
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_36 : ∀ i : Fin 512,
    levelEleven.lookup (18432 + i.val) ≤ levelElevenRoots.lookup (18432 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_18432
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18432 128 128
    h0 levelEleven_squares_18560
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18432 256 128
    h1 levelEleven_squares_18688
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18432 384 128
    h2 levelEleven_squares_18816
  exact h3

end WordCertDensity.Certificates
