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
theorem levelEleven_energy_72704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72704 128 =
      30075606237260733241580295438548 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 128 =
      900495268258263021303947 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72704 : ∀ i : Fin 128,
    levelEleven.lookup (72704 + i.val) ≤ levelElevenRoots.lookup (72704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72832 128 =
      68244731742688703866459821688716 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72832 128 =
      1360607348162552068097349 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72832 : ∀ i : Fin 128,
    levelEleven.lookup (72832 + i.val) ≤ levelElevenRoots.lookup (72832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_72960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72960 128 =
      53602982019362552101260583683344 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_72960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72960 128 =
      1295885602366619545806418 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_72960 : ∀ i : Fin 128,
    levelEleven.lookup (72960 + i.val) ≤ levelElevenRoots.lookup (72960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73088 128 =
      23170494691646399669852320008299 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73088 128 =
      751487100835613018565061 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73088 : ∀ i : Fin 128,
    levelEleven.lookup (73088 + i.val) ≤ levelElevenRoots.lookup (73088 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_142 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 72704 512 =
      175093814690958388879153020818907 := by
  have h0 := levelEleven_energy_72704
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72704 256 =
      98320337979949437108040117127264 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72704 128 128
      30075606237260733241580295438548 68244731742688703866459821688716 h0 levelEleven_energy_72832
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72704 384 =
      151923319999311989209300700810608 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72704 256 128
      98320337979949437108040117127264 53602982019362552101260583683344 h1 levelEleven_energy_72960
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 72704 512 =
      175093814690958388879153020818907 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 72704 384 128
      151923319999311989209300700810608 23170494691646399669852320008299 h2 levelEleven_energy_73088
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_142 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 512 =
      4308475319623047653772775 := by
  have h0 := levelEleven_fractional_72704
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 256 =
      2261102616420815089401296 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 128 128
      900495268258263021303947 1360607348162552068097349 h0 levelEleven_fractional_72832
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 384 =
      3556988218787434635207714 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 256 128
      2261102616420815089401296 1295885602366619545806418 h1 levelEleven_fractional_72960
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 512 =
      4308475319623047653772775 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 72704 384 128
      3556988218787434635207714 751487100835613018565061 h2 levelEleven_fractional_73088
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_142 : ∀ i : Fin 512,
    levelEleven.lookup (72704 + i.val) ≤ levelElevenRoots.lookup (72704 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_72704
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72704 128 128
    h0 levelEleven_squares_72832
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72704 256 128
    h1 levelEleven_squares_72960
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 72704 384 128
    h2 levelEleven_squares_73088
  exact h3

end WordCertDensity.Certificates
