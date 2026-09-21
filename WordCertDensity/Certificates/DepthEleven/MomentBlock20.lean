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
theorem levelEleven_energy_10240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10240 128 =
      37827123039908658988801913409171 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 128 =
      920361390639306395802114 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10240 : ∀ i : Fin 128,
    levelEleven.lookup (10240 + i.val) ≤ levelElevenRoots.lookup (10240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_10368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10368 128 =
      82049140505294810458608290538298 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10368 128 =
      1557260358981665961226597 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10368 : ∀ i : Fin 128,
    levelEleven.lookup (10368 + i.val) ≤ levelElevenRoots.lookup (10368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_10496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10496 128 =
      54689859752300804648785404587473 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10496 128 =
      1258913492647925348076619 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10496 : ∀ i : Fin 128,
    levelEleven.lookup (10496 + i.val) ≤ levelElevenRoots.lookup (10496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_10624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10624 128 =
      38281665749947771112576093416265 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10624 128 =
      1062973012807512775822557 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10624 : ∀ i : Fin 128,
    levelEleven.lookup (10624 + i.val) ≤ levelElevenRoots.lookup (10624 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_20 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10240 512 =
      212847789047452045208771701951207 := by
  have h0 := levelEleven_energy_10240
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10240 256 =
      119876263545203469447410203947469 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10240 128 128
      37827123039908658988801913409171 82049140505294810458608290538298 h0 levelEleven_energy_10368
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10240 384 =
      174566123297504274096195608534942 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10240 256 128
      119876263545203469447410203947469 54689859752300804648785404587473 h1 levelEleven_energy_10496
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 10240 512 =
      212847789047452045208771701951207 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 10240 384 128
      174566123297504274096195608534942 38281665749947771112576093416265 h2 levelEleven_energy_10624
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_20 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 512 =
      4799508255076410480927887 := by
  have h0 := levelEleven_fractional_10240
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 256 =
      2477621749620972357028711 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 128 128
      920361390639306395802114 1557260358981665961226597 h0 levelEleven_fractional_10368
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 384 =
      3736535242268897705105330 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 256 128
      2477621749620972357028711 1258913492647925348076619 h1 levelEleven_fractional_10496
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 512 =
      4799508255076410480927887 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10240 384 128
      3736535242268897705105330 1062973012807512775822557 h2 levelEleven_fractional_10624
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_20 : ∀ i : Fin 512,
    levelEleven.lookup (10240 + i.val) ≤ levelElevenRoots.lookup (10240 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_10240
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10240 128 128
    h0 levelEleven_squares_10368
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10240 256 128
    h1 levelEleven_squares_10496
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 10240 384 128
    h2 levelEleven_squares_10624
  exact h3

end WordCertDensity.Certificates
