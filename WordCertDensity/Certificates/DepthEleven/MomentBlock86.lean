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
theorem levelEleven_energy_44032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44032 128 =
      50716234115607695235355089079259 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 128 =
      1178412685434576446999403 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44032 : ∀ i : Fin 128,
    levelEleven.lookup (44032 + i.val) ≤ levelElevenRoots.lookup (44032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44160 128 =
      48691554005519220523162395481698 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44160 128 =
      1202468101382166127174441 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44160 : ∀ i : Fin 128,
    levelEleven.lookup (44160 + i.val) ≤ levelElevenRoots.lookup (44160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44288 128 =
      24268880751926968932146730723735 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44288 128 =
      798984439841901652569608 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44288 : ∀ i : Fin 128,
    levelEleven.lookup (44288 + i.val) ≤ levelElevenRoots.lookup (44288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44416 128 =
      28884105705240030674702864951486 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44416 128 =
      812336809825925594920927 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44416 : ∀ i : Fin 128,
    levelEleven.lookup (44416 + i.val) ≤ levelElevenRoots.lookup (44416 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_86 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44032 512 =
      152560774578293915365367080236178 := by
  have h0 := levelEleven_energy_44032
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44032 256 =
      99407788121126915758517484560957 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44032 128 128
      50716234115607695235355089079259 48691554005519220523162395481698 h0 levelEleven_energy_44160
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44032 384 =
      123676668873053884690664215284692 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44032 256 128
      99407788121126915758517484560957 24268880751926968932146730723735 h1 levelEleven_energy_44288
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44032 512 =
      152560774578293915365367080236178 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44032 384 128
      123676668873053884690664215284692 28884105705240030674702864951486 h2 levelEleven_energy_44416
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_86 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 512 =
      3992202036484569821664379 := by
  have h0 := levelEleven_fractional_44032
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 256 =
      2380880786816742574173844 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 128 128
      1178412685434576446999403 1202468101382166127174441 h0 levelEleven_fractional_44160
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 384 =
      3179865226658644226743452 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 256 128
      2380880786816742574173844 798984439841901652569608 h1 levelEleven_fractional_44288
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 512 =
      3992202036484569821664379 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44032 384 128
      3179865226658644226743452 812336809825925594920927 h2 levelEleven_fractional_44416
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_86 : ∀ i : Fin 512,
    levelEleven.lookup (44032 + i.val) ≤ levelElevenRoots.lookup (44032 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_44032
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44032 128 128
    h0 levelEleven_squares_44160
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44032 256 128
    h1 levelEleven_squares_44288
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44032 384 128
    h2 levelEleven_squares_44416
  exact h3

end WordCertDensity.Certificates
