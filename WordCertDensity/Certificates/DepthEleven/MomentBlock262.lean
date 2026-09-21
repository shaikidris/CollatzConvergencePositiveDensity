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
theorem levelEleven_energy_134144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134144 128 =
      31931083021167857307739747017426 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 128 =
      840727566362163697610400 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134144 : ∀ i : Fin 128,
    levelEleven.lookup (134144 + i.val) ≤ levelElevenRoots.lookup (134144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134272 128 =
      79801456258499714640979440388976 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134272 128 =
      1583186053479401553537597 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134272 : ∀ i : Fin 128,
    levelEleven.lookup (134272 + i.val) ≤ levelElevenRoots.lookup (134272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134400 128 =
      29350776835224354755732586042886 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134400 128 =
      837328537069809941774928 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134400 : ∀ i : Fin 128,
    levelEleven.lookup (134400 + i.val) ≤ levelElevenRoots.lookup (134400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134528 128 =
      20740365089990226770760613162663 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134528 128 =
      765442333070109358692045 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134528 : ∀ i : Fin 128,
    levelEleven.lookup (134528 + i.val) ≤ levelElevenRoots.lookup (134528 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_262 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134144 512 =
      161823681204882153475212386611951 := by
  have h0 := levelEleven_energy_134144
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134144 256 =
      111732539279667571948719187406402 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134144 128 128
      31931083021167857307739747017426 79801456258499714640979440388976 h0 levelEleven_energy_134272
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134144 384 =
      141083316114891926704451773449288 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134144 256 128
      111732539279667571948719187406402 29350776835224354755732586042886 h1 levelEleven_energy_134400
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134144 512 =
      161823681204882153475212386611951 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134144 384 128
      141083316114891926704451773449288 20740365089990226770760613162663 h2 levelEleven_energy_134528
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_262 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 512 =
      4026684489981484551614970 := by
  have h0 := levelEleven_fractional_134144
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 256 =
      2423913619841565251147997 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 128 128
      840727566362163697610400 1583186053479401553537597 h0 levelEleven_fractional_134272
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 384 =
      3261242156911375192922925 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 256 128
      2423913619841565251147997 837328537069809941774928 h1 levelEleven_fractional_134400
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 512 =
      4026684489981484551614970 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134144 384 128
      3261242156911375192922925 765442333070109358692045 h2 levelEleven_fractional_134528
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_262 : ∀ i : Fin 512,
    levelEleven.lookup (134144 + i.val) ≤ levelElevenRoots.lookup (134144 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_134144
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134144 128 128
    h0 levelEleven_squares_134272
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134144 256 128
    h1 levelEleven_squares_134400
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134144 384 128
    h2 levelEleven_squares_134528
  exact h3

end WordCertDensity.Certificates
