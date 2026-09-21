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
theorem levelEleven_energy_151552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151552 128 =
      41500840821301257554141652242874 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 128 =
      1068295969859773147045355 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151552 : ∀ i : Fin 128,
    levelEleven.lookup (151552 + i.val) ≤ levelElevenRoots.lookup (151552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151680 128 =
      49135329127987641978382446107656 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151680 128 =
      1136281354021004891172327 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151680 : ∀ i : Fin 128,
    levelEleven.lookup (151680 + i.val) ≤ levelElevenRoots.lookup (151680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151808 128 =
      27739598895777282266046699816603 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151808 128 =
      838175521888639420463987 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151808 : ∀ i : Fin 128,
    levelEleven.lookup (151808 + i.val) ≤ levelElevenRoots.lookup (151808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151936 128 =
      83158747901205160678623399529879 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151936 128 =
      1516181153490243879766542 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151936 : ∀ i : Fin 128,
    levelEleven.lookup (151936 + i.val) ≤ levelElevenRoots.lookup (151936 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151552 512 =
      201534516746271342477194197697012 := by
  have h0 := levelEleven_energy_151552
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151552 256 =
      90636169949288899532524098350530 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151552 128 128
      41500840821301257554141652242874 49135329127987641978382446107656 h0 levelEleven_energy_151680
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151552 384 =
      118375768845066181798570798167133 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151552 256 128
      90636169949288899532524098350530 27739598895777282266046699816603 h1 levelEleven_energy_151808
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151552 512 =
      201534516746271342477194197697012 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151552 384 128
      118375768845066181798570798167133 83158747901205160678623399529879 h2 levelEleven_energy_151936
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 512 =
      4558933999259661338448211 := by
  have h0 := levelEleven_fractional_151552
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 256 =
      2204577323880778038217682 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 128 128
      1068295969859773147045355 1136281354021004891172327 h0 levelEleven_fractional_151680
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 384 =
      3042752845769417458681669 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 256 128
      2204577323880778038217682 838175521888639420463987 h1 levelEleven_fractional_151808
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 512 =
      4558933999259661338448211 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151552 384 128
      3042752845769417458681669 1516181153490243879766542 h2 levelEleven_fractional_151936
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_296 : ∀ i : Fin 512,
    levelEleven.lookup (151552 + i.val) ≤ levelElevenRoots.lookup (151552 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_151552
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151552 128 128
    h0 levelEleven_squares_151680
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151552 256 128
    h1 levelEleven_squares_151808
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151552 384 128
    h2 levelEleven_squares_151936
  exact h3

end WordCertDensity.Certificates
