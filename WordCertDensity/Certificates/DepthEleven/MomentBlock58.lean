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
theorem levelEleven_energy_29696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29696 128 =
      51040584866643456278097725428038 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 128 =
      1273893575681481310135540 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29696 : ∀ i : Fin 128,
    levelEleven.lookup (29696 + i.val) ≤ levelElevenRoots.lookup (29696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29824 128 =
      41829781624405380362065143736068 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29824 128 =
      1004963501418121083675052 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29824 : ∀ i : Fin 128,
    levelEleven.lookup (29824 + i.val) ≤ levelElevenRoots.lookup (29824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29952 128 =
      47145108740923177669826478633776 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29952 128 =
      1207510690262567102042733 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29952 : ∀ i : Fin 128,
    levelEleven.lookup (29952 + i.val) ≤ levelElevenRoots.lookup (29952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30080 128 =
      21689614464069726016977434825940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30080 128 =
      714291157067157051129839 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30080 : ∀ i : Fin 128,
    levelEleven.lookup (30080 + i.val) ≤ levelElevenRoots.lookup (30080 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_58 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29696 512 =
      161705089696041740326966782623822 := by
  have h0 := levelEleven_energy_29696
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29696 256 =
      92870366491048836640162869164106 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29696 128 128
      51040584866643456278097725428038 41829781624405380362065143736068 h0 levelEleven_energy_29824
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29696 384 =
      140015475231972014309989347797882 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29696 256 128
      92870366491048836640162869164106 47145108740923177669826478633776 h1 levelEleven_energy_29952
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29696 512 =
      161705089696041740326966782623822 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29696 384 128
      140015475231972014309989347797882 21689614464069726016977434825940 h2 levelEleven_energy_30080
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_58 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 512 =
      4200658924429326546983164 := by
  have h0 := levelEleven_fractional_29696
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 256 =
      2278857077099602393810592 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 128 128
      1273893575681481310135540 1004963501418121083675052 h0 levelEleven_fractional_29824
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 384 =
      3486367767362169495853325 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 256 128
      2278857077099602393810592 1207510690262567102042733 h1 levelEleven_fractional_29952
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 512 =
      4200658924429326546983164 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29696 384 128
      3486367767362169495853325 714291157067157051129839 h2 levelEleven_fractional_30080
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_58 : ∀ i : Fin 512,
    levelEleven.lookup (29696 + i.val) ≤ levelElevenRoots.lookup (29696 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_29696
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29696 128 128
    h0 levelEleven_squares_29824
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29696 256 128
    h1 levelEleven_squares_29952
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29696 384 128
    h2 levelEleven_squares_30080
  exact h3

end WordCertDensity.Certificates
