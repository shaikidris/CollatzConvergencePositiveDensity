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
theorem levelEleven_energy_17920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17920 128 =
      83012884442970839398098385724245 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_17920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 128 =
      1489041935433937460791723 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_17920 : ∀ i : Fin 128,
    levelEleven.lookup (17920 + i.val) ≤ levelElevenRoots.lookup (17920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18048 128 =
      36750817210181064010486421434560 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18048 128 =
      972651947322362763555204 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18048 : ∀ i : Fin 128,
    levelEleven.lookup (18048 + i.val) ≤ levelElevenRoots.lookup (18048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18176 128 =
      22768467122335484689805383034484 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18176 128 =
      749695160987184435288465 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18176 : ∀ i : Fin 128,
    levelEleven.lookup (18176 + i.val) ≤ levelElevenRoots.lookup (18176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_18304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18304 128 =
      53260405897268512725500931605914 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18304 128 =
      1225427656571714716628094 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18304 : ∀ i : Fin 128,
    levelEleven.lookup (18304 + i.val) ≤ levelElevenRoots.lookup (18304 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_35 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 17920 512 =
      195792574672755900823891121799203 := by
  have h0 := levelEleven_energy_17920
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17920 256 =
      119763701653151903408584807158805 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17920 128 128
      83012884442970839398098385724245 36750817210181064010486421434560 h0 levelEleven_energy_18048
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17920 384 =
      142532168775487388098390190193289 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17920 256 128
      119763701653151903408584807158805 22768467122335484689805383034484 h1 levelEleven_energy_18176
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 17920 512 =
      195792574672755900823891121799203 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 17920 384 128
      142532168775487388098390190193289 53260405897268512725500931605914 h2 levelEleven_energy_18304
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_35 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 512 =
      4436816700315199376263486 := by
  have h0 := levelEleven_fractional_17920
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 256 =
      2461693882756300224346927 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 128 128
      1489041935433937460791723 972651947322362763555204 h0 levelEleven_fractional_18048
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 384 =
      3211389043743484659635392 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 256 128
      2461693882756300224346927 749695160987184435288465 h1 levelEleven_fractional_18176
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 512 =
      4436816700315199376263486 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 17920 384 128
      3211389043743484659635392 1225427656571714716628094 h2 levelEleven_fractional_18304
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_35 : ∀ i : Fin 512,
    levelEleven.lookup (17920 + i.val) ≤ levelElevenRoots.lookup (17920 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_17920
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17920 128 128
    h0 levelEleven_squares_18048
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17920 256 128
    h1 levelEleven_squares_18176
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 17920 384 128
    h2 levelEleven_squares_18304
  exact h3

end WordCertDensity.Certificates
