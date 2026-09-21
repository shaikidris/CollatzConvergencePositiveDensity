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
theorem levelEleven_energy_158208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158208 128 =
      19663259967460644029351757718640 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 128 =
      656102638562270649798447 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158208 : ∀ i : Fin 128,
    levelEleven.lookup (158208 + i.val) ≤ levelElevenRoots.lookup (158208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158336 128 =
      72948034108036310266436518490673 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158336 128 =
      1436875937444866354938046 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158336 : ∀ i : Fin 128,
    levelEleven.lookup (158336 + i.val) ≤ levelElevenRoots.lookup (158336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158464 128 =
      88307629538064178637670530096527 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158464 128 =
      1529956745071198118256985 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158464 : ∀ i : Fin 128,
    levelEleven.lookup (158464 + i.val) ≤ levelElevenRoots.lookup (158464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158592 128 =
      49775914453796027177026571531339 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158592 128 =
      1172294362385415471104876 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158592 : ∀ i : Fin 128,
    levelEleven.lookup (158592 + i.val) ≤ levelElevenRoots.lookup (158592 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_309 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158208 512 =
      230694838067357160110485377837179 := by
  have h0 := levelEleven_energy_158208
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158208 256 =
      92611294075496954295788276209313 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158208 128 128
      19663259967460644029351757718640 72948034108036310266436518490673 h0 levelEleven_energy_158336
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158208 384 =
      180918923613561132933458806305840 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158208 256 128
      92611294075496954295788276209313 88307629538064178637670530096527 h1 levelEleven_energy_158464
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 158208 512 =
      230694838067357160110485377837179 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 158208 384 128
      180918923613561132933458806305840 49775914453796027177026571531339 h2 levelEleven_energy_158592
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_309 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 512 =
      4795229683463750594098354 := by
  have h0 := levelEleven_fractional_158208
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 256 =
      2092978576007137004736493 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 128 128
      656102638562270649798447 1436875937444866354938046 h0 levelEleven_fractional_158336
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 384 =
      3622935321078335122993478 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 256 128
      2092978576007137004736493 1529956745071198118256985 h1 levelEleven_fractional_158464
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 512 =
      4795229683463750594098354 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158208 384 128
      3622935321078335122993478 1172294362385415471104876 h2 levelEleven_fractional_158592
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_309 : ∀ i : Fin 512,
    levelEleven.lookup (158208 + i.val) ≤ levelElevenRoots.lookup (158208 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_158208
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158208 128 128
    h0 levelEleven_squares_158336
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158208 256 128
    h1 levelEleven_squares_158464
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 158208 384 128
    h2 levelEleven_squares_158592
  exact h3

end WordCertDensity.Certificates
