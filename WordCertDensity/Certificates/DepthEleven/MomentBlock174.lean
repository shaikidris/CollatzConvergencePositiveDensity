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
theorem levelEleven_energy_89088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89088 128 =
      91705398416645418995638485599626 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 128 =
      1665413912544861688116244 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89088 : ∀ i : Fin 128,
    levelEleven.lookup (89088 + i.val) ≤ levelElevenRoots.lookup (89088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89216 128 =
      26131091506215524137394357215095 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89216 128 =
      836369718544023644626848 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89216 : ∀ i : Fin 128,
    levelEleven.lookup (89216 + i.val) ≤ levelElevenRoots.lookup (89216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89344 128 =
      45327864552899960099330533629376 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89344 128 =
      1145403631351500381258099 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89344 : ∀ i : Fin 128,
    levelEleven.lookup (89344 + i.val) ≤ levelElevenRoots.lookup (89344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89472 128 =
      113885789325977121898487992937353 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89472 128 =
      1837650209187350025891398 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89472 : ∀ i : Fin 128,
    levelEleven.lookup (89472 + i.val) ≤ levelElevenRoots.lookup (89472 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_174 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89088 512 =
      277050143801738025130851369381450 := by
  have h0 := levelEleven_energy_89088
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89088 256 =
      117836489922860943133032842814721 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89088 128 128
      91705398416645418995638485599626 26131091506215524137394357215095 h0 levelEleven_energy_89216
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89088 384 =
      163164354475760903232363376444097 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89088 256 128
      117836489922860943133032842814721 45327864552899960099330533629376 h1 levelEleven_energy_89344
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89088 512 =
      277050143801738025130851369381450 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89088 384 128
      163164354475760903232363376444097 113885789325977121898487992937353 h2 levelEleven_energy_89472
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_174 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 512 =
      5484837471627735739892589 := by
  have h0 := levelEleven_fractional_89088
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 256 =
      2501783631088885332743092 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 128 128
      1665413912544861688116244 836369718544023644626848 h0 levelEleven_fractional_89216
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 384 =
      3647187262440385714001191 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 256 128
      2501783631088885332743092 1145403631351500381258099 h1 levelEleven_fractional_89344
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 512 =
      5484837471627735739892589 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89088 384 128
      3647187262440385714001191 1837650209187350025891398 h2 levelEleven_fractional_89472
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_174 : ∀ i : Fin 512,
    levelEleven.lookup (89088 + i.val) ≤ levelElevenRoots.lookup (89088 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_89088
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89088 128 128
    h0 levelEleven_squares_89216
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89088 256 128
    h1 levelEleven_squares_89344
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89088 384 128
    h2 levelEleven_squares_89472
  exact h3

end WordCertDensity.Certificates
