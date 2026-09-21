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
theorem levelEleven_energy_99840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99840 128 =
      38773389425272629936291594044675 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 128 =
      945919909639209705434997 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99840 : ∀ i : Fin 128,
    levelEleven.lookup (99840 + i.val) ≤ levelElevenRoots.lookup (99840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_99968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99968 128 =
      133575511538460283000492763721596 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_99968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99968 128 =
      2174294207994762778120557 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_99968 : ∀ i : Fin 128,
    levelEleven.lookup (99968 + i.val) ≤ levelElevenRoots.lookup (99968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100096 128 =
      37318579542904570726019300837547 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100096 128 =
      1038392234841759391963846 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100096 : ∀ i : Fin 128,
    levelEleven.lookup (100096 + i.val) ≤ levelElevenRoots.lookup (100096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100224 128 =
      55676226264690153317363100214280 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100224 128 =
      1287583100262307060580318 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100224 : ∀ i : Fin 128,
    levelEleven.lookup (100224 + i.val) ≤ levelElevenRoots.lookup (100224 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_195 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 99840 512 =
      265343706771327636980166758818098 := by
  have h0 := levelEleven_energy_99840
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99840 256 =
      172348900963732912936784357766271 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99840 128 128
      38773389425272629936291594044675 133575511538460283000492763721596 h0 levelEleven_energy_99968
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99840 384 =
      209667480506637483662803658603818 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99840 256 128
      172348900963732912936784357766271 37318579542904570726019300837547 h1 levelEleven_energy_100096
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 99840 512 =
      265343706771327636980166758818098 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 99840 384 128
      209667480506637483662803658603818 55676226264690153317363100214280 h2 levelEleven_energy_100224
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_195 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 512 =
      5446189452738038936099718 := by
  have h0 := levelEleven_fractional_99840
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 256 =
      3120214117633972483555554 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 128 128
      945919909639209705434997 2174294207994762778120557 h0 levelEleven_fractional_99968
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 384 =
      4158606352475731875519400 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 256 128
      3120214117633972483555554 1038392234841759391963846 h1 levelEleven_fractional_100096
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 512 =
      5446189452738038936099718 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 99840 384 128
      4158606352475731875519400 1287583100262307060580318 h2 levelEleven_fractional_100224
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_195 : ∀ i : Fin 512,
    levelEleven.lookup (99840 + i.val) ≤ levelElevenRoots.lookup (99840 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_99840
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99840 128 128
    h0 levelEleven_squares_99968
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99840 256 128
    h1 levelEleven_squares_100096
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 99840 384 128
    h2 levelEleven_squares_100224
  exact h3

end WordCertDensity.Certificates
