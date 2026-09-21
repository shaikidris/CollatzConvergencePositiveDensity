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
theorem levelEleven_energy_175616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175616 128 =
      31995665008444659624975808946463 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 128 =
      867730491415279741207426 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175616 : ∀ i : Fin 128,
    levelEleven.lookup (175616 + i.val) ≤ levelElevenRoots.lookup (175616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_175744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175744 128 =
      33682002692481192829412408672782 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175744 128 =
      982879441647733193630317 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175744 : ∀ i : Fin 128,
    levelEleven.lookup (175744 + i.val) ≤ levelElevenRoots.lookup (175744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_175872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175872 128 =
      35997202523720138934255098870843 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175872 128 =
      990819127620607539461262 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175872 : ∀ i : Fin 128,
    levelEleven.lookup (175872 + i.val) ≤ levelElevenRoots.lookup (175872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176000 128 =
      28392299240101686730000919775787 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176000 128 =
      903537251583163082037414 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176000 : ∀ i : Fin 128,
    levelEleven.lookup (176000 + i.val) ≤ levelElevenRoots.lookup (176000 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_343 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175616 512 =
      130067169464747678118644236265875 := by
  have h0 := levelEleven_energy_175616
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175616 256 =
      65677667700925852454388217619245 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175616 128 128
      31995665008444659624975808946463 33682002692481192829412408672782 h0 levelEleven_energy_175744
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175616 384 =
      101674870224645991388643316490088 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175616 256 128
      65677667700925852454388217619245 35997202523720138934255098870843 h1 levelEleven_energy_175872
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175616 512 =
      130067169464747678118644236265875 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175616 384 128
      101674870224645991388643316490088 28392299240101686730000919775787 h2 levelEleven_energy_176000
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_343 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 512 =
      3744966312266783556336419 := by
  have h0 := levelEleven_fractional_175616
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 256 =
      1850609933063012934837743 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 128 128
      867730491415279741207426 982879441647733193630317 h0 levelEleven_fractional_175744
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 384 =
      2841429060683620474299005 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 256 128
      1850609933063012934837743 990819127620607539461262 h1 levelEleven_fractional_175872
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 512 =
      3744966312266783556336419 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175616 384 128
      2841429060683620474299005 903537251583163082037414 h2 levelEleven_fractional_176000
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_343 : ∀ i : Fin 512,
    levelEleven.lookup (175616 + i.val) ≤ levelElevenRoots.lookup (175616 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_175616
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175616 128 128
    h0 levelEleven_squares_175744
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175616 256 128
    h1 levelEleven_squares_175872
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175616 384 128
    h2 levelEleven_squares_176000
  exact h3

end WordCertDensity.Certificates
