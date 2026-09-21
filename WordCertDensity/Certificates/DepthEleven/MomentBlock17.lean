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
theorem levelEleven_energy_8704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8704 128 =
      82739047509114299611860293315940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 128 =
      1402939386610509282301275 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8704 : ∀ i : Fin 128,
    levelEleven.lookup (8704 + i.val) ≤ levelElevenRoots.lookup (8704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8832 128 =
      52880647970971935780539251117710 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8832 128 =
      1324733024240517317128148 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8832 : ∀ i : Fin 128,
    levelEleven.lookup (8832 + i.val) ≤ levelElevenRoots.lookup (8832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8960 128 =
      40915382559689907944628561569637 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8960 128 =
      1082575548774954862104346 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8960 : ∀ i : Fin 128,
    levelEleven.lookup (8960 + i.val) ≤ levelElevenRoots.lookup (8960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9088 128 =
      65719112560776241704693633480729 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9088 128 =
      1435109977271978684238439 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9088 : ∀ i : Fin 128,
    levelEleven.lookup (9088 + i.val) ≤ levelElevenRoots.lookup (9088 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_17 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8704 512 =
      242254190600552385041721739484016 := by
  have h0 := levelEleven_energy_8704
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8704 256 =
      135619695480086235392399544433650 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8704 128 128
      82739047509114299611860293315940 52880647970971935780539251117710 h0 levelEleven_energy_8832
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8704 384 =
      176535078039776143337028106003287 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8704 256 128
      135619695480086235392399544433650 40915382559689907944628561569637 h1 levelEleven_energy_8960
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8704 512 =
      242254190600552385041721739484016 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8704 384 128
      176535078039776143337028106003287 65719112560776241704693633480729 h2 levelEleven_energy_9088
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_17 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 512 =
      5245357936897960145772208 := by
  have h0 := levelEleven_fractional_8704
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 256 =
      2727672410851026599429423 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 128 128
      1402939386610509282301275 1324733024240517317128148 h0 levelEleven_fractional_8832
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 384 =
      3810247959625981461533769 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 256 128
      2727672410851026599429423 1082575548774954862104346 h1 levelEleven_fractional_8960
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 512 =
      5245357936897960145772208 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8704 384 128
      3810247959625981461533769 1435109977271978684238439 h2 levelEleven_fractional_9088
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_17 : ∀ i : Fin 512,
    levelEleven.lookup (8704 + i.val) ≤ levelElevenRoots.lookup (8704 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_8704
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8704 128 128
    h0 levelEleven_squares_8832
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8704 256 128
    h1 levelEleven_squares_8960
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8704 384 128
    h2 levelEleven_squares_9088
  exact h3

end WordCertDensity.Certificates
