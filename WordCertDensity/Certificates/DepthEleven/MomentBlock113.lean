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
theorem levelEleven_energy_57856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57856 128 =
      17595157075438127554845638234850 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 128 =
      649367026788213418572906 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57856 : ∀ i : Fin 128,
    levelEleven.lookup (57856 + i.val) ≤ levelElevenRoots.lookup (57856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57984 128 =
      28313247389688261784664866781848 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57984 128 =
      898450791972151190515291 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57984 : ∀ i : Fin 128,
    levelEleven.lookup (57984 + i.val) ≤ levelElevenRoots.lookup (57984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_58112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58112 128 =
      38908272402952507464755673000144 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58112 128 =
      1043194887460171486843701 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58112 : ∀ i : Fin 128,
    levelEleven.lookup (58112 + i.val) ≤ levelElevenRoots.lookup (58112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_58240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 58240 128 =
      31350398867778466538984538061080 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_58240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 58240 128 =
      922506344177950882928507 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_58240 : ∀ i : Fin 128,
    levelEleven.lookup (58240 + i.val) ≤ levelElevenRoots.lookup (58240 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_113 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57856 512 =
      116167075735857363343250716077922 := by
  have h0 := levelEleven_energy_57856
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57856 256 =
      45908404465126389339510505016698 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57856 128 128
      17595157075438127554845638234850 28313247389688261784664866781848 h0 levelEleven_energy_57984
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57856 384 =
      84816676868078896804266178016842 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57856 256 128
      45908404465126389339510505016698 38908272402952507464755673000144 h1 levelEleven_energy_58112
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57856 512 =
      116167075735857363343250716077922 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57856 384 128
      84816676868078896804266178016842 31350398867778466538984538061080 h2 levelEleven_energy_58240
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_113 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 512 =
      3513519050398486978860405 := by
  have h0 := levelEleven_fractional_57856
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 256 =
      1547817818760364609088197 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 128 128
      649367026788213418572906 898450791972151190515291 h0 levelEleven_fractional_57984
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 384 =
      2591012706220536095931898 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 256 128
      1547817818760364609088197 1043194887460171486843701 h1 levelEleven_fractional_58112
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 512 =
      3513519050398486978860405 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57856 384 128
      2591012706220536095931898 922506344177950882928507 h2 levelEleven_fractional_58240
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_113 : ∀ i : Fin 512,
    levelEleven.lookup (57856 + i.val) ≤ levelElevenRoots.lookup (57856 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_57856
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57856 128 128
    h0 levelEleven_squares_57984
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57856 256 128
    h1 levelEleven_squares_58112
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57856 384 128
    h2 levelEleven_squares_58240
  exact h3

end WordCertDensity.Certificates
