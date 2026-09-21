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
theorem levelEleven_energy_116736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116736 128 =
      34003124669453632211383127675032 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 128 =
      968685444380084322417357 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116736 : ∀ i : Fin 128,
    levelEleven.lookup (116736 + i.val) ≤ levelElevenRoots.lookup (116736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116864 128 =
      33741518048940765318756761942665 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116864 128 =
      977204263981616244142906 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116864 : ∀ i : Fin 128,
    levelEleven.lookup (116864 + i.val) ≤ levelElevenRoots.lookup (116864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116992 128 =
      38201612272109601017054845701985 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116992 128 =
      1021842788492176501180750 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116992 : ∀ i : Fin 128,
    levelEleven.lookup (116992 + i.val) ≤ levelElevenRoots.lookup (116992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_117120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117120 128 =
      23159276398390175139176750772389 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117120 128 =
      780729965860621510175879 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117120 : ∀ i : Fin 128,
    levelEleven.lookup (117120 + i.val) ≤ levelElevenRoots.lookup (117120 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_228 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116736 512 =
      129105531388894173686371486092071 := by
  have h0 := levelEleven_energy_116736
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116736 256 =
      67744642718394397530139889617697 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116736 128 128
      34003124669453632211383127675032 33741518048940765318756761942665 h0 levelEleven_energy_116864
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116736 384 =
      105946254990503998547194735319682 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116736 256 128
      67744642718394397530139889617697 38201612272109601017054845701985 h1 levelEleven_energy_116992
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116736 512 =
      129105531388894173686371486092071 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116736 384 128
      105946254990503998547194735319682 23159276398390175139176750772389 h2 levelEleven_energy_117120
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_228 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 512 =
      3748462462714498577916892 := by
  have h0 := levelEleven_fractional_116736
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 256 =
      1945889708361700566560263 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 128 128
      968685444380084322417357 977204263981616244142906 h0 levelEleven_fractional_116864
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 384 =
      2967732496853877067741013 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 256 128
      1945889708361700566560263 1021842788492176501180750 h1 levelEleven_fractional_116992
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 512 =
      3748462462714498577916892 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116736 384 128
      2967732496853877067741013 780729965860621510175879 h2 levelEleven_fractional_117120
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_228 : ∀ i : Fin 512,
    levelEleven.lookup (116736 + i.val) ≤ levelElevenRoots.lookup (116736 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_116736
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116736 128 128
    h0 levelEleven_squares_116864
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116736 256 128
    h1 levelEleven_squares_116992
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116736 384 128
    h2 levelEleven_squares_117120
  exact h3

end WordCertDensity.Certificates
