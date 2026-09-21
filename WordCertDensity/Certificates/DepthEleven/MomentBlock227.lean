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
theorem levelEleven_energy_116224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116224 128 =
      39221830020007995052537817105693 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 128 =
      1175834594272557716298975 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116224 : ∀ i : Fin 128,
    levelEleven.lookup (116224 + i.val) ≤ levelElevenRoots.lookup (116224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116352 128 =
      38249937844492835128091241513507 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116352 128 =
      977830718568656449112539 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116352 : ∀ i : Fin 128,
    levelEleven.lookup (116352 + i.val) ≤ levelElevenRoots.lookup (116352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116480 128 =
      29758273354226948944024560548516 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116480 128 =
      884730954680202423575774 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116480 : ∀ i : Fin 128,
    levelEleven.lookup (116480 + i.val) ≤ levelElevenRoots.lookup (116480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116608 128 =
      26263922332754401779304182361802 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116608 128 =
      793125542843248134031407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116608 : ∀ i : Fin 128,
    levelEleven.lookup (116608 + i.val) ≤ levelElevenRoots.lookup (116608 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_227 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116224 512 =
      133493963551482180903957801529518 := by
  have h0 := levelEleven_energy_116224
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116224 256 =
      77471767864500830180629058619200 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116224 128 128
      39221830020007995052537817105693 38249937844492835128091241513507 h0 levelEleven_energy_116352
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116224 384 =
      107230041218727779124653619167716 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116224 256 128
      77471767864500830180629058619200 29758273354226948944024560548516 h1 levelEleven_energy_116480
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 116224 512 =
      133493963551482180903957801529518 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 116224 384 128
      107230041218727779124653619167716 26263922332754401779304182361802 h2 levelEleven_energy_116608
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_227 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 512 =
      3831521810364664723018695 := by
  have h0 := levelEleven_fractional_116224
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 256 =
      2153665312841214165411514 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 128 128
      1175834594272557716298975 977830718568656449112539 h0 levelEleven_fractional_116352
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 384 =
      3038396267521416588987288 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 256 128
      2153665312841214165411514 884730954680202423575774 h1 levelEleven_fractional_116480
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 512 =
      3831521810364664723018695 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116224 384 128
      3038396267521416588987288 793125542843248134031407 h2 levelEleven_fractional_116608
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_227 : ∀ i : Fin 512,
    levelEleven.lookup (116224 + i.val) ≤ levelElevenRoots.lookup (116224 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_116224
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116224 128 128
    h0 levelEleven_squares_116352
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116224 256 128
    h1 levelEleven_squares_116480
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 116224 384 128
    h2 levelEleven_squares_116608
  exact h3

end WordCertDensity.Certificates
