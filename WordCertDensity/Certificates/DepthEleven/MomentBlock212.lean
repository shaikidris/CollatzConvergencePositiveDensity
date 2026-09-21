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
theorem levelEleven_energy_108544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108544 128 =
      60874673636026053197013977962294 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 128 =
      1319723044701776285882598 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108544 : ∀ i : Fin 128,
    levelEleven.lookup (108544 + i.val) ≤ levelElevenRoots.lookup (108544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108672 128 =
      54974646684895870778888827912060 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108672 128 =
      1277952769638273725658605 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108672 : ∀ i : Fin 128,
    levelEleven.lookup (108672 + i.val) ≤ levelElevenRoots.lookup (108672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108800 128 =
      59571374249691672473843315535158 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108800 128 =
      1312707544387130695449341 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108800 : ∀ i : Fin 128,
    levelEleven.lookup (108800 + i.val) ≤ levelElevenRoots.lookup (108800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_108928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108928 128 =
      41442725251895464130312839677371 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_108928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108928 128 =
      1138723649520855984201814 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_108928 : ∀ i : Fin 128,
    levelEleven.lookup (108928 + i.val) ≤ levelElevenRoots.lookup (108928 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_212 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 108544 512 =
      216863419822509060580058961086883 := by
  have h0 := levelEleven_energy_108544
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108544 256 =
      115849320320921923975902805874354 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108544 128 128
      60874673636026053197013977962294 54974646684895870778888827912060 h0 levelEleven_energy_108672
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108544 384 =
      175420694570613596449746121409512 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108544 256 128
      115849320320921923975902805874354 59571374249691672473843315535158 h1 levelEleven_energy_108800
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 108544 512 =
      216863419822509060580058961086883 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 108544 384 128
      175420694570613596449746121409512 41442725251895464130312839677371 h2 levelEleven_energy_108928
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_212 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 512 =
      5049107008248036691192358 := by
  have h0 := levelEleven_fractional_108544
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 256 =
      2597675814340050011541203 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 128 128
      1319723044701776285882598 1277952769638273725658605 h0 levelEleven_fractional_108672
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 384 =
      3910383358727180706990544 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 256 128
      2597675814340050011541203 1312707544387130695449341 h1 levelEleven_fractional_108800
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 512 =
      5049107008248036691192358 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 108544 384 128
      3910383358727180706990544 1138723649520855984201814 h2 levelEleven_fractional_108928
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_212 : ∀ i : Fin 512,
    levelEleven.lookup (108544 + i.val) ≤ levelElevenRoots.lookup (108544 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_108544
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108544 128 128
    h0 levelEleven_squares_108672
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108544 256 128
    h1 levelEleven_squares_108800
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 108544 384 128
    h2 levelEleven_squares_108928
  exact h3

end WordCertDensity.Certificates
