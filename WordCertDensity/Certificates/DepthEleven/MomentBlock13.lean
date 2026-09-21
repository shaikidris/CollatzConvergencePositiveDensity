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
theorem levelEleven_energy_6656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6656 128 =
      64931685464631427546167955775243 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 128 =
      1455999708053842783683100 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6656 : ∀ i : Fin 128,
    levelEleven.lookup (6656 + i.val) ≤ levelElevenRoots.lookup (6656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6784 128 =
      50813290783682466766363978576503 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6784 128 =
      1244890956211004975547669 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6784 : ∀ i : Fin 128,
    levelEleven.lookup (6784 + i.val) ≤ levelElevenRoots.lookup (6784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6912 128 =
      25696617803971722461346545494650 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6912 128 =
      830568522018661163305185 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6912 : ∀ i : Fin 128,
    levelEleven.lookup (6912 + i.val) ≤ levelElevenRoots.lookup (6912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7040 128 =
      57164918318137990792636843570791 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7040 128 =
      1213050338617227090575120 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7040 : ∀ i : Fin 128,
    levelEleven.lookup (7040 + i.val) ≤ levelElevenRoots.lookup (7040 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_13 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6656 512 =
      198606512370423607566515323417187 := by
  have h0 := levelEleven_energy_6656
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6656 256 =
      115744976248313894312531934351746 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6656 128 128
      64931685464631427546167955775243 50813290783682466766363978576503 h0 levelEleven_energy_6784
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6656 384 =
      141441594052285616773878479846396 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6656 256 128
      115744976248313894312531934351746 25696617803971722461346545494650 h1 levelEleven_energy_6912
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6656 512 =
      198606512370423607566515323417187 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6656 384 128
      141441594052285616773878479846396 57164918318137990792636843570791 h2 levelEleven_energy_7040
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_13 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 512 =
      4744509524900736013111074 := by
  have h0 := levelEleven_fractional_6656
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 256 =
      2700890664264847759230769 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 128 128
      1455999708053842783683100 1244890956211004975547669 h0 levelEleven_fractional_6784
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 384 =
      3531459186283508922535954 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 256 128
      2700890664264847759230769 830568522018661163305185 h1 levelEleven_fractional_6912
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 512 =
      4744509524900736013111074 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6656 384 128
      3531459186283508922535954 1213050338617227090575120 h2 levelEleven_fractional_7040
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_13 : ∀ i : Fin 512,
    levelEleven.lookup (6656 + i.val) ≤ levelElevenRoots.lookup (6656 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_6656
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6656 128 128
    h0 levelEleven_squares_6784
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6656 256 128
    h1 levelEleven_squares_6912
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6656 384 128
    h2 levelEleven_squares_7040
  exact h3

end WordCertDensity.Certificates
