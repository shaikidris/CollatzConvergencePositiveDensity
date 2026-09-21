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
theorem levelEleven_energy_175104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175104 128 =
      38990501075184807693481505420133 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 128 =
      1046735675677139835013967 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175104 : ∀ i : Fin 128,
    levelEleven.lookup (175104 + i.val) ≤ levelElevenRoots.lookup (175104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_175232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175232 128 =
      29803458486441148150042509798357 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175232 128 =
      905866525782859765273419 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175232 : ∀ i : Fin 128,
    levelEleven.lookup (175232 + i.val) ≤ levelElevenRoots.lookup (175232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_175360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175360 128 =
      30791033751688044500162747256264 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175360 128 =
      944406608742934231344196 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175360 : ∀ i : Fin 128,
    levelEleven.lookup (175360 + i.val) ≤ levelElevenRoots.lookup (175360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_175488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175488 128 =
      26695741859491656310985996388965 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_175488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175488 128 =
      794495805663012112692552 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_175488 : ∀ i : Fin 128,
    levelEleven.lookup (175488 + i.val) ≤ levelElevenRoots.lookup (175488 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_342 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 175104 512 =
      126280735172805656654672758863719 := by
  have h0 := levelEleven_energy_175104
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175104 256 =
      68793959561625955843524015218490 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175104 128 128
      38990501075184807693481505420133 29803458486441148150042509798357 h0 levelEleven_energy_175232
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175104 384 =
      99584993313314000343686762474754 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175104 256 128
      68793959561625955843524015218490 30791033751688044500162747256264 h1 levelEleven_energy_175360
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 175104 512 =
      126280735172805656654672758863719 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 175104 384 128
      99584993313314000343686762474754 26695741859491656310985996388965 h2 levelEleven_energy_175488
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_342 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 512 =
      3691504615865945944324134 := by
  have h0 := levelEleven_fractional_175104
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 256 =
      1952602201459999600287386 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 128 128
      1046735675677139835013967 905866525782859765273419 h0 levelEleven_fractional_175232
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 384 =
      2897008810202933831631582 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 256 128
      1952602201459999600287386 944406608742934231344196 h1 levelEleven_fractional_175360
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 512 =
      3691504615865945944324134 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 175104 384 128
      2897008810202933831631582 794495805663012112692552 h2 levelEleven_fractional_175488
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_342 : ∀ i : Fin 512,
    levelEleven.lookup (175104 + i.val) ≤ levelElevenRoots.lookup (175104 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_175104
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175104 128 128
    h0 levelEleven_squares_175232
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175104 256 128
    h1 levelEleven_squares_175360
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 175104 384 128
    h2 levelEleven_squares_175488
  exact h3

end WordCertDensity.Certificates
