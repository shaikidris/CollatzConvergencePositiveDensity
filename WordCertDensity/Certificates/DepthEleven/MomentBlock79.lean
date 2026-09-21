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
theorem levelEleven_energy_40448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40448 128 =
      41421326113915736102102025474507 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 128 =
      1035017481471242855809021 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40448 : ∀ i : Fin 128,
    levelEleven.lookup (40448 + i.val) ≤ levelElevenRoots.lookup (40448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40576 128 =
      36548994468382006241247428129728 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40576 128 =
      1021828178967556499585436 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40576 : ∀ i : Fin 128,
    levelEleven.lookup (40576 + i.val) ≤ levelElevenRoots.lookup (40576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40704 128 =
      42556869446885303188062883563758 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40704 128 =
      1110232176794597167320545 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40704 : ∀ i : Fin 128,
    levelEleven.lookup (40704 + i.val) ≤ levelElevenRoots.lookup (40704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_40832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40832 128 =
      30740863652866373377648304582224 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40832 128 =
      882105734715139601390798 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40832 : ∀ i : Fin 128,
    levelEleven.lookup (40832 + i.val) ≤ levelElevenRoots.lookup (40832 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_79 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40448 512 =
      151268053682049418909060641750217 := by
  have h0 := levelEleven_energy_40448
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40448 256 =
      77970320582297742343349453604235 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40448 128 128
      41421326113915736102102025474507 36548994468382006241247428129728 h0 levelEleven_energy_40576
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40448 384 =
      120527190029183045531412337167993 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40448 256 128
      77970320582297742343349453604235 42556869446885303188062883563758 h1 levelEleven_energy_40704
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40448 512 =
      151268053682049418909060641750217 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40448 384 128
      120527190029183045531412337167993 30740863652866373377648304582224 h2 levelEleven_energy_40832
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_79 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 512 =
      4049183571948536124105800 := by
  have h0 := levelEleven_fractional_40448
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 256 =
      2056845660438799355394457 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 128 128
      1035017481471242855809021 1021828178967556499585436 h0 levelEleven_fractional_40576
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 384 =
      3167077837233396522715002 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 256 128
      2056845660438799355394457 1110232176794597167320545 h1 levelEleven_fractional_40704
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 512 =
      4049183571948536124105800 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40448 384 128
      3167077837233396522715002 882105734715139601390798 h2 levelEleven_fractional_40832
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_79 : ∀ i : Fin 512,
    levelEleven.lookup (40448 + i.val) ≤ levelElevenRoots.lookup (40448 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_40448
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40448 128 128
    h0 levelEleven_squares_40576
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40448 256 128
    h1 levelEleven_squares_40704
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40448 384 128
    h2 levelEleven_squares_40832
  exact h3

end WordCertDensity.Certificates
