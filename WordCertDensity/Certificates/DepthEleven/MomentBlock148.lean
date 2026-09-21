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
theorem levelEleven_energy_75776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75776 128 =
      115311386999920867234615538548659 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 128 =
      1617970842950534841591719 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75776 : ∀ i : Fin 128,
    levelEleven.lookup (75776 + i.val) ≤ levelElevenRoots.lookup (75776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_75904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75904 128 =
      47325444484432165495822757503265 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_75904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75904 128 =
      1213140198091851287136140 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_75904 : ∀ i : Fin 128,
    levelEleven.lookup (75904 + i.val) ≤ levelElevenRoots.lookup (75904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76032 128 =
      45188094072753484055739780939553 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76032 128 =
      1170415250780390298610016 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76032 : ∀ i : Fin 128,
    levelEleven.lookup (76032 + i.val) ≤ levelElevenRoots.lookup (76032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76160 128 =
      57361854137373589397264152699305 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76160 128 =
      1406057412371572512776315 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76160 : ∀ i : Fin 128,
    levelEleven.lookup (76160 + i.val) ≤ levelElevenRoots.lookup (76160 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_148 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 75776 512 =
      265186779694480106183442229690782 := by
  have h0 := levelEleven_energy_75776
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75776 256 =
      162636831484353032730438296051924 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75776 128 128
      115311386999920867234615538548659 47325444484432165495822757503265 h0 levelEleven_energy_75904
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75776 384 =
      207824925557106516786178076991477 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75776 256 128
      162636831484353032730438296051924 45188094072753484055739780939553 h1 levelEleven_energy_76032
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 75776 512 =
      265186779694480106183442229690782 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 75776 384 128
      207824925557106516786178076991477 57361854137373589397264152699305 h2 levelEleven_energy_76160
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_148 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 512 =
      5407583704194348940114190 := by
  have h0 := levelEleven_fractional_75776
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 256 =
      2831111041042386128727859 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 128 128
      1617970842950534841591719 1213140198091851287136140 h0 levelEleven_fractional_75904
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 384 =
      4001526291822776427337875 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 256 128
      2831111041042386128727859 1170415250780390298610016 h1 levelEleven_fractional_76032
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 512 =
      5407583704194348940114190 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 75776 384 128
      4001526291822776427337875 1406057412371572512776315 h2 levelEleven_fractional_76160
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_148 : ∀ i : Fin 512,
    levelEleven.lookup (75776 + i.val) ≤ levelElevenRoots.lookup (75776 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_75776
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75776 128 128
    h0 levelEleven_squares_75904
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75776 256 128
    h1 levelEleven_squares_76032
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 75776 384 128
    h2 levelEleven_squares_76160
  exact h3

end WordCertDensity.Certificates
