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
theorem levelEleven_energy_47616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47616 128 =
      29233581225343173787995472122803 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 128 =
      920807173085258150560332 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47616 : ∀ i : Fin 128,
    levelEleven.lookup (47616 + i.val) ≤ levelElevenRoots.lookup (47616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_47744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47744 128 =
      222853535212263996217156619103880 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47744 128 =
      2660118471325274985313897 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47744 : ∀ i : Fin 128,
    levelEleven.lookup (47744 + i.val) ≤ levelElevenRoots.lookup (47744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_47872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47872 128 =
      260257830517037026320285377764224 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47872 128 =
      2647474837664172994004923 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47872 : ∀ i : Fin 128,
    levelEleven.lookup (47872 + i.val) ≤ levelElevenRoots.lookup (47872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48000 128 =
      56131967635758798969664268637051 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48000 128 =
      1353467646539626427257265 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48000 : ∀ i : Fin 128,
    levelEleven.lookup (48000 + i.val) ≤ levelElevenRoots.lookup (48000 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_93 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47616 512 =
      568476914590402995295101737627958 := by
  have h0 := levelEleven_energy_47616
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47616 256 =
      252087116437607170005152091226683 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47616 128 128
      29233581225343173787995472122803 222853535212263996217156619103880 h0 levelEleven_energy_47744
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47616 384 =
      512344946954644196325437468990907 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47616 256 128
      252087116437607170005152091226683 260257830517037026320285377764224 h1 levelEleven_energy_47872
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47616 512 =
      568476914590402995295101737627958 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47616 384 128
      512344946954644196325437468990907 56131967635758798969664268637051 h2 levelEleven_energy_48000
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_93 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 512 =
      7581868128614332557136417 := by
  have h0 := levelEleven_fractional_47616
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 256 =
      3580925644410533135874229 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 128 128
      920807173085258150560332 2660118471325274985313897 h0 levelEleven_fractional_47744
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 384 =
      6228400482074706129879152 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 256 128
      3580925644410533135874229 2647474837664172994004923 h1 levelEleven_fractional_47872
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 512 =
      7581868128614332557136417 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47616 384 128
      6228400482074706129879152 1353467646539626427257265 h2 levelEleven_fractional_48000
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_93 : ∀ i : Fin 512,
    levelEleven.lookup (47616 + i.val) ≤ levelElevenRoots.lookup (47616 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_47616
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47616 128 128
    h0 levelEleven_squares_47744
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47616 256 128
    h1 levelEleven_squares_47872
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47616 384 128
    h2 levelEleven_squares_48000
  exact h3

end WordCertDensity.Certificates
