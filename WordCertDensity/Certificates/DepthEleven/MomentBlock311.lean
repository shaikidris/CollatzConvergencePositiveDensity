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
theorem levelEleven_energy_159232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159232 128 =
      36009365469366541349058385176762 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 128 =
      1058923786731501407265389 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159232 : ∀ i : Fin 128,
    levelEleven.lookup (159232 + i.val) ≤ levelElevenRoots.lookup (159232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_159360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159360 128 =
      18246995447945360272729941159899 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159360 128 =
      666856224625959628058881 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159360 : ∀ i : Fin 128,
    levelEleven.lookup (159360 + i.val) ≤ levelElevenRoots.lookup (159360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_159488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159488 128 =
      48642298018031867075151149575140 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159488 128 =
      1199931574657854928834359 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159488 : ∀ i : Fin 128,
    levelEleven.lookup (159488 + i.val) ≤ levelElevenRoots.lookup (159488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_159616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159616 128 =
      95514470492396840869962083271417 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_159616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159616 128 =
      1524102685969658775677002 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_159616 : ∀ i : Fin 128,
    levelEleven.lookup (159616 + i.val) ≤ levelElevenRoots.lookup (159616 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_311 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 159232 512 =
      198413129427740609566901559183218 := by
  have h0 := levelEleven_energy_159232
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159232 256 =
      54256360917311901621788326336661 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159232 128 128
      36009365469366541349058385176762 18246995447945360272729941159899 h0 levelEleven_energy_159360
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159232 384 =
      102898658935343768696939475911801 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159232 256 128
      54256360917311901621788326336661 48642298018031867075151149575140 h1 levelEleven_energy_159488
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 159232 512 =
      198413129427740609566901559183218 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 159232 384 128
      102898658935343768696939475911801 95514470492396840869962083271417 h2 levelEleven_energy_159616
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_311 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 512 =
      4449814271984974739835631 := by
  have h0 := levelEleven_fractional_159232
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 256 =
      1725780011357461035324270 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 128 128
      1058923786731501407265389 666856224625959628058881 h0 levelEleven_fractional_159360
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 384 =
      2925711586015315964158629 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 256 128
      1725780011357461035324270 1199931574657854928834359 h1 levelEleven_fractional_159488
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 512 =
      4449814271984974739835631 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 159232 384 128
      2925711586015315964158629 1524102685969658775677002 h2 levelEleven_fractional_159616
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_311 : ∀ i : Fin 512,
    levelEleven.lookup (159232 + i.val) ≤ levelElevenRoots.lookup (159232 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_159232
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159232 128 128
    h0 levelEleven_squares_159360
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159232 256 128
    h1 levelEleven_squares_159488
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 159232 384 128
    h2 levelEleven_squares_159616
  exact h3

end WordCertDensity.Certificates
