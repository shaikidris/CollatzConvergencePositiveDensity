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
theorem levelEleven_energy_89600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89600 128 =
      48369968059964615274652490755099 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 128 =
      1148758316451630911822994 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89600 : ∀ i : Fin 128,
    levelEleven.lookup (89600 + i.val) ≤ levelElevenRoots.lookup (89600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89728 128 =
      100333809073254938141781036623188 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89728 128 =
      1776704694711109185822915 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89728 : ∀ i : Fin 128,
    levelEleven.lookup (89728 + i.val) ≤ levelElevenRoots.lookup (89728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89856 128 =
      107667744993059292952694387104298 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89856 128 =
      1686807590036180748192729 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89856 : ∀ i : Fin 128,
    levelEleven.lookup (89856 + i.val) ≤ levelElevenRoots.lookup (89856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_89984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89984 128 =
      36211517653752112063925790510868 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_89984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89984 128 =
      1058108744833411620120876 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_89984 : ∀ i : Fin 128,
    levelEleven.lookup (89984 + i.val) ≤ levelElevenRoots.lookup (89984 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_175 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 89600 512 =
      292583039780030958433053704993453 := by
  have h0 := levelEleven_energy_89600
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89600 256 =
      148703777133219553416433527378287 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89600 128 128
      48369968059964615274652490755099 100333809073254938141781036623188 h0 levelEleven_energy_89728
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89600 384 =
      256371522126278846369127914482585 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89600 256 128
      148703777133219553416433527378287 107667744993059292952694387104298 h1 levelEleven_energy_89856
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 89600 512 =
      292583039780030958433053704993453 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 89600 384 128
      256371522126278846369127914482585 36211517653752112063925790510868 h2 levelEleven_energy_89984
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_175 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 512 =
      5670379346032332465959514 := by
  have h0 := levelEleven_fractional_89600
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 256 =
      2925463011162740097645909 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 128 128
      1148758316451630911822994 1776704694711109185822915 h0 levelEleven_fractional_89728
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 384 =
      4612270601198920845838638 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 256 128
      2925463011162740097645909 1686807590036180748192729 h1 levelEleven_fractional_89856
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 512 =
      5670379346032332465959514 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 89600 384 128
      4612270601198920845838638 1058108744833411620120876 h2 levelEleven_fractional_89984
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_175 : ∀ i : Fin 512,
    levelEleven.lookup (89600 + i.val) ≤ levelElevenRoots.lookup (89600 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_89600
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89600 128 128
    h0 levelEleven_squares_89728
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89600 256 128
    h1 levelEleven_squares_89856
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 89600 384 128
    h2 levelEleven_squares_89984
  exact h3

end WordCertDensity.Certificates
