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
theorem levelEleven_energy_163840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163840 128 =
      71313973049457579953212314785170 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 128 =
      1463456910068289324567900 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163840 : ∀ i : Fin 128,
    levelEleven.lookup (163840 + i.val) ≤ levelElevenRoots.lookup (163840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163968 128 =
      46325453689502613756026846209261 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163968 128 =
      1111936754510230424168924 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163968 : ∀ i : Fin 128,
    levelEleven.lookup (163968 + i.val) ≤ levelElevenRoots.lookup (163968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164096 128 =
      58514077443348048061366307417275 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164096 128 =
      1396570972938726717292989 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164096 : ∀ i : Fin 128,
    levelEleven.lookup (164096 + i.val) ≤ levelElevenRoots.lookup (164096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164224 128 =
      84704699048102778748723525510414 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164224 128 =
      1630974435312211005766059 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164224 : ∀ i : Fin 128,
    levelEleven.lookup (164224 + i.val) ≤ levelElevenRoots.lookup (164224 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163840 512 =
      260858203230411020519328993922120 := by
  have h0 := levelEleven_energy_163840
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163840 256 =
      117639426738960193709239160994431 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163840 128 128
      71313973049457579953212314785170 46325453689502613756026846209261 h0 levelEleven_energy_163968
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163840 384 =
      176153504182308241770605468411706 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163840 256 128
      117639426738960193709239160994431 58514077443348048061366307417275 h1 levelEleven_energy_164096
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163840 512 =
      260858203230411020519328993922120 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163840 384 128
      176153504182308241770605468411706 84704699048102778748723525510414 h2 levelEleven_energy_164224
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 512 =
      5602939072829457471795872 := by
  have h0 := levelEleven_fractional_163840
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 256 =
      2575393664578519748736824 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 128 128
      1463456910068289324567900 1111936754510230424168924 h0 levelEleven_fractional_163968
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 384 =
      3971964637517246466029813 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 256 128
      2575393664578519748736824 1396570972938726717292989 h1 levelEleven_fractional_164096
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 512 =
      5602939072829457471795872 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163840 384 128
      3971964637517246466029813 1630974435312211005766059 h2 levelEleven_fractional_164224
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_320 : ∀ i : Fin 512,
    levelEleven.lookup (163840 + i.val) ≤ levelElevenRoots.lookup (163840 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_163840
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163840 128 128
    h0 levelEleven_squares_163968
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163840 256 128
    h1 levelEleven_squares_164096
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163840 384 128
    h2 levelEleven_squares_164224
  exact h3

end WordCertDensity.Certificates
