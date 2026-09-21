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
theorem levelEleven_energy_135680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135680 128 =
      39649147809261675992940842101706 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 128 =
      1126982293038105048522991 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135680 : ∀ i : Fin 128,
    levelEleven.lookup (135680 + i.val) ≤ levelElevenRoots.lookup (135680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135808 128 =
      40362924300941067206238149047233 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135808 128 =
      1064737076328571805943326 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135808 : ∀ i : Fin 128,
    levelEleven.lookup (135808 + i.val) ≤ levelElevenRoots.lookup (135808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135936 128 =
      43800684457204113674154290387153 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135936 128 =
      1140353753976231570231618 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135936 : ∀ i : Fin 128,
    levelEleven.lookup (135936 + i.val) ≤ levelElevenRoots.lookup (135936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136064 128 =
      30977209350615507953732710935718 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136064 128 =
      875730471485155207648235 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136064 : ∀ i : Fin 128,
    levelEleven.lookup (136064 + i.val) ≤ levelElevenRoots.lookup (136064 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_265 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135680 512 =
      154789965918022364827065992471810 := by
  have h0 := levelEleven_energy_135680
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135680 256 =
      80012072110202743199178991148939 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135680 128 128
      39649147809261675992940842101706 40362924300941067206238149047233 h0 levelEleven_energy_135808
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135680 384 =
      123812756567406856873333281536092 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135680 256 128
      80012072110202743199178991148939 43800684457204113674154290387153 h1 levelEleven_energy_135936
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 135680 512 =
      154789965918022364827065992471810 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 135680 384 128
      123812756567406856873333281536092 30977209350615507953732710935718 h2 levelEleven_energy_136064
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_265 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 512 =
      4207803594828063632346170 := by
  have h0 := levelEleven_fractional_135680
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 256 =
      2191719369366676854466317 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 128 128
      1126982293038105048522991 1064737076328571805943326 h0 levelEleven_fractional_135808
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 384 =
      3332073123342908424697935 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 256 128
      2191719369366676854466317 1140353753976231570231618 h1 levelEleven_fractional_135936
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 512 =
      4207803594828063632346170 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135680 384 128
      3332073123342908424697935 875730471485155207648235 h2 levelEleven_fractional_136064
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_265 : ∀ i : Fin 512,
    levelEleven.lookup (135680 + i.val) ≤ levelElevenRoots.lookup (135680 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_135680
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135680 128 128
    h0 levelEleven_squares_135808
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135680 256 128
    h1 levelEleven_squares_135936
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 135680 384 128
    h2 levelEleven_squares_136064
  exact h3

end WordCertDensity.Certificates
