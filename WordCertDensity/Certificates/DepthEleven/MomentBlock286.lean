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
theorem levelEleven_energy_146432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146432 128 =
      99450762959262829267895234224333 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 128 =
      1709703952935933725447796 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146432 : ∀ i : Fin 128,
    levelEleven.lookup (146432 + i.val) ≤ levelElevenRoots.lookup (146432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146560 128 =
      24989769917378243262145678470257 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146560 128 =
      783669011348603362223154 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146560 : ∀ i : Fin 128,
    levelEleven.lookup (146560 + i.val) ≤ levelElevenRoots.lookup (146560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146688 128 =
      38511172501797995051287935808942 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146688 128 =
      1077270783684291754366126 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146688 : ∀ i : Fin 128,
    levelEleven.lookup (146688 + i.val) ≤ levelElevenRoots.lookup (146688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_146816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146816 128 =
      37380561006050264671820239704520 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_146816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146816 128 =
      964251961682853024404734 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_146816 : ∀ i : Fin 128,
    levelEleven.lookup (146816 + i.val) ≤ levelElevenRoots.lookup (146816 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_286 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 146432 512 =
      200332266384489332253149088208052 := by
  have h0 := levelEleven_energy_146432
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146432 256 =
      124440532876641072530040912694590 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146432 128 128
      99450762959262829267895234224333 24989769917378243262145678470257 h0 levelEleven_energy_146560
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146432 384 =
      162951705378439067581328848503532 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146432 256 128
      124440532876641072530040912694590 38511172501797995051287935808942 h1 levelEleven_energy_146688
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 146432 512 =
      200332266384489332253149088208052 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 146432 384 128
      162951705378439067581328848503532 37380561006050264671820239704520 h2 levelEleven_energy_146816
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_286 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 512 =
      4534895709651681866441810 := by
  have h0 := levelEleven_fractional_146432
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 256 =
      2493372964284537087670950 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 128 128
      1709703952935933725447796 783669011348603362223154 h0 levelEleven_fractional_146560
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 384 =
      3570643747968828842037076 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 256 128
      2493372964284537087670950 1077270783684291754366126 h1 levelEleven_fractional_146688
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 512 =
      4534895709651681866441810 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 146432 384 128
      3570643747968828842037076 964251961682853024404734 h2 levelEleven_fractional_146816
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_286 : ∀ i : Fin 512,
    levelEleven.lookup (146432 + i.val) ≤ levelElevenRoots.lookup (146432 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_146432
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146432 128 128
    h0 levelEleven_squares_146560
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146432 256 128
    h1 levelEleven_squares_146688
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 146432 384 128
    h2 levelEleven_squares_146816
  exact h3

end WordCertDensity.Certificates
