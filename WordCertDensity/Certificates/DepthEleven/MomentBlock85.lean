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
theorem levelEleven_energy_43520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43520 128 =
      26412367620774694569096530313670 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 128 =
      806483205090644104162863 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43520 : ∀ i : Fin 128,
    levelEleven.lookup (43520 + i.val) ≤ levelElevenRoots.lookup (43520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43648 128 =
      65856608003946342912625478462396 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43648 128 =
      1471242673889590771040158 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43648 : ∀ i : Fin 128,
    levelEleven.lookup (43648 + i.val) ≤ levelElevenRoots.lookup (43648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43776 128 =
      36138225572967775138537436533274 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43776 128 =
      983393957261032962113065 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43776 : ∀ i : Fin 128,
    levelEleven.lookup (43776 + i.val) ≤ levelElevenRoots.lookup (43776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43904 128 =
      131606103349988566255575849865504 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43904 128 =
      1922898244831416884508009 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43904 : ∀ i : Fin 128,
    levelEleven.lookup (43904 + i.val) ≤ levelElevenRoots.lookup (43904 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_85 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43520 512 =
      260013304547677378875835295174844 := by
  have h0 := levelEleven_energy_43520
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43520 256 =
      92268975624721037481722008776066 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43520 128 128
      26412367620774694569096530313670 65856608003946342912625478462396 h0 levelEleven_energy_43648
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43520 384 =
      128407201197688812620259445309340 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43520 256 128
      92268975624721037481722008776066 36138225572967775138537436533274 h1 levelEleven_energy_43776
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43520 512 =
      260013304547677378875835295174844 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43520 384 128
      128407201197688812620259445309340 131606103349988566255575849865504 h2 levelEleven_energy_43904
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_85 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 512 =
      5184018081072684721824095 := by
  have h0 := levelEleven_fractional_43520
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 256 =
      2277725878980234875203021 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 128 128
      806483205090644104162863 1471242673889590771040158 h0 levelEleven_fractional_43648
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 384 =
      3261119836241267837316086 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 256 128
      2277725878980234875203021 983393957261032962113065 h1 levelEleven_fractional_43776
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 512 =
      5184018081072684721824095 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43520 384 128
      3261119836241267837316086 1922898244831416884508009 h2 levelEleven_fractional_43904
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_85 : ∀ i : Fin 512,
    levelEleven.lookup (43520 + i.val) ≤ levelElevenRoots.lookup (43520 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_43520
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43520 128 128
    h0 levelEleven_squares_43648
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43520 256 128
    h1 levelEleven_squares_43776
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43520 384 128
    h2 levelEleven_squares_43904
  exact h3

end WordCertDensity.Certificates
