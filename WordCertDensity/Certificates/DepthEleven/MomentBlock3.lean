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
theorem levelEleven_energy_1536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1536 128 =
      84000959416987051858524329736030 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 128 =
      1659126326801146016663822 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1536 : ∀ i : Fin 128,
    levelEleven.lookup (1536 + i.val) ≤ levelElevenRoots.lookup (1536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1664 128 =
      31784260232763684198462129073955 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1664 128 =
      868598331269631115627211 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1664 : ∀ i : Fin 128,
    levelEleven.lookup (1664 + i.val) ≤ levelElevenRoots.lookup (1664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1792 128 =
      74773875785157690890849287705548 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1792 128 =
      1417412795779387487740496 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1792 : ∀ i : Fin 128,
    levelEleven.lookup (1792 + i.val) ≤ levelElevenRoots.lookup (1792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1920 128 =
      26462397701188610469248483277884 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1920 128 =
      810331561127275178866682 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1920 : ∀ i : Fin 128,
    levelEleven.lookup (1920 + i.val) ≤ levelElevenRoots.lookup (1920 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_3 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1536 512 =
      217021493136097037417084229793417 := by
  have h0 := levelEleven_energy_1536
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1536 256 =
      115785219649750736056986458809985 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1536 128 128
      84000959416987051858524329736030 31784260232763684198462129073955 h0 levelEleven_energy_1664
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1536 384 =
      190559095434908426947835746515533 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1536 256 128
      115785219649750736056986458809985 74773875785157690890849287705548 h1 levelEleven_energy_1792
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1536 512 =
      217021493136097037417084229793417 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1536 384 128
      190559095434908426947835746515533 26462397701188610469248483277884 h2 levelEleven_energy_1920
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_3 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 512 =
      4755469014977439798898211 := by
  have h0 := levelEleven_fractional_1536
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 256 =
      2527724658070777132291033 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 128 128
      1659126326801146016663822 868598331269631115627211 h0 levelEleven_fractional_1664
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 384 =
      3945137453850164620031529 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 256 128
      2527724658070777132291033 1417412795779387487740496 h1 levelEleven_fractional_1792
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 512 =
      4755469014977439798898211 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1536 384 128
      3945137453850164620031529 810331561127275178866682 h2 levelEleven_fractional_1920
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_3 : ∀ i : Fin 512,
    levelEleven.lookup (1536 + i.val) ≤ levelElevenRoots.lookup (1536 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_1536
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1536 128 128
    h0 levelEleven_squares_1664
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1536 256 128
    h1 levelEleven_squares_1792
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1536 384 128
    h2 levelEleven_squares_1920
  exact h3

end WordCertDensity.Certificates
