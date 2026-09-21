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
theorem levelEleven_energy_49664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49664 128 =
      58457068153497382149530343336303 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 128 =
      1352120056593735461532476 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49664 : ∀ i : Fin 128,
    levelEleven.lookup (49664 + i.val) ≤ levelElevenRoots.lookup (49664 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49792 128 =
      66167337576945241521926515935250 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49792 128 =
      1261570869867445351390369 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49792 : ∀ i : Fin 128,
    levelEleven.lookup (49792 + i.val) ≤ levelElevenRoots.lookup (49792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_49920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49920 128 =
      57841129362851672880242937207617 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_49920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49920 128 =
      1370895435761595958496324 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_49920 : ∀ i : Fin 128,
    levelEleven.lookup (49920 + i.val) ≤ levelElevenRoots.lookup (49920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50048 128 =
      46715246036675603093521908225520 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50048 128 =
      1111558910500157613249893 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50048 : ∀ i : Fin 128,
    levelEleven.lookup (50048 + i.val) ≤ levelElevenRoots.lookup (50048 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_97 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 49664 512 =
      229180781129969899645221704704690 := by
  have h0 := levelEleven_energy_49664
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49664 256 =
      124624405730442623671456859271553 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49664 128 128
      58457068153497382149530343336303 66167337576945241521926515935250 h0 levelEleven_energy_49792
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49664 384 =
      182465535093294296551699796479170 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49664 256 128
      124624405730442623671456859271553 57841129362851672880242937207617 h1 levelEleven_energy_49920
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 49664 512 =
      229180781129969899645221704704690 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 49664 384 128
      182465535093294296551699796479170 46715246036675603093521908225520 h2 levelEleven_energy_50048
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_97 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 512 =
      5096145272722934384669062 := by
  have h0 := levelEleven_fractional_49664
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 256 =
      2613690926461180812922845 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 128 128
      1352120056593735461532476 1261570869867445351390369 h0 levelEleven_fractional_49792
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 384 =
      3984586362222776771419169 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 256 128
      2613690926461180812922845 1370895435761595958496324 h1 levelEleven_fractional_49920
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 512 =
      5096145272722934384669062 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 49664 384 128
      3984586362222776771419169 1111558910500157613249893 h2 levelEleven_fractional_50048
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_97 : ∀ i : Fin 512,
    levelEleven.lookup (49664 + i.val) ≤ levelElevenRoots.lookup (49664 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_49664
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49664 128 128
    h0 levelEleven_squares_49792
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49664 256 128
    h1 levelEleven_squares_49920
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 49664 384 128
    h2 levelEleven_squares_50048
  exact h3

end WordCertDensity.Certificates
