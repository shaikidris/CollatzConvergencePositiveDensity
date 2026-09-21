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
theorem levelEleven_energy_80384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80384 128 =
      26293798169521868988412554230114 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 128 =
      872908019802285455805039 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80384 : ∀ i : Fin 128,
    levelEleven.lookup (80384 + i.val) ≤ levelElevenRoots.lookup (80384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80512 128 =
      33091749094763245720068754344443 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80512 128 =
      993760447357050335965574 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80512 : ∀ i : Fin 128,
    levelEleven.lookup (80512 + i.val) ≤ levelElevenRoots.lookup (80512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80640 128 =
      25423366244282434241175995464315 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80640 128 =
      775395029597161739569986 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80640 : ∀ i : Fin 128,
    levelEleven.lookup (80640 + i.val) ≤ levelElevenRoots.lookup (80640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80768 128 =
      79121018495818175737558306436145 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80768 128 =
      1613367668307479349623085 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80768 : ∀ i : Fin 128,
    levelEleven.lookup (80768 + i.val) ≤ levelElevenRoots.lookup (80768 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_157 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80384 512 =
      163929932004385724687215610475017 := by
  have h0 := levelEleven_energy_80384
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80384 256 =
      59385547264285114708481308574557 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80384 128 128
      26293798169521868988412554230114 33091749094763245720068754344443 h0 levelEleven_energy_80512
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80384 384 =
      84808913508567548949657304038872 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80384 256 128
      59385547264285114708481308574557 25423366244282434241175995464315 h1 levelEleven_energy_80640
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80384 512 =
      163929932004385724687215610475017 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80384 384 128
      84808913508567548949657304038872 79121018495818175737558306436145 h2 levelEleven_energy_80768
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_157 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 512 =
      4255431165063976880963684 := by
  have h0 := levelEleven_fractional_80384
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 256 =
      1866668467159335791770613 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 128 128
      872908019802285455805039 993760447357050335965574 h0 levelEleven_fractional_80512
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 384 =
      2642063496756497531340599 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 256 128
      1866668467159335791770613 775395029597161739569986 h1 levelEleven_fractional_80640
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 512 =
      4255431165063976880963684 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80384 384 128
      2642063496756497531340599 1613367668307479349623085 h2 levelEleven_fractional_80768
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_157 : ∀ i : Fin 512,
    levelEleven.lookup (80384 + i.val) ≤ levelElevenRoots.lookup (80384 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_80384
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80384 128 128
    h0 levelEleven_squares_80512
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80384 256 128
    h1 levelEleven_squares_80640
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80384 384 128
    h2 levelEleven_squares_80768
  exact h3

end WordCertDensity.Certificates
