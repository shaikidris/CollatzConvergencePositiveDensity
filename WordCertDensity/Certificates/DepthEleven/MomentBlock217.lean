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
theorem levelEleven_energy_111104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111104 128 =
      29763684566008251662028268384538 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 128 =
      923070050037670267502734 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111104 : ∀ i : Fin 128,
    levelEleven.lookup (111104 + i.val) ≤ levelElevenRoots.lookup (111104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_111232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111232 128 =
      32289910379336085876282781980508 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111232 128 =
      962820133236066034649271 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111232 : ∀ i : Fin 128,
    levelEleven.lookup (111232 + i.val) ≤ levelElevenRoots.lookup (111232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_111360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111360 128 =
      49508260309797338641043312421851 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111360 128 =
      1182450917118725486266120 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111360 : ∀ i : Fin 128,
    levelEleven.lookup (111360 + i.val) ≤ levelElevenRoots.lookup (111360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_111488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111488 128 =
      151227513482218376594908129893371 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111488 128 =
      1928334345822454737597661 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111488 : ∀ i : Fin 128,
    levelEleven.lookup (111488 + i.val) ≤ levelElevenRoots.lookup (111488 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_217 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111104 512 =
      262789368737360052774262492680268 := by
  have h0 := levelEleven_energy_111104
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111104 256 =
      62053594945344337538311050365046 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111104 128 128
      29763684566008251662028268384538 32289910379336085876282781980508 h0 levelEleven_energy_111232
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111104 384 =
      111561855255141676179354362786897 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111104 256 128
      62053594945344337538311050365046 49508260309797338641043312421851 h1 levelEleven_energy_111360
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111104 512 =
      262789368737360052774262492680268 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111104 384 128
      111561855255141676179354362786897 151227513482218376594908129893371 h2 levelEleven_energy_111488
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_217 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 512 =
      4996675446214916526015786 := by
  have h0 := levelEleven_fractional_111104
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 256 =
      1885890183273736302152005 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 128 128
      923070050037670267502734 962820133236066034649271 h0 levelEleven_fractional_111232
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 384 =
      3068341100392461788418125 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 256 128
      1885890183273736302152005 1182450917118725486266120 h1 levelEleven_fractional_111360
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 512 =
      4996675446214916526015786 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111104 384 128
      3068341100392461788418125 1928334345822454737597661 h2 levelEleven_fractional_111488
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_217 : ∀ i : Fin 512,
    levelEleven.lookup (111104 + i.val) ≤ levelElevenRoots.lookup (111104 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_111104
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111104 128 128
    h0 levelEleven_squares_111232
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111104 256 128
    h1 levelEleven_squares_111360
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111104 384 128
    h2 levelEleven_squares_111488
  exact h3

end WordCertDensity.Certificates
