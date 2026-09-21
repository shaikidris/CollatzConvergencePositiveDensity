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
theorem levelEleven_energy_73728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73728 128 =
      208306587102841270405748349456918 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 128 =
      2736364434560273003836357 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73728 : ∀ i : Fin 128,
    levelEleven.lookup (73728 + i.val) ≤ levelElevenRoots.lookup (73728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73856 128 =
      35791859436469179851527090555811 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73856 128 =
      1031237216900125051645855 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73856 : ∀ i : Fin 128,
    levelEleven.lookup (73856 + i.val) ≤ levelElevenRoots.lookup (73856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73984 128 =
      37194145290791081419369022389081 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73984 128 =
      1051593003827342716598633 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73984 : ∀ i : Fin 128,
    levelEleven.lookup (73984 + i.val) ≤ levelElevenRoots.lookup (73984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_74112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74112 128 =
      237233659225494072184212155025808 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74112 128 =
      2624132764981289365098834 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74112 : ∀ i : Fin 128,
    levelEleven.lookup (74112 + i.val) ≤ levelElevenRoots.lookup (74112 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73728 512 =
      518526251055595603860856617427618 := by
  have h0 := levelEleven_energy_73728
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73728 256 =
      244098446539310450257275440012729 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73728 128 128
      208306587102841270405748349456918 35791859436469179851527090555811 h0 levelEleven_energy_73856
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73728 384 =
      281292591830101531676644462401810 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73728 256 128
      244098446539310450257275440012729 37194145290791081419369022389081 h1 levelEleven_energy_73984
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73728 512 =
      518526251055595603860856617427618 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73728 384 128
      281292591830101531676644462401810 237233659225494072184212155025808 h2 levelEleven_energy_74112
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 512 =
      7443327420269030137179679 := by
  have h0 := levelEleven_fractional_73728
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 256 =
      3767601651460398055482212 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 128 128
      2736364434560273003836357 1031237216900125051645855 h0 levelEleven_fractional_73856
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 384 =
      4819194655287740772080845 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 256 128
      3767601651460398055482212 1051593003827342716598633 h1 levelEleven_fractional_73984
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 512 =
      7443327420269030137179679 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73728 384 128
      4819194655287740772080845 2624132764981289365098834 h2 levelEleven_fractional_74112
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_144 : ∀ i : Fin 512,
    levelEleven.lookup (73728 + i.val) ≤ levelElevenRoots.lookup (73728 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_73728
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73728 128 128
    h0 levelEleven_squares_73856
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73728 256 128
    h1 levelEleven_squares_73984
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73728 384 128
    h2 levelEleven_squares_74112
  exact h3

end WordCertDensity.Certificates
