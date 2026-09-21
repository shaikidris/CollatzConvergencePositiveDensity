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
theorem levelEleven_energy_78848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78848 128 =
      109991824101699397314187809900869 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 128 =
      2029707307030199143635379 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78848 : ∀ i : Fin 128,
    levelEleven.lookup (78848 + i.val) ≤ levelElevenRoots.lookup (78848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78976 128 =
      26057491741769035298769549935322 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78976 128 =
      864849509638166247433523 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78976 : ∀ i : Fin 128,
    levelEleven.lookup (78976 + i.val) ≤ levelElevenRoots.lookup (78976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_79104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79104 128 =
      36580209394905862628953744068220 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79104 128 =
      1042887943631351387770019 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79104 : ∀ i : Fin 128,
    levelEleven.lookup (79104 + i.val) ≤ levelElevenRoots.lookup (79104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_79232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79232 128 =
      84317005500839867543276314931344 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79232 128 =
      1489177257228669799022248 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79232 : ∀ i : Fin 128,
    levelEleven.lookup (79232 + i.val) ≤ levelElevenRoots.lookup (79232 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_154 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78848 512 =
      256946530739214162785187418835755 := by
  have h0 := levelEleven_energy_78848
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78848 256 =
      136049315843468432612957359836191 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78848 128 128
      109991824101699397314187809900869 26057491741769035298769549935322 h0 levelEleven_energy_78976
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78848 384 =
      172629525238374295241911103904411 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78848 256 128
      136049315843468432612957359836191 36580209394905862628953744068220 h1 levelEleven_energy_79104
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78848 512 =
      256946530739214162785187418835755 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78848 384 128
      172629525238374295241911103904411 84317005500839867543276314931344 h2 levelEleven_energy_79232
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_154 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 512 =
      5426622017528386577861169 := by
  have h0 := levelEleven_fractional_78848
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 256 =
      2894556816668365391068902 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 128 128
      2029707307030199143635379 864849509638166247433523 h0 levelEleven_fractional_78976
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 384 =
      3937444760299716778838921 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 256 128
      2894556816668365391068902 1042887943631351387770019 h1 levelEleven_fractional_79104
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 512 =
      5426622017528386577861169 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78848 384 128
      3937444760299716778838921 1489177257228669799022248 h2 levelEleven_fractional_79232
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_154 : ∀ i : Fin 512,
    levelEleven.lookup (78848 + i.val) ≤ levelElevenRoots.lookup (78848 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_78848
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78848 128 128
    h0 levelEleven_squares_78976
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78848 256 128
    h1 levelEleven_squares_79104
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78848 384 128
    h2 levelEleven_squares_79232
  exact h3

end WordCertDensity.Certificates
