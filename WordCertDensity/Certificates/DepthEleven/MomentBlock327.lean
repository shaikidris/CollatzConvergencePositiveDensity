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
theorem levelEleven_energy_167424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167424 128 =
      23416565228359325362040360506220 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 128 =
      812663585126828939702742 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167424 : ∀ i : Fin 128,
    levelEleven.lookup (167424 + i.val) ≤ levelElevenRoots.lookup (167424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167552 128 =
      135375277546011135833640924104962 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167552 128 =
      2139045600399561340103792 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167552 : ∀ i : Fin 128,
    levelEleven.lookup (167552 + i.val) ≤ levelElevenRoots.lookup (167552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167680 128 =
      63370210273514355361163585880026 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167680 128 =
      1157173028615402423076226 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167680 : ∀ i : Fin 128,
    levelEleven.lookup (167680 + i.val) ≤ levelElevenRoots.lookup (167680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_167808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167808 128 =
      64990090070329698368564387343855 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167808 128 =
      1406628663332668645496952 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167808 : ∀ i : Fin 128,
    levelEleven.lookup (167808 + i.val) ≤ levelElevenRoots.lookup (167808 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_327 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167424 512 =
      287152143118214514925409257835063 := by
  have h0 := levelEleven_energy_167424
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167424 256 =
      158791842774370461195681284611182 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167424 128 128
      23416565228359325362040360506220 135375277546011135833640924104962 h0 levelEleven_energy_167552
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167424 384 =
      222162053047884816556844870491208 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167424 256 128
      158791842774370461195681284611182 63370210273514355361163585880026 h1 levelEleven_energy_167680
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167424 512 =
      287152143118214514925409257835063 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167424 384 128
      222162053047884816556844870491208 64990090070329698368564387343855 h2 levelEleven_energy_167808
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_327 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 512 =
      5515510877474461348379712 := by
  have h0 := levelEleven_fractional_167424
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 256 =
      2951709185526390279806534 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 128 128
      812663585126828939702742 2139045600399561340103792 h0 levelEleven_fractional_167552
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 384 =
      4108882214141792702882760 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 256 128
      2951709185526390279806534 1157173028615402423076226 h1 levelEleven_fractional_167680
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 512 =
      5515510877474461348379712 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167424 384 128
      4108882214141792702882760 1406628663332668645496952 h2 levelEleven_fractional_167808
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_327 : ∀ i : Fin 512,
    levelEleven.lookup (167424 + i.val) ≤ levelElevenRoots.lookup (167424 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_167424
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167424 128 128
    h0 levelEleven_squares_167552
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167424 256 128
    h1 levelEleven_squares_167680
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167424 384 128
    h2 levelEleven_squares_167808
  exact h3

end WordCertDensity.Certificates
