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
theorem levelEleven_energy_140288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140288 128 =
      38740385208114792304492235556106 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 128 =
      1052985250231766666430303 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140288 : ∀ i : Fin 128,
    levelEleven.lookup (140288 + i.val) ≤ levelElevenRoots.lookup (140288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140416 128 =
      89826348735548935103730131776279 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140416 128 =
      1593781280855902719022534 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140416 : ∀ i : Fin 128,
    levelEleven.lookup (140416 + i.val) ≤ levelElevenRoots.lookup (140416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140544 128 =
      46988812770203911691800639562545 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140544 128 =
      1182601993297134478443903 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140544 : ∀ i : Fin 128,
    levelEleven.lookup (140544 + i.val) ≤ levelElevenRoots.lookup (140544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140672 128 =
      33794246763402545966324827091388 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140672 128 =
      885389348555452120600728 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140672 : ∀ i : Fin 128,
    levelEleven.lookup (140672 + i.val) ≤ levelElevenRoots.lookup (140672 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_274 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140288 512 =
      209349793477270185066347833986318 := by
  have h0 := levelEleven_energy_140288
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140288 256 =
      128566733943663727408222367332385 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140288 128 128
      38740385208114792304492235556106 89826348735548935103730131776279 h0 levelEleven_energy_140416
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140288 384 =
      175555546713867639100023006894930 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140288 256 128
      128566733943663727408222367332385 46988812770203911691800639562545 h1 levelEleven_energy_140544
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140288 512 =
      209349793477270185066347833986318 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140288 384 128
      175555546713867639100023006894930 33794246763402545966324827091388 h2 levelEleven_energy_140672
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_274 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 512 =
      4714757872940255984497468 := by
  have h0 := levelEleven_fractional_140288
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 256 =
      2646766531087669385452837 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 128 128
      1052985250231766666430303 1593781280855902719022534 h0 levelEleven_fractional_140416
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 384 =
      3829368524384803863896740 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 256 128
      2646766531087669385452837 1182601993297134478443903 h1 levelEleven_fractional_140544
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 512 =
      4714757872940255984497468 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140288 384 128
      3829368524384803863896740 885389348555452120600728 h2 levelEleven_fractional_140672
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_274 : ∀ i : Fin 512,
    levelEleven.lookup (140288 + i.val) ≤ levelElevenRoots.lookup (140288 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_140288
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140288 128 128
    h0 levelEleven_squares_140416
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140288 256 128
    h1 levelEleven_squares_140544
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140288 384 128
    h2 levelEleven_squares_140672
  exact h3

end WordCertDensity.Certificates
