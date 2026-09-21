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
theorem levelEleven_energy_32768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32768 128 =
      255658762082320435530150297195073 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 128 =
      2534330567207580978972584 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32768 : ∀ i : Fin 128,
    levelEleven.lookup (32768 + i.val) ≤ levelElevenRoots.lookup (32768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32896 128 =
      100489766514101005307162283850950 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32896 128 =
      1774149116617446947187542 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32896 : ∀ i : Fin 128,
    levelEleven.lookup (32896 + i.val) ≤ levelElevenRoots.lookup (32896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33024 128 =
      93431722515830345865617930256086 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33024 128 =
      1673505856089291303975516 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33024 : ∀ i : Fin 128,
    levelEleven.lookup (33024 + i.val) ≤ levelElevenRoots.lookup (33024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33152 128 =
      90181106166077322328227586651813 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33152 128 =
      1664907996039004986658337 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33152 : ∀ i : Fin 128,
    levelEleven.lookup (33152 + i.val) ≤ levelElevenRoots.lookup (33152 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_64 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32768 512 =
      539761357278329109031158097953922 := by
  have h0 := levelEleven_energy_32768
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32768 256 =
      356148528596421440837312581046023 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32768 128 128
      255658762082320435530150297195073 100489766514101005307162283850950 h0 levelEleven_energy_32896
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32768 384 =
      449580251112251786702930511302109 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32768 256 128
      356148528596421440837312581046023 93431722515830345865617930256086 h1 levelEleven_energy_33024
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32768 512 =
      539761357278329109031158097953922 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32768 384 128
      449580251112251786702930511302109 90181106166077322328227586651813 h2 levelEleven_energy_33152
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_64 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 512 =
      7646893535953324216793979 := by
  have h0 := levelEleven_fractional_32768
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 256 =
      4308479683825027926160126 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 128 128
      2534330567207580978972584 1774149116617446947187542 h0 levelEleven_fractional_32896
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 384 =
      5981985539914319230135642 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 256 128
      4308479683825027926160126 1673505856089291303975516 h1 levelEleven_fractional_33024
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 512 =
      7646893535953324216793979 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32768 384 128
      5981985539914319230135642 1664907996039004986658337 h2 levelEleven_fractional_33152
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_64 : ∀ i : Fin 512,
    levelEleven.lookup (32768 + i.val) ≤ levelElevenRoots.lookup (32768 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_32768
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32768 128 128
    h0 levelEleven_squares_32896
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32768 256 128
    h1 levelEleven_squares_33024
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32768 384 128
    h2 levelEleven_squares_33152
  exact h3

end WordCertDensity.Certificates
