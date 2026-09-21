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
theorem levelEleven_energy_71168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71168 128 =
      63846510907513155481219786422580 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 128 =
      1190959701842331527545575 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71168 : ∀ i : Fin 128,
    levelEleven.lookup (71168 + i.val) ≤ levelElevenRoots.lookup (71168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71296 128 =
      80987514975232642939907391065466 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71296 128 =
      1579926146778437949442506 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71296 : ∀ i : Fin 128,
    levelEleven.lookup (71296 + i.val) ≤ levelElevenRoots.lookup (71296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71424 128 =
      24355309747510320874970438787663 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71424 128 =
      793674988898680657271213 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71424 : ∀ i : Fin 128,
    levelEleven.lookup (71424 + i.val) ≤ levelElevenRoots.lookup (71424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71552 128 =
      228749129309459445110903239600388 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71552 128 =
      2612710398239338680511529 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71552 : ∀ i : Fin 128,
    levelEleven.lookup (71552 + i.val) ≤ levelElevenRoots.lookup (71552 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_139 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71168 512 =
      397938464939715564407000855876097 := by
  have h0 := levelEleven_energy_71168
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71168 256 =
      144834025882745798421127177488046 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71168 128 128
      63846510907513155481219786422580 80987514975232642939907391065466 h0 levelEleven_energy_71296
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71168 384 =
      169189335630256119296097616275709 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71168 256 128
      144834025882745798421127177488046 24355309747510320874970438787663 h1 levelEleven_energy_71424
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 71168 512 =
      397938464939715564407000855876097 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 71168 384 128
      169189335630256119296097616275709 228749129309459445110903239600388 h2 levelEleven_energy_71552
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_139 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 512 =
      6177271235758788814770823 := by
  have h0 := levelEleven_fractional_71168
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 256 =
      2770885848620769476988081 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 128 128
      1190959701842331527545575 1579926146778437949442506 h0 levelEleven_fractional_71296
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 384 =
      3564560837519450134259294 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 256 128
      2770885848620769476988081 793674988898680657271213 h1 levelEleven_fractional_71424
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 512 =
      6177271235758788814770823 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71168 384 128
      3564560837519450134259294 2612710398239338680511529 h2 levelEleven_fractional_71552
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_139 : ∀ i : Fin 512,
    levelEleven.lookup (71168 + i.val) ≤ levelElevenRoots.lookup (71168 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_71168
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71168 128 128
    h0 levelEleven_squares_71296
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71168 256 128
    h1 levelEleven_squares_71424
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 71168 384 128
    h2 levelEleven_squares_71552
  exact h3

end WordCertDensity.Certificates
