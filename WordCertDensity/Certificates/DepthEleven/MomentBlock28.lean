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
theorem levelEleven_energy_14336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14336 128 =
      23744096704228179622075869790555 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 128 =
      775782221017957960234020 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14336 : ∀ i : Fin 128,
    levelEleven.lookup (14336 + i.val) ≤ levelElevenRoots.lookup (14336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14464 128 =
      53085733738605389795665843996334 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14464 128 =
      1227294667077717491691102 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14464 : ∀ i : Fin 128,
    levelEleven.lookup (14464 + i.val) ≤ levelElevenRoots.lookup (14464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14592 128 =
      34985771255687485678354198303210 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14592 128 =
      896015289620427992092364 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14592 : ∀ i : Fin 128,
    levelEleven.lookup (14592 + i.val) ≤ levelElevenRoots.lookup (14592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14720 128 =
      277265947028962130663866498283549 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14720 128 =
      2956927190518710158683658 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14720 : ∀ i : Fin 128,
    levelEleven.lookup (14720 + i.val) ≤ levelElevenRoots.lookup (14720 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_28 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14336 512 =
      389081548727483185759962410373648 := by
  have h0 := levelEleven_energy_14336
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14336 256 =
      76829830442833569417741713786889 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14336 128 128
      23744096704228179622075869790555 53085733738605389795665843996334 h0 levelEleven_energy_14464
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14336 384 =
      111815601698521055096095912090099 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14336 256 128
      76829830442833569417741713786889 34985771255687485678354198303210 h1 levelEleven_energy_14592
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14336 512 =
      389081548727483185759962410373648 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14336 384 128
      111815601698521055096095912090099 277265947028962130663866498283549 h2 levelEleven_energy_14720
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_28 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 512 =
      5856019368234813602701144 := by
  have h0 := levelEleven_fractional_14336
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 256 =
      2003076888095675451925122 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 128 128
      775782221017957960234020 1227294667077717491691102 h0 levelEleven_fractional_14464
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 384 =
      2899092177716103444017486 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 256 128
      2003076888095675451925122 896015289620427992092364 h1 levelEleven_fractional_14592
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 512 =
      5856019368234813602701144 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14336 384 128
      2899092177716103444017486 2956927190518710158683658 h2 levelEleven_fractional_14720
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_28 : ∀ i : Fin 512,
    levelEleven.lookup (14336 + i.val) ≤ levelElevenRoots.lookup (14336 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_14336
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14336 128 128
    h0 levelEleven_squares_14464
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14336 256 128
    h1 levelEleven_squares_14592
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14336 384 128
    h2 levelEleven_squares_14720
  exact h3

end WordCertDensity.Certificates
