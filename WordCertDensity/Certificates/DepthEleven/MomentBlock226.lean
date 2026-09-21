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
theorem levelEleven_energy_115712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115712 128 =
      44057522769831940770159742247655 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 128 =
      1085367446969093076708586 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115712 : ∀ i : Fin 128,
    levelEleven.lookup (115712 + i.val) ≤ levelElevenRoots.lookup (115712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115840 128 =
      33888198755342645174344291105995 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115840 128 =
      977142518024398657015466 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115840 : ∀ i : Fin 128,
    levelEleven.lookup (115840 + i.val) ≤ levelElevenRoots.lookup (115840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_115968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115968 128 =
      31220849592932842409051001572421 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_115968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115968 128 =
      933842703268800738969970 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_115968 : ∀ i : Fin 128,
    levelEleven.lookup (115968 + i.val) ≤ levelElevenRoots.lookup (115968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_116096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 116096 128 =
      47797021277938233269991697394794 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_116096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 116096 128 =
      1033883245051774939229643 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_116096 : ∀ i : Fin 128,
    levelEleven.lookup (116096 + i.val) ≤ levelElevenRoots.lookup (116096 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_226 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 115712 512 =
      156963592396045661623546732320865 := by
  have h0 := levelEleven_energy_115712
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115712 256 =
      77945721525174585944504033353650 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115712 128 128
      44057522769831940770159742247655 33888198755342645174344291105995 h0 levelEleven_energy_115840
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115712 384 =
      109166571118107428353555034926071 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115712 256 128
      77945721525174585944504033353650 31220849592932842409051001572421 h1 levelEleven_energy_115968
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 115712 512 =
      156963592396045661623546732320865 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 115712 384 128
      109166571118107428353555034926071 47797021277938233269991697394794 h2 levelEleven_energy_116096
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_226 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 512 =
      4030235913314067411923665 := by
  have h0 := levelEleven_fractional_115712
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 256 =
      2062509964993491733724052 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 128 128
      1085367446969093076708586 977142518024398657015466 h0 levelEleven_fractional_115840
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 384 =
      2996352668262292472694022 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 256 128
      2062509964993491733724052 933842703268800738969970 h1 levelEleven_fractional_115968
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 512 =
      4030235913314067411923665 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 115712 384 128
      2996352668262292472694022 1033883245051774939229643 h2 levelEleven_fractional_116096
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_226 : ∀ i : Fin 512,
    levelEleven.lookup (115712 + i.val) ≤ levelElevenRoots.lookup (115712 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_115712
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115712 128 128
    h0 levelEleven_squares_115840
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115712 256 128
    h1 levelEleven_squares_115968
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 115712 384 128
    h2 levelEleven_squares_116096
  exact h3

end WordCertDensity.Certificates
