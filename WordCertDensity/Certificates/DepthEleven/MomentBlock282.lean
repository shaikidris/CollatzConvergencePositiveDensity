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
theorem levelEleven_energy_144384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144384 128 =
      52352079055222824880488792649989 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 128 =
      1205115008130115503332387 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144384 : ∀ i : Fin 128,
    levelEleven.lookup (144384 + i.val) ≤ levelElevenRoots.lookup (144384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144512 128 =
      69586620425227670464594701390995 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144512 128 =
      1473526405397432785368091 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144512 : ∀ i : Fin 128,
    levelEleven.lookup (144512 + i.val) ≤ levelElevenRoots.lookup (144512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144640 128 =
      29660414221003204356139540578564 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144640 128 =
      943380622171230654505452 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144640 : ∀ i : Fin 128,
    levelEleven.lookup (144640 + i.val) ≤ levelElevenRoots.lookup (144640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144768 128 =
      32554471887054832222344156945779 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144768 128 =
      961422793936059259127408 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144768 : ∀ i : Fin 128,
    levelEleven.lookup (144768 + i.val) ≤ levelElevenRoots.lookup (144768 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_282 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144384 512 =
      184153585588508531923567191565327 := by
  have h0 := levelEleven_energy_144384
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144384 256 =
      121938699480450495345083494040984 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144384 128 128
      52352079055222824880488792649989 69586620425227670464594701390995 h0 levelEleven_energy_144512
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144384 384 =
      151599113701453699701223034619548 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144384 256 128
      121938699480450495345083494040984 29660414221003204356139540578564 h1 levelEleven_energy_144640
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144384 512 =
      184153585588508531923567191565327 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144384 384 128
      151599113701453699701223034619548 32554471887054832222344156945779 h2 levelEleven_energy_144768
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_282 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 512 =
      4583444829634838202333338 := by
  have h0 := levelEleven_fractional_144384
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 256 =
      2678641413527548288700478 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 128 128
      1205115008130115503332387 1473526405397432785368091 h0 levelEleven_fractional_144512
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 384 =
      3622022035698778943205930 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 256 128
      2678641413527548288700478 943380622171230654505452 h1 levelEleven_fractional_144640
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 512 =
      4583444829634838202333338 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144384 384 128
      3622022035698778943205930 961422793936059259127408 h2 levelEleven_fractional_144768
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_282 : ∀ i : Fin 512,
    levelEleven.lookup (144384 + i.val) ≤ levelElevenRoots.lookup (144384 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_144384
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144384 128 128
    h0 levelEleven_squares_144512
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144384 256 128
    h1 levelEleven_squares_144640
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144384 384 128
    h2 levelEleven_squares_144768
  exact h3

end WordCertDensity.Certificates
