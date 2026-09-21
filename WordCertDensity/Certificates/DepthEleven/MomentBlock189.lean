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
theorem levelEleven_energy_96768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96768 128 =
      78189673979172215138964876512772 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 128 =
      1417050980233552360597577 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96768 : ∀ i : Fin 128,
    levelEleven.lookup (96768 + i.val) ≤ levelElevenRoots.lookup (96768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_96896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96896 128 =
      21867620454823123904451336208757 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_96896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96896 128 =
      748331899408610484309123 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_96896 : ∀ i : Fin 128,
    levelEleven.lookup (96896 + i.val) ≤ levelElevenRoots.lookup (96896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97024 128 =
      67897957477685865872900895241328 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97024 128 =
      1437180660017646200559571 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97024 : ∀ i : Fin 128,
    levelEleven.lookup (97024 + i.val) ≤ levelElevenRoots.lookup (97024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97152 128 =
      25513092471329708879276520671276 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97152 128 =
      826051117173734188165966 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97152 : ∀ i : Fin 128,
    levelEleven.lookup (97152 + i.val) ≤ levelElevenRoots.lookup (97152 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_189 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 96768 512 =
      193468344383010913795593628634133 := by
  have h0 := levelEleven_energy_96768
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96768 256 =
      100057294433995339043416212721529 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96768 128 128
      78189673979172215138964876512772 21867620454823123904451336208757 h0 levelEleven_energy_96896
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96768 384 =
      167955251911681204916317107962857 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96768 256 128
      100057294433995339043416212721529 67897957477685865872900895241328 h1 levelEleven_energy_97024
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 96768 512 =
      193468344383010913795593628634133 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 96768 384 128
      167955251911681204916317107962857 25513092471329708879276520671276 h2 levelEleven_energy_97152
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_189 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 512 =
      4428614656833543233632237 := by
  have h0 := levelEleven_fractional_96768
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 256 =
      2165382879642162844906700 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 128 128
      1417050980233552360597577 748331899408610484309123 h0 levelEleven_fractional_96896
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 384 =
      3602563539659809045466271 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 256 128
      2165382879642162844906700 1437180660017646200559571 h1 levelEleven_fractional_97024
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 512 =
      4428614656833543233632237 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 96768 384 128
      3602563539659809045466271 826051117173734188165966 h2 levelEleven_fractional_97152
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_189 : ∀ i : Fin 512,
    levelEleven.lookup (96768 + i.val) ≤ levelElevenRoots.lookup (96768 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_96768
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96768 128 128
    h0 levelEleven_squares_96896
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96768 256 128
    h1 levelEleven_squares_97024
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 96768 384 128
    h2 levelEleven_squares_97152
  exact h3

end WordCertDensity.Certificates
