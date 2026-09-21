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
theorem levelEleven_energy_85504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85504 128 =
      27348809491097449092706291566557 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 128 =
      884045140931141918307028 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85504 : ∀ i : Fin 128,
    levelEleven.lookup (85504 + i.val) ≤ levelElevenRoots.lookup (85504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85632 128 =
      30900786726175560553453476864161 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85632 128 =
      943814770607430982358865 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85632 : ∀ i : Fin 128,
    levelEleven.lookup (85632 + i.val) ≤ levelElevenRoots.lookup (85632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85760 128 =
      42424156281700191303436720895159 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85760 128 =
      1143095841027022771747393 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85760 : ∀ i : Fin 128,
    levelEleven.lookup (85760 + i.val) ≤ levelElevenRoots.lookup (85760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_85888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85888 128 =
      70581724445933330298905380122023 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_85888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85888 128 =
      1501932636548813756820563 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_85888 : ∀ i : Fin 128,
    levelEleven.lookup (85888 + i.val) ≤ levelElevenRoots.lookup (85888 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_167 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 85504 512 =
      171255476944906531248501869447900 := by
  have h0 := levelEleven_energy_85504
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 85504 256 =
      58249596217273009646159768430718 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 85504 128 128
      27348809491097449092706291566557 30900786726175560553453476864161 h0 levelEleven_energy_85632
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 85504 384 =
      100673752498973200949596489325877 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 85504 256 128
      58249596217273009646159768430718 42424156281700191303436720895159 h1 levelEleven_energy_85760
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 85504 512 =
      171255476944906531248501869447900 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 85504 384 128
      100673752498973200949596489325877 70581724445933330298905380122023 h2 levelEleven_energy_85888
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_167 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 512 =
      4472888389114409429233849 := by
  have h0 := levelEleven_fractional_85504
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 256 =
      1827859911538572900665893 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 128 128
      884045140931141918307028 943814770607430982358865 h0 levelEleven_fractional_85632
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 384 =
      2970955752565595672413286 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 256 128
      1827859911538572900665893 1143095841027022771747393 h1 levelEleven_fractional_85760
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 512 =
      4472888389114409429233849 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 85504 384 128
      2970955752565595672413286 1501932636548813756820563 h2 levelEleven_fractional_85888
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_167 : ∀ i : Fin 512,
    levelEleven.lookup (85504 + i.val) ≤ levelElevenRoots.lookup (85504 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_85504
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 85504 128 128
    h0 levelEleven_squares_85632
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 85504 256 128
    h1 levelEleven_squares_85760
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 85504 384 128
    h2 levelEleven_squares_85888
  exact h3

end WordCertDensity.Certificates
