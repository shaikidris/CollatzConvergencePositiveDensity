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
theorem levelEleven_energy_93696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93696 128 =
      43782126298309535766272167063590 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 128 =
      1122630820598923666628644 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93696 : ∀ i : Fin 128,
    levelEleven.lookup (93696 + i.val) ≤ levelElevenRoots.lookup (93696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93824 128 =
      96381244448241568632588783229767 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93824 128 =
      1542332220766086811266759 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93824 : ∀ i : Fin 128,
    levelEleven.lookup (93824 + i.val) ≤ levelElevenRoots.lookup (93824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93952 128 =
      273803447894757719080017468099140 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93952 128 =
      2972061465996476494140217 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93952 : ∀ i : Fin 128,
    levelEleven.lookup (93952 + i.val) ≤ levelElevenRoots.lookup (93952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94080 128 =
      20756303282837304335668388691856 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94080 128 =
      737581267230385829068354 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94080 : ∀ i : Fin 128,
    levelEleven.lookup (94080 + i.val) ≤ levelElevenRoots.lookup (94080 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_183 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93696 512 =
      434723121924146127814546807084353 := by
  have h0 := levelEleven_energy_93696
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93696 256 =
      140163370746551104398860950293357 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93696 128 128
      43782126298309535766272167063590 96381244448241568632588783229767 h0 levelEleven_energy_93824
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93696 384 =
      413966818641308823478878418392497 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93696 256 128
      140163370746551104398860950293357 273803447894757719080017468099140 h1 levelEleven_energy_93952
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93696 512 =
      434723121924146127814546807084353 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93696 384 128
      413966818641308823478878418392497 20756303282837304335668388691856 h2 levelEleven_energy_94080
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_183 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 512 =
      6374605774591872801103974 := by
  have h0 := levelEleven_fractional_93696
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 256 =
      2664963041365010477895403 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 128 128
      1122630820598923666628644 1542332220766086811266759 h0 levelEleven_fractional_93824
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 384 =
      5637024507361486972035620 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 256 128
      2664963041365010477895403 2972061465996476494140217 h1 levelEleven_fractional_93952
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 512 =
      6374605774591872801103974 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93696 384 128
      5637024507361486972035620 737581267230385829068354 h2 levelEleven_fractional_94080
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_183 : ∀ i : Fin 512,
    levelEleven.lookup (93696 + i.val) ≤ levelElevenRoots.lookup (93696 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_93696
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93696 128 128
    h0 levelEleven_squares_93824
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93696 256 128
    h1 levelEleven_squares_93952
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93696 384 128
    h2 levelEleven_squares_94080
  exact h3

end WordCertDensity.Certificates
