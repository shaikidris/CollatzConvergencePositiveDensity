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
theorem levelEleven_energy_140800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140800 128 =
      125567332208777837293890932114796 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 128 =
      1827768360528105366913834 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140800 : ∀ i : Fin 128,
    levelEleven.lookup (140800 + i.val) ≤ levelElevenRoots.lookup (140800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140928 128 =
      98759908362690419748620480536662 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140928 128 =
      1679294040895594577318147 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140928 : ∀ i : Fin 128,
    levelEleven.lookup (140928 + i.val) ≤ levelElevenRoots.lookup (140928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141056 128 =
      35135921934853645681805909466812 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141056 128 =
      1054270119895903181761412 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141056 : ∀ i : Fin 128,
    levelEleven.lookup (141056 + i.val) ≤ levelElevenRoots.lookup (141056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141184 128 =
      21335380336443012454967956942135 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141184 128 =
      762555963529360546484938 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141184 : ∀ i : Fin 128,
    levelEleven.lookup (141184 + i.val) ≤ levelElevenRoots.lookup (141184 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_275 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140800 512 =
      280798542842764915179285279060405 := by
  have h0 := levelEleven_energy_140800
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140800 256 =
      224327240571468257042511412651458 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140800 128 128
      125567332208777837293890932114796 98759908362690419748620480536662 h0 levelEleven_energy_140928
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140800 384 =
      259463162506321902724317322118270 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140800 256 128
      224327240571468257042511412651458 35135921934853645681805909466812 h1 levelEleven_energy_141056
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 140800 512 =
      280798542842764915179285279060405 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 140800 384 128
      259463162506321902724317322118270 21335380336443012454967956942135 h2 levelEleven_energy_141184
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_275 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 512 =
      5323888484848963672478331 := by
  have h0 := levelEleven_fractional_140800
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 256 =
      3507062401423699944231981 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 128 128
      1827768360528105366913834 1679294040895594577318147 h0 levelEleven_fractional_140928
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 384 =
      4561332521319603125993393 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 256 128
      3507062401423699944231981 1054270119895903181761412 h1 levelEleven_fractional_141056
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 512 =
      5323888484848963672478331 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140800 384 128
      4561332521319603125993393 762555963529360546484938 h2 levelEleven_fractional_141184
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_275 : ∀ i : Fin 512,
    levelEleven.lookup (140800 + i.val) ≤ levelElevenRoots.lookup (140800 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_140800
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140800 128 128
    h0 levelEleven_squares_140928
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140800 256 128
    h1 levelEleven_squares_141056
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 140800 384 128
    h2 levelEleven_squares_141184
  exact h3

end WordCertDensity.Certificates
