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
theorem levelEleven_energy_143872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143872 128 =
      206191391993823240786676354954279 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 128 =
      2406123169073646769406900 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143872 : ∀ i : Fin 128,
    levelEleven.lookup (143872 + i.val) ≤ levelElevenRoots.lookup (143872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144000 128 =
      25238129396784900544201651567228 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144000 128 =
      843189699238581596366104 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144000 : ∀ i : Fin 128,
    levelEleven.lookup (144000 + i.val) ≤ levelElevenRoots.lookup (144000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144128 128 =
      47979741532374169512184988574350 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144128 128 =
      1141258037127153554115856 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144128 : ∀ i : Fin 128,
    levelEleven.lookup (144128 + i.val) ≤ levelElevenRoots.lookup (144128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_144256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144256 128 =
      82700349245888350961722405048169 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144256 128 =
      1559901403862837955158453 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144256 : ∀ i : Fin 128,
    levelEleven.lookup (144256 + i.val) ≤ levelElevenRoots.lookup (144256 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_281 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143872 512 =
      362109612168870661804785400144026 := by
  have h0 := levelEleven_energy_143872
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143872 256 =
      231429521390608141330878006521507 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143872 128 128
      206191391993823240786676354954279 25238129396784900544201651567228 h0 levelEleven_energy_144000
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143872 384 =
      279409262922982310843062995095857 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143872 256 128
      231429521390608141330878006521507 47979741532374169512184988574350 h1 levelEleven_energy_144128
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143872 512 =
      362109612168870661804785400144026 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143872 384 128
      279409262922982310843062995095857 82700349245888350961722405048169 h2 levelEleven_energy_144256
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_281 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 512 =
      5950472309302219875047313 := by
  have h0 := levelEleven_fractional_143872
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 256 =
      3249312868312228365773004 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 128 128
      2406123169073646769406900 843189699238581596366104 h0 levelEleven_fractional_144000
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 384 =
      4390570905439381919888860 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 256 128
      3249312868312228365773004 1141258037127153554115856 h1 levelEleven_fractional_144128
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 512 =
      5950472309302219875047313 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143872 384 128
      4390570905439381919888860 1559901403862837955158453 h2 levelEleven_fractional_144256
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_281 : ∀ i : Fin 512,
    levelEleven.lookup (143872 + i.val) ≤ levelElevenRoots.lookup (143872 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_143872
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143872 128 128
    h0 levelEleven_squares_144000
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143872 256 128
    h1 levelEleven_squares_144128
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143872 384 128
    h2 levelEleven_squares_144256
  exact h3

end WordCertDensity.Certificates
