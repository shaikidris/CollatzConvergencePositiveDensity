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
theorem levelEleven_energy_94720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94720 128 =
      20832156407133560974328813941856 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 128 =
      709258754123686170418840 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94720 : ∀ i : Fin 128,
    levelEleven.lookup (94720 + i.val) ≤ levelElevenRoots.lookup (94720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94848 128 =
      75447045467411428839448258580881 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94848 128 =
      1569814877131034431604760 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94848 : ∀ i : Fin 128,
    levelEleven.lookup (94848 + i.val) ≤ levelElevenRoots.lookup (94848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94976 128 =
      82344045820566714075755554141690 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94976 128 =
      1587920606824299922083633 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94976 : ∀ i : Fin 128,
    levelEleven.lookup (94976 + i.val) ≤ levelElevenRoots.lookup (94976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_95104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95104 128 =
      44032600814800712651626099200370 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95104 128 =
      1163530018815208350506998 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95104 : ∀ i : Fin 128,
    levelEleven.lookup (95104 + i.val) ≤ levelElevenRoots.lookup (95104 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_185 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94720 512 =
      222655848509912416541158725864797 := by
  have h0 := levelEleven_energy_94720
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94720 256 =
      96279201874544989813777072522737 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94720 128 128
      20832156407133560974328813941856 75447045467411428839448258580881 h0 levelEleven_energy_94848
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94720 384 =
      178623247695111703889532626664427 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94720 256 128
      96279201874544989813777072522737 82344045820566714075755554141690 h1 levelEleven_energy_94976
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94720 512 =
      222655848509912416541158725864797 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94720 384 128
      178623247695111703889532626664427 44032600814800712651626099200370 h2 levelEleven_energy_95104
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_185 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 512 =
      5030524256894228874614231 := by
  have h0 := levelEleven_fractional_94720
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 256 =
      2279073631254720602023600 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 128 128
      709258754123686170418840 1569814877131034431604760 h0 levelEleven_fractional_94848
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 384 =
      3866994238079020524107233 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 256 128
      2279073631254720602023600 1587920606824299922083633 h1 levelEleven_fractional_94976
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 512 =
      5030524256894228874614231 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94720 384 128
      3866994238079020524107233 1163530018815208350506998 h2 levelEleven_fractional_95104
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_185 : ∀ i : Fin 512,
    levelEleven.lookup (94720 + i.val) ≤ levelElevenRoots.lookup (94720 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_94720
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94720 128 128
    h0 levelEleven_squares_94848
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94720 256 128
    h1 levelEleven_squares_94976
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94720 384 128
    h2 levelEleven_squares_95104
  exact h3

end WordCertDensity.Certificates
