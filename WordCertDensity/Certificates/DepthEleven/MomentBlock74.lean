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
theorem levelEleven_energy_37888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37888 128 =
      18575717798176497585768846260719 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_37888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 128 =
      692342771686565532274928 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_37888 : ∀ i : Fin 128,
    levelEleven.lookup (37888 + i.val) ≤ levelElevenRoots.lookup (37888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38016 128 =
      89584983148781601250653306814403 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38016 128 =
      1640041595529812810293049 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38016 : ∀ i : Fin 128,
    levelEleven.lookup (38016 + i.val) ≤ levelElevenRoots.lookup (38016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38144 128 =
      41347889963186026760604419527488 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38144 128 =
      1079198876572978928375889 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38144 : ∀ i : Fin 128,
    levelEleven.lookup (38144 + i.val) ≤ levelElevenRoots.lookup (38144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38272 128 =
      29193935449850322646049143120399 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38272 128 =
      892108146177051621392422 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38272 : ∀ i : Fin 128,
    levelEleven.lookup (38272 + i.val) ≤ levelElevenRoots.lookup (38272 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_74 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 37888 512 =
      178702526359994448243075715723009 := by
  have h0 := levelEleven_energy_37888
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37888 256 =
      108160700946958098836422153075122 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37888 128 128
      18575717798176497585768846260719 89584983148781601250653306814403 h0 levelEleven_energy_38016
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37888 384 =
      149508590910144125597026572602610 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37888 256 128
      108160700946958098836422153075122 41347889963186026760604419527488 h1 levelEleven_energy_38144
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 37888 512 =
      178702526359994448243075715723009 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 37888 384 128
      149508590910144125597026572602610 29193935449850322646049143120399 h2 levelEleven_energy_38272
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_74 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 512 =
      4303691389966408892336288 := by
  have h0 := levelEleven_fractional_37888
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 256 =
      2332384367216378342567977 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 128 128
      692342771686565532274928 1640041595529812810293049 h0 levelEleven_fractional_38016
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 384 =
      3411583243789357270943866 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 256 128
      2332384367216378342567977 1079198876572978928375889 h1 levelEleven_fractional_38144
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 512 =
      4303691389966408892336288 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 37888 384 128
      3411583243789357270943866 892108146177051621392422 h2 levelEleven_fractional_38272
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_74 : ∀ i : Fin 512,
    levelEleven.lookup (37888 + i.val) ≤ levelElevenRoots.lookup (37888 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_37888
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37888 128 128
    h0 levelEleven_squares_38016
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37888 256 128
    h1 levelEleven_squares_38144
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 37888 384 128
    h2 levelEleven_squares_38272
  exact h3

end WordCertDensity.Certificates
