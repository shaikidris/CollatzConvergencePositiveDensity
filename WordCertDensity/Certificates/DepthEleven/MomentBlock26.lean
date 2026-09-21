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
theorem levelEleven_energy_13312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13312 128 =
      34793967678938868858884018015313 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 128 =
      1035595085926565812920784 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13312 : ∀ i : Fin 128,
    levelEleven.lookup (13312 + i.val) ≤ levelElevenRoots.lookup (13312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13440 128 =
      36886911754821888644421640340153 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13440 128 =
      1072101637826171187329310 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13440 : ∀ i : Fin 128,
    levelEleven.lookup (13440 + i.val) ≤ levelElevenRoots.lookup (13440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13568 128 =
      28845653392954927141933365214940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13568 128 =
      879435526391613065236514 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13568 : ∀ i : Fin 128,
    levelEleven.lookup (13568 + i.val) ≤ levelElevenRoots.lookup (13568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13696 128 =
      55739796003957003373413537184621 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13696 128 =
      1289525947115764696157282 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13696 : ∀ i : Fin 128,
    levelEleven.lookup (13696 + i.val) ≤ levelElevenRoots.lookup (13696 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_26 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13312 512 =
      156266328830672688018652560755027 := by
  have h0 := levelEleven_energy_13312
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13312 256 =
      71680879433760757503305658355466 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13312 128 128
      34793967678938868858884018015313 36886911754821888644421640340153 h0 levelEleven_energy_13440
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13312 384 =
      100526532826715684645239023570406 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13312 256 128
      71680879433760757503305658355466 28845653392954927141933365214940 h1 levelEleven_energy_13568
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13312 512 =
      156266328830672688018652560755027 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13312 384 128
      100526532826715684645239023570406 55739796003957003373413537184621 h2 levelEleven_energy_13696
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_26 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 512 =
      4276658197260114761643890 := by
  have h0 := levelEleven_fractional_13312
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 256 =
      2107696723752737000250094 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 128 128
      1035595085926565812920784 1072101637826171187329310 h0 levelEleven_fractional_13440
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 384 =
      2987132250144350065486608 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 256 128
      2107696723752737000250094 879435526391613065236514 h1 levelEleven_fractional_13568
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 512 =
      4276658197260114761643890 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13312 384 128
      2987132250144350065486608 1289525947115764696157282 h2 levelEleven_fractional_13696
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_26 : ∀ i : Fin 512,
    levelEleven.lookup (13312 + i.val) ≤ levelElevenRoots.lookup (13312 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_13312
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13312 128 128
    h0 levelEleven_squares_13440
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13312 256 128
    h1 levelEleven_squares_13568
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13312 384 128
    h2 levelEleven_squares_13696
  exact h3

end WordCertDensity.Certificates
