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
theorem levelEleven_energy_173056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173056 128 =
      38460407064166572755971168064643 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 128 =
      1018496430198571916836954 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173056 : ∀ i : Fin 128,
    levelEleven.lookup (173056 + i.val) ≤ levelElevenRoots.lookup (173056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173184 128 =
      28255996421463155477352654312639 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173184 128 =
      864848789371359427848956 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173184 : ∀ i : Fin 128,
    levelEleven.lookup (173184 + i.val) ≤ levelElevenRoots.lookup (173184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173312 128 =
      28507854033878962709921776830502 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173312 128 =
      873463759066806495484568 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173312 : ∀ i : Fin 128,
    levelEleven.lookup (173312 + i.val) ≤ levelElevenRoots.lookup (173312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173440 128 =
      46413586024127718837467350624536 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173440 128 =
      1120117709897121047828238 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173440 : ∀ i : Fin 128,
    levelEleven.lookup (173440 + i.val) ≤ levelElevenRoots.lookup (173440 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_338 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173056 512 =
      141637843543636409780712949832320 := by
  have h0 := levelEleven_energy_173056
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173056 256 =
      66716403485629728233323822377282 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173056 128 128
      38460407064166572755971168064643 28255996421463155477352654312639 h0 levelEleven_energy_173184
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173056 384 =
      95224257519508690943245599207784 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173056 256 128
      66716403485629728233323822377282 28507854033878962709921776830502 h1 levelEleven_energy_173312
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173056 512 =
      141637843543636409780712949832320 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173056 384 128
      95224257519508690943245599207784 46413586024127718837467350624536 h2 levelEleven_energy_173440
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_338 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 512 =
      3876926688533858887998716 := by
  have h0 := levelEleven_fractional_173056
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 256 =
      1883345219569931344685910 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 128 128
      1018496430198571916836954 864848789371359427848956 h0 levelEleven_fractional_173184
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 384 =
      2756808978636737840170478 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 256 128
      1883345219569931344685910 873463759066806495484568 h1 levelEleven_fractional_173312
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 512 =
      3876926688533858887998716 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173056 384 128
      2756808978636737840170478 1120117709897121047828238 h2 levelEleven_fractional_173440
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_338 : ∀ i : Fin 512,
    levelEleven.lookup (173056 + i.val) ≤ levelElevenRoots.lookup (173056 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_173056
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173056 128 128
    h0 levelEleven_squares_173184
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173056 256 128
    h1 levelEleven_squares_173312
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173056 384 128
    h2 levelEleven_squares_173440
  exact h3

end WordCertDensity.Certificates
