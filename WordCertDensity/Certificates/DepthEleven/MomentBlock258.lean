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
theorem levelEleven_energy_132096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132096 128 =
      32605545022190358108142548333097 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 128 =
      962276351874756737230725 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132096 : ∀ i : Fin 128,
    levelEleven.lookup (132096 + i.val) ≤ levelElevenRoots.lookup (132096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132224 128 =
      37537765224879022821723485705842 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132224 128 =
      981044981409501744936480 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132224 : ∀ i : Fin 128,
    levelEleven.lookup (132224 + i.val) ≤ levelElevenRoots.lookup (132224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132352 128 =
      20665001328225164286247344841533 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132352 128 =
      767897396661588280073950 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132352 : ∀ i : Fin 128,
    levelEleven.lookup (132352 + i.val) ≤ levelElevenRoots.lookup (132352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_132480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132480 128 =
      26513614259305555855505629657860 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_132480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132480 128 =
      818690053805023860566611 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_132480 : ∀ i : Fin 128,
    levelEleven.lookup (132480 + i.val) ≤ levelElevenRoots.lookup (132480 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_258 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 132096 512 =
      117321925834600101071619008538332 := by
  have h0 := levelEleven_energy_132096
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132096 256 =
      70143310247069380929866034038939 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132096 128 128
      32605545022190358108142548333097 37537765224879022821723485705842 h0 levelEleven_energy_132224
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132096 384 =
      90808311575294545216113378880472 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132096 256 128
      70143310247069380929866034038939 20665001328225164286247344841533 h1 levelEleven_energy_132352
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 132096 512 =
      117321925834600101071619008538332 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 132096 384 128
      90808311575294545216113378880472 26513614259305555855505629657860 h2 levelEleven_energy_132480
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_258 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 512 =
      3529908783750870622807766 := by
  have h0 := levelEleven_fractional_132096
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 256 =
      1943321333284258482167205 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 128 128
      962276351874756737230725 981044981409501744936480 h0 levelEleven_fractional_132224
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 384 =
      2711218729945846762241155 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 256 128
      1943321333284258482167205 767897396661588280073950 h1 levelEleven_fractional_132352
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 512 =
      3529908783750870622807766 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 132096 384 128
      2711218729945846762241155 818690053805023860566611 h2 levelEleven_fractional_132480
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_258 : ∀ i : Fin 512,
    levelEleven.lookup (132096 + i.val) ≤ levelElevenRoots.lookup (132096 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_132096
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132096 128 128
    h0 levelEleven_squares_132224
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132096 256 128
    h1 levelEleven_squares_132352
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 132096 384 128
    h2 levelEleven_squares_132480
  exact h3

end WordCertDensity.Certificates
