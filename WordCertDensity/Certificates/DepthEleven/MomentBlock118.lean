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
theorem levelEleven_energy_60416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60416 128 =
      54649911242211655926681256606583 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 128 =
      1320335356862966660220401 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60416 : ∀ i : Fin 128,
    levelEleven.lookup (60416 + i.val) ≤ levelElevenRoots.lookup (60416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60544 128 =
      95539572586894132333707245013316 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60544 128 =
      1596934421564844573198731 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60544 : ∀ i : Fin 128,
    levelEleven.lookup (60544 + i.val) ≤ levelElevenRoots.lookup (60544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60672 128 =
      93434748843713237115074065189935 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60672 128 =
      1490917523762130013125944 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60672 : ∀ i : Fin 128,
    levelEleven.lookup (60672 + i.val) ≤ levelElevenRoots.lookup (60672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60800 128 =
      48636980332090914051241384502263 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60800 128 =
      1175011333910266677654593 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60800 : ∀ i : Fin 128,
    levelEleven.lookup (60800 + i.val) ≤ levelElevenRoots.lookup (60800 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_118 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60416 512 =
      292261213004909939426703951312097 := by
  have h0 := levelEleven_energy_60416
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60416 256 =
      150189483829105788260388501619899 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60416 128 128
      54649911242211655926681256606583 95539572586894132333707245013316 h0 levelEleven_energy_60544
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60416 384 =
      243624232672819025375462566809834 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60416 256 128
      150189483829105788260388501619899 93434748843713237115074065189935 h1 levelEleven_energy_60672
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60416 512 =
      292261213004909939426703951312097 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60416 384 128
      243624232672819025375462566809834 48636980332090914051241384502263 h2 levelEleven_energy_60800
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_118 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 512 =
      5583198636100207924199669 := by
  have h0 := levelEleven_fractional_60416
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 256 =
      2917269778427811233419132 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 128 128
      1320335356862966660220401 1596934421564844573198731 h0 levelEleven_fractional_60544
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 384 =
      4408187302189941246545076 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 256 128
      2917269778427811233419132 1490917523762130013125944 h1 levelEleven_fractional_60672
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 512 =
      5583198636100207924199669 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60416 384 128
      4408187302189941246545076 1175011333910266677654593 h2 levelEleven_fractional_60800
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_118 : ∀ i : Fin 512,
    levelEleven.lookup (60416 + i.val) ≤ levelElevenRoots.lookup (60416 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_60416
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60416 128 128
    h0 levelEleven_squares_60544
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60416 256 128
    h1 levelEleven_squares_60672
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60416 384 128
    h2 levelEleven_squares_60800
  exact h3

end WordCertDensity.Certificates
