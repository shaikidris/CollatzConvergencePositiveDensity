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
theorem levelEleven_energy_100864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100864 128 =
      22281533518020645587562579645610 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 128 =
      732755418659011938438044 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100864 : ∀ i : Fin 128,
    levelEleven.lookup (100864 + i.val) ≤ levelElevenRoots.lookup (100864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_100992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100992 128 =
      38112884690444669409108645301803 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_100992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100992 128 =
      1119386602524833769615671 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_100992 : ∀ i : Fin 128,
    levelEleven.lookup (100992 + i.val) ≤ levelElevenRoots.lookup (100992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_101120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101120 128 =
      25698131265213439335274435355023 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101120 128 =
      783977898936834467994661 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101120 : ∀ i : Fin 128,
    levelEleven.lookup (101120 + i.val) ≤ levelElevenRoots.lookup (101120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_101248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101248 128 =
      44080325058185453520326243275760 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101248 128 =
      1170309381534232620623448 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101248 : ∀ i : Fin 128,
    levelEleven.lookup (101248 + i.val) ≤ levelElevenRoots.lookup (101248 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_197 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 100864 512 =
      130172874531864207852271903578196 := by
  have h0 := levelEleven_energy_100864
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100864 256 =
      60394418208465314996671224947413 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100864 128 128
      22281533518020645587562579645610 38112884690444669409108645301803 h0 levelEleven_energy_100992
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100864 384 =
      86092549473678754331945660302436 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100864 256 128
      60394418208465314996671224947413 25698131265213439335274435355023 h1 levelEleven_energy_101120
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 100864 512 =
      130172874531864207852271903578196 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 100864 384 128
      86092549473678754331945660302436 44080325058185453520326243275760 h2 levelEleven_energy_101248
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_197 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 512 =
      3806429301654912796671824 := by
  have h0 := levelEleven_fractional_100864
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 256 =
      1852142021183845708053715 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 128 128
      732755418659011938438044 1119386602524833769615671 h0 levelEleven_fractional_100992
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 384 =
      2636119920120680176048376 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 256 128
      1852142021183845708053715 783977898936834467994661 h1 levelEleven_fractional_101120
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 512 =
      3806429301654912796671824 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 100864 384 128
      2636119920120680176048376 1170309381534232620623448 h2 levelEleven_fractional_101248
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_197 : ∀ i : Fin 512,
    levelEleven.lookup (100864 + i.val) ≤ levelElevenRoots.lookup (100864 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_100864
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100864 128 128
    h0 levelEleven_squares_100992
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100864 256 128
    h1 levelEleven_squares_101120
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 100864 384 128
    h2 levelEleven_squares_101248
  exact h3

end WordCertDensity.Certificates
