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
theorem levelEleven_energy_105984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105984 128 =
      48537706103132371332544258360302 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 128 =
      1133793361018190847625070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105984 : ∀ i : Fin 128,
    levelEleven.lookup (105984 + i.val) ≤ levelElevenRoots.lookup (105984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106112 128 =
      17619602167258229445411897483454 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106112 128 =
      671644683520679784891496 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106112 : ∀ i : Fin 128,
    levelEleven.lookup (106112 + i.val) ≤ levelElevenRoots.lookup (106112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106240 128 =
      41106105182520945017456178814943 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106240 128 =
      1085953405216672351872753 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106240 : ∀ i : Fin 128,
    levelEleven.lookup (106240 + i.val) ≤ levelElevenRoots.lookup (106240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106368 128 =
      31980453235093480828493422032459 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106368 128 =
      857574965205422388205461 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106368 : ∀ i : Fin 128,
    levelEleven.lookup (106368 + i.val) ≤ levelElevenRoots.lookup (106368 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_207 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105984 512 =
      139243866688005026623905756691158 := by
  have h0 := levelEleven_energy_105984
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105984 256 =
      66157308270390600777956155843756 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105984 128 128
      48537706103132371332544258360302 17619602167258229445411897483454 h0 levelEleven_energy_106112
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105984 384 =
      107263413452911545795412334658699 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105984 256 128
      66157308270390600777956155843756 41106105182520945017456178814943 h1 levelEleven_energy_106240
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105984 512 =
      139243866688005026623905756691158 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105984 384 128
      107263413452911545795412334658699 31980453235093480828493422032459 h2 levelEleven_energy_106368
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_207 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 512 =
      3748966414960965372594780 := by
  have h0 := levelEleven_fractional_105984
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 256 =
      1805438044538870632516566 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 128 128
      1133793361018190847625070 671644683520679784891496 h0 levelEleven_fractional_106112
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 384 =
      2891391449755542984389319 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 256 128
      1805438044538870632516566 1085953405216672351872753 h1 levelEleven_fractional_106240
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 512 =
      3748966414960965372594780 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105984 384 128
      2891391449755542984389319 857574965205422388205461 h2 levelEleven_fractional_106368
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_207 : ∀ i : Fin 512,
    levelEleven.lookup (105984 + i.val) ≤ levelElevenRoots.lookup (105984 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_105984
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105984 128 128
    h0 levelEleven_squares_106112
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105984 256 128
    h1 levelEleven_squares_106240
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105984 384 128
    h2 levelEleven_squares_106368
  exact h3

end WordCertDensity.Certificates
