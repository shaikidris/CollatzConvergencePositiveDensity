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
theorem levelEleven_energy_149504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149504 128 =
      34977675096445206983992047943432 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 128 =
      1045308809658303857264944 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149504 : ∀ i : Fin 128,
    levelEleven.lookup (149504 + i.val) ≤ levelElevenRoots.lookup (149504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149632 128 =
      27508565734007408095104521110436 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149632 128 =
      866242827536409234392099 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149632 : ∀ i : Fin 128,
    levelEleven.lookup (149632 + i.val) ≤ levelElevenRoots.lookup (149632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149760 128 =
      30141574662749709574891328575458 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149760 128 =
      926541888014313653854555 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149760 : ∀ i : Fin 128,
    levelEleven.lookup (149760 + i.val) ≤ levelElevenRoots.lookup (149760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_149888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149888 128 =
      22774780811129950080527017631761 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_149888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149888 128 =
      748408119174628802887412 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_149888 : ∀ i : Fin 128,
    levelEleven.lookup (149888 + i.val) ≤ levelElevenRoots.lookup (149888 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_292 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 149504 512 =
      115402596304332274734514915261087 := by
  have h0 := levelEleven_energy_149504
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 149504 256 =
      62486240830452615079096569053868 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 149504 128 128
      34977675096445206983992047943432 27508565734007408095104521110436 h0 levelEleven_energy_149632
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 149504 384 =
      92627815493202324653987897629326 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 149504 256 128
      62486240830452615079096569053868 30141574662749709574891328575458 h1 levelEleven_energy_149760
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 149504 512 =
      115402596304332274734514915261087 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 149504 384 128
      92627815493202324653987897629326 22774780811129950080527017631761 h2 levelEleven_energy_149888
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_292 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 512 =
      3586501644383655548399010 := by
  have h0 := levelEleven_fractional_149504
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 256 =
      1911551637194713091657043 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 128 128
      1045308809658303857264944 866242827536409234392099 h0 levelEleven_fractional_149632
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 384 =
      2838093525209026745511598 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 256 128
      1911551637194713091657043 926541888014313653854555 h1 levelEleven_fractional_149760
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 512 =
      3586501644383655548399010 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 149504 384 128
      2838093525209026745511598 748408119174628802887412 h2 levelEleven_fractional_149888
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_292 : ∀ i : Fin 512,
    levelEleven.lookup (149504 + i.val) ≤ levelElevenRoots.lookup (149504 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_149504
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 149504 128 128
    h0 levelEleven_squares_149632
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 149504 256 128
    h1 levelEleven_squares_149760
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 149504 384 128
    h2 levelEleven_squares_149888
  exact h3

end WordCertDensity.Certificates
