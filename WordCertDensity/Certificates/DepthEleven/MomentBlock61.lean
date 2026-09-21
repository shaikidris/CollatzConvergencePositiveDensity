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
theorem levelEleven_energy_31232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31232 128 =
      54466343479248768909321344976897 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 128 =
      1235127772989650504111272 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31232 : ∀ i : Fin 128,
    levelEleven.lookup (31232 + i.val) ≤ levelElevenRoots.lookup (31232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_31360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31360 128 =
      17440694801137527171851422153665 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31360 128 =
      647348045439230476395175 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31360 : ∀ i : Fin 128,
    levelEleven.lookup (31360 + i.val) ≤ levelElevenRoots.lookup (31360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_31488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31488 128 =
      45706747309604257918440157513382 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31488 128 =
      1207561184682711018728251 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31488 : ∀ i : Fin 128,
    levelEleven.lookup (31488 + i.val) ≤ levelElevenRoots.lookup (31488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_31616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31616 128 =
      21340688332920686138182544182946 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31616 128 =
      725786369806470428583320 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31616 : ∀ i : Fin 128,
    levelEleven.lookup (31616 + i.val) ≤ levelElevenRoots.lookup (31616 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_61 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31232 512 =
      138954473922911240137795468826890 := by
  have h0 := levelEleven_energy_31232
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31232 256 =
      71907038280386296081172767130562 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31232 128 128
      54466343479248768909321344976897 17440694801137527171851422153665 h0 levelEleven_energy_31360
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31232 384 =
      117613785589990553999612924643944 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31232 256 128
      71907038280386296081172767130562 45706747309604257918440157513382 h1 levelEleven_energy_31488
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 31232 512 =
      138954473922911240137795468826890 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 31232 384 128
      117613785589990553999612924643944 21340688332920686138182544182946 h2 levelEleven_energy_31616
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_61 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 512 =
      3815823372918062427818018 := by
  have h0 := levelEleven_fractional_31232
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 256 =
      1882475818428880980506447 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 128 128
      1235127772989650504111272 647348045439230476395175 h0 levelEleven_fractional_31360
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 384 =
      3090037003111591999234698 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 256 128
      1882475818428880980506447 1207561184682711018728251 h1 levelEleven_fractional_31488
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 512 =
      3815823372918062427818018 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31232 384 128
      3090037003111591999234698 725786369806470428583320 h2 levelEleven_fractional_31616
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_61 : ∀ i : Fin 512,
    levelEleven.lookup (31232 + i.val) ≤ levelElevenRoots.lookup (31232 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_31232
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31232 128 128
    h0 levelEleven_squares_31360
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31232 256 128
    h1 levelEleven_squares_31488
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 31232 384 128
    h2 levelEleven_squares_31616
  exact h3

end WordCertDensity.Certificates
