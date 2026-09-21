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
theorem levelEleven_energy_154624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154624 128 =
      43383053151290188670587262863191 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 128 =
      1107787600483322124036432 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154624 : ∀ i : Fin 128,
    levelEleven.lookup (154624 + i.val) ≤ levelElevenRoots.lookup (154624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_154752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154752 128 =
      21569976746046563187546365691476 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154752 128 =
      749849514626663142220089 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154752 : ∀ i : Fin 128,
    levelEleven.lookup (154752 + i.val) ≤ levelElevenRoots.lookup (154752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_154880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154880 128 =
      51401721411031137719357684938838 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_154880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154880 128 =
      1343238882162340023252628 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_154880 : ∀ i : Fin 128,
    levelEleven.lookup (154880 + i.val) ≤ levelElevenRoots.lookup (154880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155008 128 =
      25914467629766407153438846260793 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155008 128 =
      822163916074567357138715 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155008 : ∀ i : Fin 128,
    levelEleven.lookup (155008 + i.val) ≤ levelElevenRoots.lookup (155008 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_302 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 154624 512 =
      142269218938134296730930159754298 := by
  have h0 := levelEleven_energy_154624
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154624 256 =
      64953029897336751858133628554667 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154624 128 128
      43383053151290188670587262863191 21569976746046563187546365691476 h0 levelEleven_energy_154752
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154624 384 =
      116354751308367889577491313493505 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154624 256 128
      64953029897336751858133628554667 51401721411031137719357684938838 h1 levelEleven_energy_154880
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 154624 512 =
      142269218938134296730930159754298 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 154624 384 128
      116354751308367889577491313493505 25914467629766407153438846260793 h2 levelEleven_energy_155008
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_302 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 512 =
      4023039913346892646647864 := by
  have h0 := levelEleven_fractional_154624
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 256 =
      1857637115109985266256521 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 128 128
      1107787600483322124036432 749849514626663142220089 h0 levelEleven_fractional_154752
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 384 =
      3200875997272325289509149 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 256 128
      1857637115109985266256521 1343238882162340023252628 h1 levelEleven_fractional_154880
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 512 =
      4023039913346892646647864 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 154624 384 128
      3200875997272325289509149 822163916074567357138715 h2 levelEleven_fractional_155008
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_302 : ∀ i : Fin 512,
    levelEleven.lookup (154624 + i.val) ≤ levelElevenRoots.lookup (154624 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_154624
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154624 128 128
    h0 levelEleven_squares_154752
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154624 256 128
    h1 levelEleven_squares_154880
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 154624 384 128
    h2 levelEleven_squares_155008
  exact h3

end WordCertDensity.Certificates
