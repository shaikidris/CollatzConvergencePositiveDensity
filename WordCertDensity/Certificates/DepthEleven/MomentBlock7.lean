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
theorem levelEleven_energy_3584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3584 128 =
      240284331835174826356915655718819 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 128 =
      2601262716386113399693665 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3584 : ∀ i : Fin 128,
    levelEleven.lookup (3584 + i.val) ≤ levelElevenRoots.lookup (3584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3712 128 =
      35392685649969317694020472868705 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3712 128 =
      1010999828987283124483188 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3712 : ∀ i : Fin 128,
    levelEleven.lookup (3712 + i.val) ≤ levelElevenRoots.lookup (3712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3840 128 =
      30621358505930769886931791961673 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3840 128 =
      920706410709406409217101 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3840 : ∀ i : Fin 128,
    levelEleven.lookup (3840 + i.val) ≤ levelElevenRoots.lookup (3840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_3968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3968 128 =
      69437474611225450683626926822440 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_3968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3968 128 =
      1505961896263012248294375 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_3968 : ∀ i : Fin 128,
    levelEleven.lookup (3968 + i.val) ≤ levelElevenRoots.lookup (3968 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_7 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 3584 512 =
      375735850602300364621494847371637 := by
  have h0 := levelEleven_energy_3584
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3584 256 =
      275677017485144144050936128587524 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3584 128 128
      240284331835174826356915655718819 35392685649969317694020472868705 h0 levelEleven_energy_3712
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3584 384 =
      306298375991074913937867920549197 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3584 256 128
      275677017485144144050936128587524 30621358505930769886931791961673 h1 levelEleven_energy_3840
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 3584 512 =
      375735850602300364621494847371637 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 3584 384 128
      306298375991074913937867920549197 69437474611225450683626926822440 h2 levelEleven_energy_3968
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_7 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 512 =
      6038930852345815181688329 := by
  have h0 := levelEleven_fractional_3584
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 256 =
      3612262545373396524176853 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 128 128
      2601262716386113399693665 1010999828987283124483188 h0 levelEleven_fractional_3712
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 384 =
      4532968956082802933393954 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 256 128
      3612262545373396524176853 920706410709406409217101 h1 levelEleven_fractional_3840
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 512 =
      6038930852345815181688329 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 3584 384 128
      4532968956082802933393954 1505961896263012248294375 h2 levelEleven_fractional_3968
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_7 : ∀ i : Fin 512,
    levelEleven.lookup (3584 + i.val) ≤ levelElevenRoots.lookup (3584 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_3584
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3584 128 128
    h0 levelEleven_squares_3712
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3584 256 128
    h1 levelEleven_squares_3840
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 3584 384 128
    h2 levelEleven_squares_3968
  exact h3

end WordCertDensity.Certificates
