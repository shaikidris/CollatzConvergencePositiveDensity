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
theorem levelEleven_energy_110080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110080 128 =
      29960122112785361905718706910497 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 128 =
      837636257051759019874352 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110080 : ∀ i : Fin 128,
    levelEleven.lookup (110080 + i.val) ≤ levelElevenRoots.lookup (110080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110208 128 =
      36223933879557056158758180793184 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110208 128 =
      1000854177222265990639576 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110208 : ∀ i : Fin 128,
    levelEleven.lookup (110208 + i.val) ≤ levelElevenRoots.lookup (110208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110336 128 =
      25495838440254785562747493822095 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110336 128 =
      826503391121165359303597 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110336 : ∀ i : Fin 128,
    levelEleven.lookup (110336 + i.val) ≤ levelElevenRoots.lookup (110336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110464 128 =
      24213493049690268305001799050964 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110464 128 =
      807192467068017740442672 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110464 : ∀ i : Fin 128,
    levelEleven.lookup (110464 + i.val) ≤ levelElevenRoots.lookup (110464 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_215 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110080 512 =
      115893387482287471932226180576740 := by
  have h0 := levelEleven_energy_110080
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110080 256 =
      66184055992342418064476887703681 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110080 128 128
      29960122112785361905718706910497 36223933879557056158758180793184 h0 levelEleven_energy_110208
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110080 384 =
      91679894432597203627224381525776 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110080 256 128
      66184055992342418064476887703681 25495838440254785562747493822095 h1 levelEleven_energy_110336
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110080 512 =
      115893387482287471932226180576740 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110080 384 128
      91679894432597203627224381525776 24213493049690268305001799050964 h2 levelEleven_energy_110464
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_215 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 512 =
      3472186292463208110260197 := by
  have h0 := levelEleven_fractional_110080
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 256 =
      1838490434274025010513928 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 128 128
      837636257051759019874352 1000854177222265990639576 h0 levelEleven_fractional_110208
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 384 =
      2664993825395190369817525 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 256 128
      1838490434274025010513928 826503391121165359303597 h1 levelEleven_fractional_110336
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 512 =
      3472186292463208110260197 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110080 384 128
      2664993825395190369817525 807192467068017740442672 h2 levelEleven_fractional_110464
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_215 : ∀ i : Fin 512,
    levelEleven.lookup (110080 + i.val) ≤ levelElevenRoots.lookup (110080 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_110080
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110080 128 128
    h0 levelEleven_squares_110208
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110080 256 128
    h1 levelEleven_squares_110336
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110080 384 128
    h2 levelEleven_squares_110464
  exact h3

end WordCertDensity.Certificates
