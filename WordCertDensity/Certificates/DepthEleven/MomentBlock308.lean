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
theorem levelEleven_energy_157696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157696 128 =
      51647715307769800755378931011674 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 128 =
      1281821116032861051096874 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157696 : ∀ i : Fin 128,
    levelEleven.lookup (157696 + i.val) ≤ levelElevenRoots.lookup (157696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157824 128 =
      53848161494475719417607079709150 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157824 128 =
      1343570652015993793449196 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157824 : ∀ i : Fin 128,
    levelEleven.lookup (157824 + i.val) ≤ levelElevenRoots.lookup (157824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157952 128 =
      26428183322688891397078101099981 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157952 128 =
      829814798410175176508324 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157952 : ∀ i : Fin 128,
    levelEleven.lookup (157952 + i.val) ≤ levelElevenRoots.lookup (157952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_158080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 158080 128 =
      39527437451525739478083417816970 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_158080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 158080 128 =
      1058665749785832197388188 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_158080 : ∀ i : Fin 128,
    levelEleven.lookup (158080 + i.val) ≤ levelElevenRoots.lookup (158080 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_308 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157696 512 =
      171451497576460151048147529637775 := by
  have h0 := levelEleven_energy_157696
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157696 256 =
      105495876802245520172986010720824 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157696 128 128
      51647715307769800755378931011674 53848161494475719417607079709150 h0 levelEleven_energy_157824
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157696 384 =
      131924060124934411570064111820805 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157696 256 128
      105495876802245520172986010720824 26428183322688891397078101099981 h1 levelEleven_energy_157952
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157696 512 =
      171451497576460151048147529637775 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157696 384 128
      131924060124934411570064111820805 39527437451525739478083417816970 h2 levelEleven_energy_158080
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_308 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 512 =
      4513872316244862218442582 := by
  have h0 := levelEleven_fractional_157696
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 256 =
      2625391768048854844546070 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 128 128
      1281821116032861051096874 1343570652015993793449196 h0 levelEleven_fractional_157824
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 384 =
      3455206566459030021054394 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 256 128
      2625391768048854844546070 829814798410175176508324 h1 levelEleven_fractional_157952
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 512 =
      4513872316244862218442582 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157696 384 128
      3455206566459030021054394 1058665749785832197388188 h2 levelEleven_fractional_158080
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_308 : ∀ i : Fin 512,
    levelEleven.lookup (157696 + i.val) ≤ levelElevenRoots.lookup (157696 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_157696
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157696 128 128
    h0 levelEleven_squares_157824
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157696 256 128
    h1 levelEleven_squares_157952
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157696 384 128
    h2 levelEleven_squares_158080
  exact h3

end WordCertDensity.Certificates
