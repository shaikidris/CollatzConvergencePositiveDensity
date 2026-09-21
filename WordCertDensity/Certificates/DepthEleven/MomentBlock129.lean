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
theorem levelEleven_energy_66048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66048 128 =
      37639660812580891921671125952865 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 128 =
      984449869274428513208377 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66048 : ∀ i : Fin 128,
    levelEleven.lookup (66048 + i.val) ≤ levelElevenRoots.lookup (66048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66176 128 =
      117536312991750595362524280159613 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66176 128 =
      1920367858476418931218850 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66176 : ∀ i : Fin 128,
    levelEleven.lookup (66176 + i.val) ≤ levelElevenRoots.lookup (66176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66304 128 =
      211230847929594906812528125860952 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66304 128 =
      2386925508425922262725360 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66304 : ∀ i : Fin 128,
    levelEleven.lookup (66304 + i.val) ≤ levelElevenRoots.lookup (66304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66432 128 =
      27898964348603760027883241028559 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66432 128 =
      887594802046555993121136 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66432 : ∀ i : Fin 128,
    levelEleven.lookup (66432 + i.val) ≤ levelElevenRoots.lookup (66432 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_129 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66048 512 =
      394305786082530154124606773001989 := by
  have h0 := levelEleven_energy_66048
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66048 256 =
      155175973804331487284195406112478 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66048 128 128
      37639660812580891921671125952865 117536312991750595362524280159613 h0 levelEleven_energy_66176
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66048 384 =
      366406821733926394096723531973430 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66048 256 128
      155175973804331487284195406112478 211230847929594906812528125860952 h1 levelEleven_energy_66304
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66048 512 =
      394305786082530154124606773001989 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66048 384 128
      366406821733926394096723531973430 27898964348603760027883241028559 h2 levelEleven_energy_66432
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_129 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 512 =
      6179338038223325700273723 := by
  have h0 := levelEleven_fractional_66048
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 256 =
      2904817727750847444427227 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 128 128
      984449869274428513208377 1920367858476418931218850 h0 levelEleven_fractional_66176
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 384 =
      5291743236176769707152587 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 256 128
      2904817727750847444427227 2386925508425922262725360 h1 levelEleven_fractional_66304
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 512 =
      6179338038223325700273723 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66048 384 128
      5291743236176769707152587 887594802046555993121136 h2 levelEleven_fractional_66432
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_129 : ∀ i : Fin 512,
    levelEleven.lookup (66048 + i.val) ≤ levelElevenRoots.lookup (66048 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_66048
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66048 128 128
    h0 levelEleven_squares_66176
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66048 256 128
    h1 levelEleven_squares_66304
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66048 384 128
    h2 levelEleven_squares_66432
  exact h3

end WordCertDensity.Certificates
