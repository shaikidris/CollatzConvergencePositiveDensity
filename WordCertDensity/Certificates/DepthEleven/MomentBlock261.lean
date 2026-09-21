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
theorem levelEleven_energy_133632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133632 128 =
      101253168772655438277872368259219 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 128 =
      1722467114842719088050820 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133632 : ∀ i : Fin 128,
    levelEleven.lookup (133632 + i.val) ≤ levelElevenRoots.lookup (133632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_133760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133760 128 =
      43329308788062150809652533486299 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133760 128 =
      1121744529357114178910834 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133760 : ∀ i : Fin 128,
    levelEleven.lookup (133760 + i.val) ≤ levelElevenRoots.lookup (133760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_133888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133888 128 =
      26755663940076726052803736026373 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133888 128 =
      808303773529865560670166 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133888 : ∀ i : Fin 128,
    levelEleven.lookup (133888 + i.val) ≤ levelElevenRoots.lookup (133888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134016 128 =
      100057565838065686828227579442786 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134016 128 =
      1794447501110247659072694 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134016 : ∀ i : Fin 128,
    levelEleven.lookup (134016 + i.val) ≤ levelElevenRoots.lookup (134016 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_261 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133632 512 =
      271395707338860001968556217214677 := by
  have h0 := levelEleven_energy_133632
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133632 256 =
      144582477560717589087524901745518 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133632 128 128
      101253168772655438277872368259219 43329308788062150809652533486299 h0 levelEleven_energy_133760
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133632 384 =
      171338141500794315140328637771891 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133632 256 128
      144582477560717589087524901745518 26755663940076726052803736026373 h1 levelEleven_energy_133888
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133632 512 =
      271395707338860001968556217214677 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133632 384 128
      171338141500794315140328637771891 100057565838065686828227579442786 h2 levelEleven_energy_134016
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_261 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 512 =
      5446962918839946486704514 := by
  have h0 := levelEleven_fractional_133632
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 256 =
      2844211644199833266961654 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 128 128
      1722467114842719088050820 1121744529357114178910834 h0 levelEleven_fractional_133760
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 384 =
      3652515417729698827631820 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 256 128
      2844211644199833266961654 808303773529865560670166 h1 levelEleven_fractional_133888
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 512 =
      5446962918839946486704514 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133632 384 128
      3652515417729698827631820 1794447501110247659072694 h2 levelEleven_fractional_134016
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_261 : ∀ i : Fin 512,
    levelEleven.lookup (133632 + i.val) ≤ levelElevenRoots.lookup (133632 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_133632
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133632 128 128
    h0 levelEleven_squares_133760
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133632 256 128
    h1 levelEleven_squares_133888
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133632 384 128
    h2 levelEleven_squares_134016
  exact h3

end WordCertDensity.Certificates
