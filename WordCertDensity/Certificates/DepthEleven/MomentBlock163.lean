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
theorem levelEleven_energy_83456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83456 128 =
      89190542469922758567706640591436 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 128 =
      1505823684070452988785074 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83456 : ∀ i : Fin 128,
    levelEleven.lookup (83456 + i.val) ≤ levelElevenRoots.lookup (83456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83584 128 =
      32730842214152479914919935161408 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83584 128 =
      917106439682939522075269 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83584 : ∀ i : Fin 128,
    levelEleven.lookup (83584 + i.val) ≤ levelElevenRoots.lookup (83584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83712 128 =
      27251563556868311170512275202599 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83712 128 =
      876302454635279610185332 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83712 : ∀ i : Fin 128,
    levelEleven.lookup (83712 + i.val) ≤ levelElevenRoots.lookup (83712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83840 128 =
      22174145786380673389004792783873 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83840 128 =
      737350631736072804248622 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83840 : ∀ i : Fin 128,
    levelEleven.lookup (83840 + i.val) ≤ levelElevenRoots.lookup (83840 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_163 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83456 512 =
      171347094027324223042143643739316 := by
  have h0 := levelEleven_energy_83456
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83456 256 =
      121921384684075238482626575752844 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83456 128 128
      89190542469922758567706640591436 32730842214152479914919935161408 h0 levelEleven_energy_83584
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83456 384 =
      149172948240943549653138850955443 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83456 256 128
      121921384684075238482626575752844 27251563556868311170512275202599 h1 levelEleven_energy_83712
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 83456 512 =
      171347094027324223042143643739316 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 83456 384 128
      149172948240943549653138850955443 22174145786380673389004792783873 h2 levelEleven_energy_83840
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_163 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 512 =
      4036583210124744925294297 := by
  have h0 := levelEleven_fractional_83456
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 256 =
      2422930123753392510860343 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 128 128
      1505823684070452988785074 917106439682939522075269 h0 levelEleven_fractional_83584
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 384 =
      3299232578388672121045675 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 256 128
      2422930123753392510860343 876302454635279610185332 h1 levelEleven_fractional_83712
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 512 =
      4036583210124744925294297 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83456 384 128
      3299232578388672121045675 737350631736072804248622 h2 levelEleven_fractional_83840
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_163 : ∀ i : Fin 512,
    levelEleven.lookup (83456 + i.val) ≤ levelElevenRoots.lookup (83456 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_83456
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83456 128 128
    h0 levelEleven_squares_83584
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83456 256 128
    h1 levelEleven_squares_83712
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 83456 384 128
    h2 levelEleven_squares_83840
  exact h3

end WordCertDensity.Certificates
