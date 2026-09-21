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
theorem levelEleven_energy_29184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29184 128 =
      18303792302123797793905555206892 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 128 =
      647202573153344462523166 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29184 : ∀ i : Fin 128,
    levelEleven.lookup (29184 + i.val) ≤ levelElevenRoots.lookup (29184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29312 128 =
      68789506512832016338701214975018 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29312 128 =
      1510493719680830625321963 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29312 : ∀ i : Fin 128,
    levelEleven.lookup (29312 + i.val) ≤ levelElevenRoots.lookup (29312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29440 128 =
      48903731661509732069354891398519 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29440 128 =
      1152406789968328297868712 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29440 : ∀ i : Fin 128,
    levelEleven.lookup (29440 + i.val) ≤ levelElevenRoots.lookup (29440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_29568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29568 128 =
      22761486912125666173475739068208 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_29568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29568 128 =
      814519003596283100909583 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_29568 : ∀ i : Fin 128,
    levelEleven.lookup (29568 + i.val) ≤ levelElevenRoots.lookup (29568 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_57 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 29184 512 =
      158758517388591212375437400648637 := by
  have h0 := levelEleven_energy_29184
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29184 256 =
      87093298814955814132606770181910 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29184 128 128
      18303792302123797793905555206892 68789506512832016338701214975018 h0 levelEleven_energy_29312
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29184 384 =
      135997030476465546201961661580429 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29184 256 128
      87093298814955814132606770181910 48903731661509732069354891398519 h1 levelEleven_energy_29440
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 29184 512 =
      158758517388591212375437400648637 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 29184 384 128
      135997030476465546201961661580429 22761486912125666173475739068208 h2 levelEleven_energy_29568
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_57 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 512 =
      4124622086398786486623424 := by
  have h0 := levelEleven_fractional_29184
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 256 =
      2157696292834175087845129 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 128 128
      647202573153344462523166 1510493719680830625321963 h0 levelEleven_fractional_29312
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 384 =
      3310103082802503385713841 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 256 128
      2157696292834175087845129 1152406789968328297868712 h1 levelEleven_fractional_29440
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 512 =
      4124622086398786486623424 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 29184 384 128
      3310103082802503385713841 814519003596283100909583 h2 levelEleven_fractional_29568
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_57 : ∀ i : Fin 512,
    levelEleven.lookup (29184 + i.val) ≤ levelElevenRoots.lookup (29184 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_29184
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29184 128 128
    h0 levelEleven_squares_29312
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29184 256 128
    h1 levelEleven_squares_29440
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 29184 384 128
    h2 levelEleven_squares_29568
  exact h3

end WordCertDensity.Certificates
