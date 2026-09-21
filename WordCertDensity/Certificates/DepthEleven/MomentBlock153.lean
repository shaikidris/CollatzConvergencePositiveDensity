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
theorem levelEleven_energy_78336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78336 128 =
      41441435209284668285063291231025 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 128 =
      1078451641372309628136605 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78336 : ∀ i : Fin 128,
    levelEleven.lookup (78336 + i.val) ≤ levelElevenRoots.lookup (78336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78464 128 =
      22245583773919391065062476478800 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78464 128 =
      749831038584496396204917 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78464 : ∀ i : Fin 128,
    levelEleven.lookup (78464 + i.val) ≤ levelElevenRoots.lookup (78464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78592 128 =
      45220742496226396353656849153213 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78592 128 =
      1184280792796413522641587 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78592 : ∀ i : Fin 128,
    levelEleven.lookup (78592 + i.val) ≤ levelElevenRoots.lookup (78592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78720 128 =
      740892091313752018817349582770059 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78720 128 =
      5143632606638783491268855 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78720 : ∀ i : Fin 128,
    levelEleven.lookup (78720 + i.val) ≤ levelElevenRoots.lookup (78720 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_153 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78336 512 =
      849799852793182474521132199633097 := by
  have h0 := levelEleven_energy_78336
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78336 256 =
      63687018983204059350125767709825 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78336 128 128
      41441435209284668285063291231025 22245583773919391065062476478800 h0 levelEleven_energy_78464
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78336 384 =
      108907761479430455703782616863038 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78336 256 128
      63687018983204059350125767709825 45220742496226396353656849153213 h1 levelEleven_energy_78592
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 78336 512 =
      849799852793182474521132199633097 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 78336 384 128
      108907761479430455703782616863038 740892091313752018817349582770059 h2 levelEleven_energy_78720
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_153 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 512 =
      8156196079392003038251964 := by
  have h0 := levelEleven_fractional_78336
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 256 =
      1828282679956806024341522 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 128 128
      1078451641372309628136605 749831038584496396204917 h0 levelEleven_fractional_78464
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 384 =
      3012563472753219546983109 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 256 128
      1828282679956806024341522 1184280792796413522641587 h1 levelEleven_fractional_78592
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 512 =
      8156196079392003038251964 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78336 384 128
      3012563472753219546983109 5143632606638783491268855 h2 levelEleven_fractional_78720
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_153 : ∀ i : Fin 512,
    levelEleven.lookup (78336 + i.val) ≤ levelElevenRoots.lookup (78336 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_78336
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78336 128 128
    h0 levelEleven_squares_78464
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78336 256 128
    h1 levelEleven_squares_78592
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 78336 384 128
    h2 levelEleven_squares_78720
  exact h3

end WordCertDensity.Certificates
