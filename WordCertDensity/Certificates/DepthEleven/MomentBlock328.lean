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
theorem levelEleven_energy_167936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167936 128 =
      21069146019629477589797176988204 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_167936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 128 =
      741267726087268637353291 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_167936 : ∀ i : Fin 128,
    levelEleven.lookup (167936 + i.val) ≤ levelElevenRoots.lookup (167936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168064 128 =
      80730307403026940058693242249502 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168064 128 =
      1542549436865615119382421 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168064 : ∀ i : Fin 128,
    levelEleven.lookup (168064 + i.val) ≤ levelElevenRoots.lookup (168064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168192 128 =
      53780347386248119144228832640010 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168192 128 =
      1218929298462716481212761 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168192 : ∀ i : Fin 128,
    levelEleven.lookup (168192 + i.val) ≤ levelElevenRoots.lookup (168192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168320 128 =
      30880249676900937925681014130362 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168320 128 =
      939161846693127749530173 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168320 : ∀ i : Fin 128,
    levelEleven.lookup (168320 + i.val) ≤ levelElevenRoots.lookup (168320 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 167936 512 =
      186460050485805474718400266008078 := by
  have h0 := levelEleven_energy_167936
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167936 256 =
      101799453422656417648490419237706 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167936 128 128
      21069146019629477589797176988204 80730307403026940058693242249502 h0 levelEleven_energy_168064
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167936 384 =
      155579800808904536792719251877716 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167936 256 128
      101799453422656417648490419237706 53780347386248119144228832640010 h1 levelEleven_energy_168192
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 167936 512 =
      186460050485805474718400266008078 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 167936 384 128
      155579800808904536792719251877716 30880249676900937925681014130362 h2 levelEleven_energy_168320
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 512 =
      4441908308108727987478646 := by
  have h0 := levelEleven_fractional_167936
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 256 =
      2283817162952883756735712 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 128 128
      741267726087268637353291 1542549436865615119382421 h0 levelEleven_fractional_168064
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 384 =
      3502746461415600237948473 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 256 128
      2283817162952883756735712 1218929298462716481212761 h1 levelEleven_fractional_168192
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 512 =
      4441908308108727987478646 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 167936 384 128
      3502746461415600237948473 939161846693127749530173 h2 levelEleven_fractional_168320
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_328 : ∀ i : Fin 512,
    levelEleven.lookup (167936 + i.val) ≤ levelElevenRoots.lookup (167936 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_167936
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167936 128 128
    h0 levelEleven_squares_168064
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167936 256 128
    h1 levelEleven_squares_168192
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 167936 384 128
    h2 levelEleven_squares_168320
  exact h3

end WordCertDensity.Certificates
