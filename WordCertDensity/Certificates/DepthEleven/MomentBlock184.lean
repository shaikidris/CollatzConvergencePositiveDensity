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
theorem levelEleven_energy_94208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94208 128 =
      43948227643858523179370049814738 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 128 =
      1131755853117262546725219 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94208 : ∀ i : Fin 128,
    levelEleven.lookup (94208 + i.val) ≤ levelElevenRoots.lookup (94208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94336 128 =
      34953663238705746940850576242876 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94336 128 =
      995990745098148063828971 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94336 : ∀ i : Fin 128,
    levelEleven.lookup (94336 + i.val) ≤ levelElevenRoots.lookup (94336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94464 128 =
      29272575711421458532664197267586 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94464 128 =
      873094778564869200184930 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94464 : ∀ i : Fin 128,
    levelEleven.lookup (94464 + i.val) ≤ levelElevenRoots.lookup (94464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_94592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94592 128 =
      87255622300170762256121923742544 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_94592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94592 128 =
      1591181529005672450821343 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_94592 : ∀ i : Fin 128,
    levelEleven.lookup (94592 + i.val) ≤ levelElevenRoots.lookup (94592 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 94208 512 =
      195430088894156490909006747067744 := by
  have h0 := levelEleven_energy_94208
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94208 256 =
      78901890882564270120220626057614 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94208 128 128
      43948227643858523179370049814738 34953663238705746940850576242876 h0 levelEleven_energy_94336
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94208 384 =
      108174466593985728652884823325200 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94208 256 128
      78901890882564270120220626057614 29272575711421458532664197267586 h1 levelEleven_energy_94464
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 94208 512 =
      195430088894156490909006747067744 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 94208 384 128
      108174466593985728652884823325200 87255622300170762256121923742544 h2 levelEleven_energy_94592
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 512 =
      4592022905785952261560463 := by
  have h0 := levelEleven_fractional_94208
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 256 =
      2127746598215410610554190 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 128 128
      1131755853117262546725219 995990745098148063828971 h0 levelEleven_fractional_94336
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 384 =
      3000841376780279810739120 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 256 128
      2127746598215410610554190 873094778564869200184930 h1 levelEleven_fractional_94464
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 512 =
      4592022905785952261560463 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 94208 384 128
      3000841376780279810739120 1591181529005672450821343 h2 levelEleven_fractional_94592
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_184 : ∀ i : Fin 512,
    levelEleven.lookup (94208 + i.val) ≤ levelElevenRoots.lookup (94208 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_94208
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94208 128 128
    h0 levelEleven_squares_94336
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94208 256 128
    h1 levelEleven_squares_94464
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 94208 384 128
    h2 levelEleven_squares_94592
  exact h3

end WordCertDensity.Certificates
