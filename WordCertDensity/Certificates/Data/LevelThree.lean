/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.SeedTwo

/-! # Complete level-three integer certificate

Generated from the exact direct evaluator at scale 2^48 and sixteen terms.
Each arithmetic claim below is checked by Lean's kernel.
-/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Every residue of the complete level-three upper tree. -/
def levelThree : Entries :=
  (.node
  (.node
    (.node
      (.node
        (.node
          (.leaf 0)
          (.leaf 125125759692215))
        (.node
          (.leaf 303827145907055)
          (.leaf 0)))
      (.node
        (.node
          (.leaf 151913572953528)
          (.leaf 1001006076751288))
        (.leaf 0)))
    (.node
      (.node
        (.node
          (.leaf 558485318065008)
          (.leaf 0))
        (.node
          (.leaf 500503038375644)
          (.leaf 1350117382722123)))
      (.node
        (.node
          (.leaf 0)
          (.leaf 499981197883101))
        (.leaf 139621329797121))))
  (.node
    (.node
      (.node
        (.node
          (.leaf 279242659032504)
          (.leaf 999962395766201))
        (.node
          (.leaf 0)
          (.leaf 46327841554433)))
      (.node
        (.node
          (.leaf 250251519384430)
          (.leaf 0))
        (.leaf 675058691361062)))
    (.node
      (.node
        (.node
          (.leaf 0)
          (.leaf 185311365908774))
        (.leaf 370622731817547))
      (.node
        (.node
          (.leaf 69810664898561)
          (.leaf 92655683108865))
        (.leaf 0)))))

/-- Integer square-root upper enclosures for every level-three entry. -/
def levelThreeRoots : Entries :=
  (.node
  (.node
    (.node
      (.node
        (.node
          (.leaf 0)
          (.leaf 11185963))
        (.node
          (.leaf 17430639)
          (.leaf 0)))
      (.node
        (.node
          (.leaf 12325323)
          (.leaf 31638681))
        (.leaf 0)))
    (.node
      (.node
        (.node
          (.leaf 23632294)
          (.leaf 0))
        (.node
          (.leaf 22371926)
          (.leaf 36743944)))
      (.node
        (.node
          (.leaf 0)
          (.leaf 22360260))
        (.leaf 11816147))))
  (.node
    (.node
      (.node
        (.node
          (.leaf 16710556)
          (.leaf 31622183))
        (.node
          (.leaf 0)
          (.leaf 6806456)))
      (.node
        (.node
          (.leaf 15819341)
          (.leaf 0))
        (.leaf 25981892)))
    (.node
      (.node
        (.node
          (.leaf 0)
          (.leaf 13612912))
        (.leaf 19251565))
      (.node
        (.node
          (.leaf 8355278)
          (.leaf 9625783))
        (.leaf 0)))))

/-- All 27 stored entries agree with the executable direct transfer. -/
theorem levelThree_transfer :
    levelThree.checkRange (seedTwo48.directEntry 884635641090634 3 16) 0 27 = true := by
  decide +kernel

/-- The exact integer maximum bounds every entry. -/
theorem levelThree_cap : levelThree.allLE 1350117382722123 = true := by decide +kernel

/-- The maximum is below the retained rational ceiling after scaling. -/
theorem levelThree_max_comparison : 5 * 1350117382722123 ≤ 24 * 2 ^ 48 := by
  decide +kernel

/-- Complete natural energy comparison, including all zero residues. -/
theorem levelThree_energy_comparison :
    200 * ((List.range 27).map (fun i => levelThree.lookup i ^ 2)).sum ≤
      521 * 27 * (2 ^ 48) ^ 2 := by decide +kernel

/-- The root enclosure check covers every one of the 27 entries. -/
theorem levelThree_square_enclosures : ∀ i : Fin 27,
    levelThree.lookup i.val ≤ levelThreeRoots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison with the retained denominator. -/
theorem levelThree_fractional_comparison :
    500000 * ((List.range 27).map
      (fun i => levelThree.lookup i * levelThreeRoots.lookup i)).sum ≤
        769803 * 27 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
