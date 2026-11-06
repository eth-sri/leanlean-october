import Mathlib.Tactic

import RequestProject.OrderNormalizationSupport

/-! Normalized strict two-chain maps of actual monotone maps. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

  (f : P → Q)
  (hf : Monotone f)
noncomputable def normalizedStrictChain2   :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdTri Q →₀ ℤ) :=
  normalizeOrdChain2.comp ((chain2 (orderCxMap f hf)).comp (chain2 (strictOrderIncl P)))

/-- Mapping a weak two-chain and then normalizing agrees with first normalizing its
source and applying the actual normalized strict chain map. -/
theorem normalizeOrdChain2_map   (z : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf) z) =
      normalizedStrictChain2 f hf (normalizeOrdChain2 z) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single t n =>
      obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
      by_cases he1 : a = b
      · simp_all [orderCxMap, normalizeOrdChain2, normalizeOrdTriangle]
      · by_cases he2 : b = c
        · simp_all [orderCxMap, normalizeOrdChain2, normalizeOrdTriangle]
        · have hab'  := lt_of_le_of_ne hab he1
          have hbc'  := lt_of_le_of_ne hbc he2
          have hs : normalizeOrdChain2
              (Finsupp.single (⟨(a, b, c), hab, hbc⟩ : OrdTri P) n) =
              Finsupp.single (⟨(a, b, c), hab', hbc'⟩ : StrictOrdTri P) n := by
            simp_all [normalizeOrdTriangle]
          change normalizeOrdChain2 (chain2 (orderCxMap f hf)
              (Finsupp.single (⟨(a, b, c), hab, hbc⟩ : OrdTri P) n)) =
            normalizeOrdChain2 (chain2 (orderCxMap f hf) (chain2 (strictOrderIncl P)
              (normalizeOrdChain2 (Finsupp.single (⟨(a, b, c), hab, hbc⟩ : OrdTri P) n))))
          aesop

theorem normalizedStrictChain2_single  
    (t : StrictOrdTri P) (n : ℤ) :
    normalizedStrictChain2 f hf (Finsupp.single t n) =
      n • normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF t)) := by
  change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
    (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain2_single]

end FiniteChains.Comb
