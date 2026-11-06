import RequestProject.OrderNormalizationSupport
import RequestProject.Tac


/-! Normalized strict two-chain maps of actual monotone maps. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def normalizedStrictChain2 (f : P → Q) (hf : Monotone f) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdTri Q →₀ ℤ) :=
  normalizeOrdChain2.comp ((chain2 (orderCxMap f hf)).comp (chain2 (strictOrderIncl P)))

/-- Mapping a weak two-chain and then normalizing agrees with first normalizing its
source and applying the actual normalized strict chain map. -/
theorem normalizeOrdChain2_map (f : P → Q) hf (z : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf) z) =
      normalizedStrictChain2 f hf (normalizeOrdChain2 z) := by
  classical
  lin_ind z with z w hz hw => simp only [map_add, hz, hw]
  | t n =>
      obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
      by_cases he1 : a = b
      · subst b
        simp [normalizedStrictChain2, chain2, orderCxMap, normalizeOrdChain2,
          normalizeOrdTriangle]
      · by_cases he2 : b = c
        · subst c
          simp [normalizedStrictChain2, chain2, orderCxMap, normalizeOrdChain2,
            normalizeOrdTriangle]
        · have hab' := lt_of_le_of_ne hab he1
          have hbc' := lt_of_le_of_ne hbc he2
          have hs : normalizeOrdChain2
              (Finsupp.single ⟨(a, b, c), hab, hbc⟩ n) =
              Finsupp.single ⟨(a, b, c), hab', hbc'⟩ n := by
            simp [normalizeOrdChain2, normalizeOrdTriangle, hab', hbc']
          change normalizeOrdChain2 (chain2 (orderCxMap f hf)
              (Finsupp.single ⟨(a, b, c), hab, hbc⟩ n)) =
            normalizeOrdChain2 (chain2 (orderCxMap f hf) (chain2 (strictOrderIncl P)
              (normalizeOrdChain2 (Finsupp.single ⟨(a, b, c), hab, hbc⟩ n))))
          aesop

theorem normalizedStrictChain2_single (f : P → Q) hf
    t n :
    normalizedStrictChain2 f hf (Finsupp.single t n) =
      n • normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF t)) := by
  change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
    (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) = _
  simp
