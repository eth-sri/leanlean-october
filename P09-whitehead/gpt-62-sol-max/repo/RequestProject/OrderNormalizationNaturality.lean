module

public import RequestProject.OrderNormalizationSupport
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Normalized strict two-chain maps of actual monotone maps. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def normalizedStrictChain2 (f : P → Q) (hf : Monotone f) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdTri Q →₀ ℤ) :=
  normalizeOrdChain2.comp ((chain2 (orderCxMap f hf)).comp (chain2 (strictOrderIncl P)))

theorem normalizedStrictChain2_single (f : P → Q) (hf : Monotone f)
    (t : StrictOrdTri P) (n : ℤ) :
    normalizedStrictChain2 f hf (Finsupp.single t n) =
      n • normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF t)) := by
  change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
    (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain2_single]

/-- Mapping a weak two-chain and then normalizing agrees with first normalizing its
source and applying the actual normalized strict chain map. -/
theorem normalizeOrdChain2_map (f : P → Q) (hf : Monotone f) (z : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf) z) =
      normalizedStrictChain2 f hf (normalizeOrdChain2 z) := by
  classical
  finsupp_singles z
  intro t n
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  rw [chain2_apply, Finsupp.mapDomain_single]
  erw [normalizeOrdChain2_single, normalizeOrdChain2_single ⟨(a,b,c), hab, hbc⟩ n, map_smul]
  by_cases h₁ : a = b
  · subst b
    simp [normalizeOrdTriangle, orderCxMap]
  by_cases h₂ : b = c
  · subst c
    simp [normalizeOrdTriangle, orderCxMap]
  have ha : a < b := lt_of_le_of_ne hab h₁
  have hb : b < c := lt_of_le_of_ne hbc h₂
  have hs : normalizeOrdTriangle ⟨(a,b,c), hab, hbc⟩ = Finsupp.single ⟨(a,b,c), ha, hb⟩ 1 := by
    simp [normalizeOrdTriangle, ha, hb]
  rw [hs]
  rw [normalizedStrictChain2_single, one_smul] <;> rfl

end FiniteChains.Comb
