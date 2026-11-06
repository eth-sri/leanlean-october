import RequestProject.OrderNormalizationNaturality
import RequestProject.Tac


/-! Faithfulness of actual normalized strict maps on retained vertex sets. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A monotone map injective on the vertices supporting a strict two-chain reflects
zero of its actual normalized chain image. -/
theorem normalizedStrictChain2_zero_of_injOn (f : P → Q) hf
    S (hinj : Set.InjOn f S) r
    (hr : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hz : normalizedStrictChain2 f hf r = 0) : r = 0 := by
  classical
  let D := {t : StrictOrdTri P // t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S}
  let incl : D → StrictOrdTri P := Subtype.val
  have hstrict (t : D) : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 := by
    constructor
    · exact lt_of_le_of_ne (hf t.1.2.1.le)
        (fun he => t.1.2.1.ne (hinj t.2.1 t.2.2.1 he))
    · exact lt_of_le_of_ne (hf t.1.2.2.le)
        (fun he => t.1.2.2.ne (hinj t.2.2.1 t.2.2.2 he))
  let image : D → StrictOrdTri Q := fun t =>
    ⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), hstrict t⟩
  have himage : image.Injective := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hinj a.2.1 b.2.1 (by grind)
    · apply Prod.ext
      · exact hinj a.2.2.1 b.2.2.1 (by grind)
      · exact hinj a.2.2.2 b.2.2.2 (by grind)
  let z := r.comapDomain incl Subtype.val_injective.injOn
  have hrecon : Finsupp.mapDomain incl z = r := by
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro t ht
    simp_all
  have hmap (w : D →₀ ℤ) :
      normalizedStrictChain2 f hf (Finsupp.mapDomain incl w) = Finsupp.mapDomain image w := by
    lin_ind w with w z hw hz => simp [Finsupp.mapDomain_add, map_add, hw, hz]
    | t n =>
        rw [Finsupp.mapDomain_single, normalizedStrictChain2_single, Finsupp.mapDomain_single]
        have hn : normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF (incl t))) =
            Finsupp.single (image t) 1 := by
          change (if h : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 then
            Finsupp.single ⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), h⟩ 1
            else 0) = Finsupp.single (image t) 1
          aesop
        simp_all
  have hz' : Finsupp.mapDomain image z = 0 := by grind
  have he := Finsupp.mapDomain_injective himage (hz'.trans Finsupp.mapDomain_zero.symm)
  simp_all
