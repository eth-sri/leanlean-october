import RequestProject.OrderNerveRealizationSubtypeHomeomorph


/-! A family of induced subposets containing every simplex realizes as
an actual quotient cover, even for infinitely many pieces. This is a
weak-topology assertion, not a finite closed-cover argument. -/

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory Topology

variable {P : Type} [PartialOrder P] {J : Type} (A : J → Set P)

def orderNervePieceMap j : C(orderNerveRealization (A j), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (Subtype.val : A j → P) (by tauto),
    (orderNerveRealizationMap (Subtype.val : A j → P) (by tauto)).hom.continuous⟩

def orderNervePieceQuotient : C((Σ j, orderNerveRealization (A j)), orderNerveRealization P) :=
  ⟨fun x => orderNervePieceMap A x.1 x.2,
    continuous_sigma (fun j => (orderNervePieceMap A j).continuous)⟩

variable (hc : ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
  ∃ j, ∀ i, s.obj i ∈ A j)

include hc in
theorem orderNervePieceQuotient_surjective : Function.Surjective (orderNervePieceQuotient A) := by
  intro x
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  cases' hc n s with j hj
  exact ⟨⟨j, orderNerveRealizationSimplex _ (orderNerveSimplexSubtype _ s hj) z⟩,
    orderNerveRealizationSimplex_subtype _ s hj z⟩

include hc in
theorem orderNervePieceQuotient_isQuotientMap : IsQuotientMap (orderNervePieceQuotient A) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨orderNervePieceQuotient_surjective A hc, ?_⟩
  intro T
  constructor
  · exact fun hT => hT.preimage (orderNervePieceQuotient A).continuous
  · intro hT
    apply (orderNerveRealization_isClosed_iff P T).mpr
    intro n s
    cases' hc n s with j hj
    have hjT := (isClosed_sigma_iff.mp hT) j
    have hz := hjT.preimage
      (orderNerveRealizationSimplex _ (orderNerveSimplexSubtype _ s hj)).hom.continuous
    convert hz using 1
    ext z
    exact iff_of_eq (congrArg (· ∈ T)
      (orderNerveRealizationSimplex_subtype _ s hj z).symm)

theorem orderNerveRealizationSupported_inter B C :
    orderNerveRealizationSupported P (B ∩ C) =
      orderNerveRealizationSupported P B ∩ orderNerveRealizationSupported P C := by
  ext x
  constructor
  · intro h
    exact ⟨fun p hp => by aesop,
      fun p hp => by aesop⟩
  · rintro ⟨hB, hC⟩ p hp
    by_cases hb : p ∈ B
    · aesop
    tauto

theorem orderNerveRealizationSubtype_preimage_supported (B C : Set P) :
    (orderNerveRealizationMap (Subtype.val : B → P) (fun _ _ h => h)) ⁻¹'
        orderNerveRealizationSupported P C =
      orderNerveRealizationSupported B {b | b.val ∈ C} := by
  ext x
  constructor
  · intro hx b hb
    have h := hx b.val hb
    simp_all [orderNerveRealizationCoordinates_map_injective
      (Subtype.val : B → P) (by tauto) Subtype.val_injective]
  · intro hx p hp
    by_cases hb : p ∈ B
    · have h := hx ⟨p, hb⟩ hp
      exact (orderNerveRealizationCoordinates_map_injective
        _ _ Subtype.val_injective x _).trans h
    · exact orderNerveRealizationCoordinates_map_outside
        _ _ x p (by
          simp_all)
