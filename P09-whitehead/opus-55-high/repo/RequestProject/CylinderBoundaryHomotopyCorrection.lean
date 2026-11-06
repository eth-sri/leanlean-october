import RequestProject.HomeomorphContinuousMap
import RequestProject.CylinderBoundaryPasting
import RequestProject.BallCylinderHomotopyExtension


/-! Turn a homotopy with a contractible boundary track into a homotopy
relative to that boundary. Endpoint maps are retained exactly. -/

namespace FiniteChains.RelativeAttachment
open scoped unitInterval

variable {D Z : Type u} [TopologicalSpace D] [TopologicalSpace Z]

theorem homotopyRel_of_boundaryContraction S (hS : IsClosed S)
    (hext : HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary S → I × D))
    {f₀ f₁ : C(D, Z)} (F : f₀.Homotopy f₁)
    (J : C(I × (I × S), Z))
    (hJ₀ : ∀ t a, J (0, (t, a)) = F (t, a.val))
    (hJ₁ : ∀ t a, J (1, (t, a)) = f₀ a.val)
    (hJl : ∀ s a, J (s, (0, a)) = f₀ a.val)
    (hJr : ∀ s a, J (s, (1, a)) = f₁ a.val) :
    f₀.HomotopicRel f₁ S := by
  let P₀ : C(D, C(I, Z)) := {
    toFun := fun d => ContinuousMap.const I (f₀ d)
    continuous_toFun := ContinuousMap.continuous_const'.comp f₀.continuous }
  let P₁ : C(D, C(I, Z)) := {
    toFun := fun d => ContinuousMap.const I (f₁ d)
    continuous_toFun := ContinuousMap.continuous_const'.comp f₁.continuous }
  let PS : C(I × S, C(I, Z)) :=
    (J.comp ⟨fun z => (z.2, z.1), continuous_swap⟩).curry
  have hP₀ : ∀ a, PS (0, a) = P₀ a.val := by
    intro a
    apply ContinuousMap.ext
    tauto
  have hP₁ : ∀ a, PS (1, a) = P₁ a.val := by
    intro a
    apply ContinuousMap.ext
    tauto
  let PB : C(FullCylinderBoundary S, C(I, Z)) :=
    fullCylinderPasting S hS P₀ P₁ PS hP₀ hP₁
  let HB : C(I × FullCylinderBoundary S, Z) :=
    PB.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hBleft (s : I) (d : D) :
      HB (s, ⟨(0, d), Or.inl rfl⟩) = f₀ d := by
    aesop
  have hBright (s : I) (d : D) :
      HB (s, ⟨(1, d), Or.inr (Or.inl rfl)⟩) = f₁ d := by
    aesop
  have hBside (s t : I) (a : S) :
      HB (s, ⟨(t, a.val), Or.inr (Or.inr a.property)⟩) = J (s, (t, a)) := by
    aesop
  have hB₀ : ∀ b, HB (0, b) = F b.val := by
    intro b
    rcases b.property with hb | hb | hb
    · aesop
    · aesop
    · exact (hBside 0 b.val.1 ⟨b.val.2, hb⟩).trans (hJ₀ _ _)
  obtain ⟨G, _, hGB⟩ := hext Z F.toContinuousMap HB hB₀
  refine ⟨{
    toFun := fun td => G (1, td)
    continuous_toFun := G.continuous.comp (continuous_const.prodMk continuous_id)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro d
    exact (hGB 1 _).trans (hBleft 1 d)
  · intro d
    exact (hGB 1 _).trans (hBright 1 d)
  · intro t d hd
    exact (hGB 1 _).trans
      ((hBside 1 t ⟨d, hd⟩).trans (hJ₁ t _))
