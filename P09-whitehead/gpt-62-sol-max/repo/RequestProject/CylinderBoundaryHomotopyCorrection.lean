module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.CylinderBoundaryPasting
public import RequestProject.BallCylinderHomotopyExtension

@[expose] public section

/-! Turn a homotopy with a contractible boundary track into a homotopy
relative to that boundary. Endpoint maps are retained exactly. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D Z : Type u} [TopologicalSpace D] [TopologicalSpace Z]

theorem homotopyRel_of_boundaryContraction (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary S → I × D))
    {f₀ f₁ : C(D, Z)} (F : f₀.Homotopy f₁)
    (J : C(I × (I × S), Z))
    (hJ₀ : ∀ t a, J (0, (t, a)) = F (t, a.val))
    (hJ₁ : ∀ t a, J (1, (t, a)) = f₀ a.val)
    (hJl : ∀ s a, J (s, (0, a)) = f₀ a.val)
    (hJr : ∀ s a, J (s, (1, a)) = f₁ a.val) :
    f₀.HomotopicRel f₁ S := by
  let endpoint (f : C(D, Z)) := (f.comp (ContinuousMap.fst : C(D × I, D))).curry
  let PS := (J.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hP₀ : ∀ a, PS (0, a) = endpoint f₀ a.val := fun a => ContinuousMap.ext fun s => hJl s a
  have hP₁ : ∀ a, PS (1, a) = endpoint f₁ a.val := fun a => ContinuousMap.ext fun s => hJr s a
  let PB := fullCylinderPasting S hS (endpoint f₀) (endpoint f₁) PS hP₀ hP₁
  let HB := PB.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hend (s t : I) (ht : t = 0 ∨ t = 1) (d : D) :
      HB (s, ⟨(t, d), ht.imp id Or.inl⟩) = (if t = 0 then f₀ d else f₁ d) := by
    have h := congrArg (fun f : C(I, Z) => f s)
      (fullCylinderPasting_end S hS (endpoint f₀) (endpoint f₁) PS hP₀ hP₁ t ht d)
    change HB (s, ⟨(t, d), _⟩) = _ at h
    split_ifs at h ⊢ <;> exact h
  have hBleft (s : I) (d : D) : HB (s, ⟨(0, d), Or.inl rfl⟩) = f₀ d := by
    simpa only [ite_eq_left rfl, if_true] using hend s 0 (Or.inl rfl) d
  have hBright (s : I) (d : D) : HB (s, ⟨(1, d), Or.inr (Or.inl rfl)⟩) = f₁ d := by
    simpa only [ite_eq_right one_ne_zero] using hend s 1 (Or.inr rfl) d
  have hBside (s t : I) (a : S) := congrArg (fun f  => f s)
      (fullCylinderPasting_side S hS (endpoint f₀) (endpoint f₁) PS hP₀ hP₁ t a)
  have hB₀ : ∀ b : FullCylinderBoundary S, HB (0, b) = F b.val := by
    rintro ⟨⟨t, d⟩, ht | ht | hd⟩
    · change t = 0 at ht
      subst t
      exact (hBleft 0 d).trans (F.apply_zero d).symm
    · change t = 1 at ht
      subst t
      exact (hBright 0 d).trans (F.apply_one d).symm
    · exact (hBside 0 t ⟨d, hd⟩).trans (hJ₀ _ _)
  obtain ⟨G, _, hGB⟩ := hext Z F.toContinuousMap HB hB₀
  refine ⟨{
    toFun := fun td => G (1, td)
    continuous_toFun := G.continuous.comp (continuous_const.prodMk continuous_id)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro d
    exact (hGB 1 ⟨(0, d), Or.inl rfl⟩).trans (hBleft 1 d)
  · intro d
    exact (hGB 1 ⟨(1, d), Or.inr (Or.inl rfl)⟩).trans (hBright 1 d)
  · intro t d hd
    exact (hGB 1 ⟨(t, d), Or.inr (Or.inr hd)⟩).trans
      ((hBside 1 t ⟨d, hd⟩).trans (hJ₁ t ⟨d, hd⟩))

end FiniteChains.RelativeAttachment
