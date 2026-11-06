module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalChosen
public import OAI.NumberTheory.DirichletL.Reflection.MarkedChosenDual

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CanonicalRowCompletion
noncomputable section

def sourceDependentExtension {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (C : ∀ x, D (f x)) (fallback : ∀ y, D y) (y : Y) : D y :=
  if h : ∃ x, f x=y then h.choose_spec ▸ C h.choose else fallback y

lemma sourceDependentExtension_at {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (hinj : Function.Injective f) (C : ∀ x, D (f x))
    (fallback : ∀ y, D y) (x : X) :
    sourceDependentExtension f C fallback (f x)=C x := by
  have h : ∃ z, f z=f x := by simp
  unfold sourceDependentExtension
  grind

variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

lemma markedActiveSet_injective (e : α⊕β≃γ) :
    Function.Injective (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2) := by
  intro x y he
  have hh := congrArg (optionalPrimeActive (joinedFiberEquiv e)) he
  dsimp only at hh
  rw [← complete_marked_set,← complete_marked_set,
    optionalPrimeActive_completeActiveSet,optionalPrimeActive_completeActiveSet] at hh
  apply Prod.ext
  · simp_all
  simp_all

theorem exists_marked_source_selection (e : α⊕β≃γ)
    (D : Finset (γ⊕σ)→Type*) (fallback : ∀ A, D A)
    (C : ∀ B : Finset β, ∀ T : Finset σ, D (markedActiveSet e B T)) :
    ∃ E : ∀ A, D A, ∀ B T, E (markedActiveSet e B T)=C B T := by
  refine ⟨sourceDependentExtension (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2)
    (fun q => C q.1 q.2) fallback,?_⟩
  intro B T
  exact sourceDependentExtension_at _ (markedActiveSet_injective e) _ _ (B,T)
end
end SevenEighths.InverseReflectedPhase

end OAI
