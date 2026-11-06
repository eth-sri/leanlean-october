module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.FiniteConductor

@[expose] public section

namespace OAI

namespace SevenEighths.CharacterTransport

open SevenEighths.FiniteFourier

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simpa using h.map e.symm.toMonoidHom

section
variable (e : R ≃+* S) (χ ψ : MulChar S ℂ)


@[simp] theorem pullback_apply     (x : R) :
    pullback e χ x = χ (e x) := rfl

@[simp] theorem pullback_symm     :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp



theorem primitive_pullback    
    (hχ : IsPrimitiveOnIdeals χ) : IsPrimitiveOnIdeals (pullback e χ) := by
  intro I hI
  let J : Ideal S := I.comap e.symm.toRingHom
  have hJ : J ≠ ⊥ := by
    intro hJ
    apply hI
    apply le_antisymm _ bot_le
    intro x hx
    have he : e x ∈ J := by
      change e.symm (e x) ∈ I
      simpa using hx
    simp_all
  obtain ⟨u, hu, hχu⟩ := hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · aesop
  · simpa [v, pullback] using hχu

end

end

end SevenEighths.CharacterTransport

end OAI
