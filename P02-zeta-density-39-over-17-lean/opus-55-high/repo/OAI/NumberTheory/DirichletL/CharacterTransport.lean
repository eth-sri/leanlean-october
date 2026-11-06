module
public import OAI.NumberTheory.DirichletL.FiniteConductor
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CharacterTransport

open SevenEighths.FiniteFourier

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by grind
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simp_all

section
variable (e : R ≃+* S)
include e
@[simp] theorem pullback_apply (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl

@[simp] theorem pullback_symm (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp

@[simp] theorem pullback_mul (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by
  apply MulChar.ext'
  intro x
  rfl

theorem primitive_pullback (χ : MulChar S ℂ)
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
      simp_all
    rw [hJ] at he
    have hx0 : x = 0 := e.injective (by simp_all)
    exact hx0
  pm_98 u hu hχu hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  aesop
  aesop
end

end

end SevenEighths.CharacterTransport

end OAI
