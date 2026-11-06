module
import Mathlib
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
    simp_all

@[simp] theorem pullback_apply (e : R ≃+* S) (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl

@[simp] theorem pullback_symm (e : R ≃+* S) (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp



theorem primitive_pullback (e : R ≃+* S) (χ : MulChar S ℂ)
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
    rw [hJ] at he
    simp_all <;> nlinarith
  obtain ⟨u, hu, hχu⟩ := hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · change e.symm (u : S) - 1 ∈ I
    change e.symm ((u : S) - 1) ∈ I at hu
    simpa only [map_sub, map_one] using hu
  · simpa [v, pullback] using hχu






