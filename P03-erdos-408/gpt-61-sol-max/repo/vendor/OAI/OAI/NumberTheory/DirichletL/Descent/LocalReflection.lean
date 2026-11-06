module
public import Mathlib.Tactic

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F)  :=
  ∑ t : F, f t * ψ (-(h * t))

theorem localFourier_zeroMark (ψ : AddChar F ℂ)  h  :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero  ψ 
    (hψ : ψ.IsPrimitive)  h  (hh : h ≠ 0) :
    localFourier ((1 : MulChar F ℂ)) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F)  :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

theorem marked_active_eq_neg_trivial  χ 
     ψ  (hψ : ψ.IsPrimitive)  σ ε   x  :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive ((1 : MulChar F ℂ)) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  simp_all [localFourier_zeroMark, localFourier_trivial_nonzero]

end

end SevenEighths.InverseMoment

end OAI
