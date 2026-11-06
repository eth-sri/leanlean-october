module

public import OAI.NumberTheory.PrimeGaps.EulerProducts

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set

open scoped ContDiff





section FourierNormalization


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def frequencyDilation : V ≃L[ℝ] V :=
  Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)) • ContinuousLinearEquiv.refl ℝ V

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem frequencyDilation_apply (u : V) :
    frequencyDilation u = (2*Real.pi)⁻¹ • u := rfl

noncomputable def laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  (show HasCompactSupport (fun v => Complex.exp (ℓ v : ℂ)*F v) from hF.mul_left).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp ℓ.contDiff).cexp).mul hFs)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceSchwartz_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    laplaceSchwartz ℓ F hF hFs v = Complex.exp (ℓ v : ℂ)*F v := rfl

end FourierNormalization

def primePrefix (y : ℕ) : Finset Nat.Primes := (Nat.primesLE y).subtype Nat.Prime

@[simp] theorem mem_primePrefix (y : ℕ) (p : Nat.Primes) :
    p∈primePrefix y ↔ (p:ℕ)≤y :=
  (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE y) (a := p)).trans
    (by rw [Nat.mem_primesLE]; grind)

noncomputable def primeReciprocalPrefix (y : ℕ) : ℝ :=
  ∑ p∈primePrefix y, (p:ℝ)⁻¹

abbrev EulerChoices {κ : Type*} (A : κ → Type*) :=
  Σ P : Finset κ, (p : P) → A p

end LargePrimeGaps

end OAI
