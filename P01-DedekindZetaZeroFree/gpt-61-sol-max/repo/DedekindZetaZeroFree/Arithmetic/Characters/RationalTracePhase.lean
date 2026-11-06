module

public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section


noncomputable section

namespace DedekindZetaZeroFree.Hecke

def rationalTracePhase : AddChar ℚ ℂ where
  toFun q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro q r
    simp only [Rat.cast_add, mul_add, Complex.exp_add]

section
variable (q : ℚ)
include q
@[simp] theorem rationalTracePhase_apply   :
    rationalTracePhase q = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ)) :=
  rfl

theorem rationalTracePhase_apply_real   :
    rationalTracePhase q =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((q : ℝ) : ℂ)) := rfl

theorem rationalTracePhase_eq_one_iff   :
    rationalTracePhase q = 1 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [rationalTracePhase_apply, Complex.exp_eq_one_iff]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero <;> aesop
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (q : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hc
      simpa only [mul_comm] using hn
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (n : ℂ) = (q : ℂ) := by exact_mod_cast hn
    rw [← h, mul_comm]

@[simp] theorem norm_rationalTracePhase   :
    ‖rationalTracePhase q‖ = 1 := by
  rw [rationalTracePhase_apply, Complex.norm_exp]
  simp

theorem rationalTracePhase_ne_zero   :
    rationalTracePhase q ≠ 0 := Complex.exp_ne_zero _
end


end DedekindZetaZeroFree.Hecke

end
