module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Characters.RationalTracePhase
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualsAndFractionalQuotients

@[expose] public section


/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

section
variable (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0)
include I hI
theorem mem_traceDualFractionalIdeal_iff_tracePhase_eq_one
      (z : F) :
    z ∈ traceDualFractionalIdeal I ↔
      ∀ x : F, x ∈ I → rationalTracePhase (Algebra.trace ℚ F (x * z)) = 1 := by
  rw [traceDualFractionalIdeal, FractionalIdeal.mem_dual hI]
  simp only [Algebra.traceForm_apply, mul_comm z, RingHom.mem_range,
    rationalTracePhase_eq_one_iff]
  rfl

def tracePhase_eq_one_of_mem_dual
     
    {x z : F} (hx : x ∈ I) (hz : z ∈ traceDualFractionalIdeal I)  := (mem_traceDualFractionalIdeal_iff_tracePhase_eq_one I hI z).mp hz x hx

@[simp] theorem traceDualFractionalIdeal_traceDualFractionalIdeal
      :
    traceDualFractionalIdeal (traceDualFractionalIdeal I) = I := by
  apply FractionalIdeal.dual_dual

def traceDualFractionalIdeal_ne_zero
       := FractionalIdeal.dual_ne_zero ℤ ℚ hI
end


end DedekindZetaZeroFree.Hecke

end
