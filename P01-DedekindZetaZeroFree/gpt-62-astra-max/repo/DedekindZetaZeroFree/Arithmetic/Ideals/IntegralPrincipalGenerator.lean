module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.RayUnitary

open scoped NumberField

theorem integral_generator_of_spanSingleton_eq_coeIdeal
    (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) (x : Fˣ)
    (hx : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) =
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :
    ∃ α : 𝓞 F, α ≠ 0 ∧ (α : F) = (x : F) ∧ Ideal.span {α} = I := by
  obtain ⟨α, _, hαx⟩ :=
    (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 F))).mp (by
      rw [← hx]
      exact FractionalIdeal.mem_spanSingleton_self _ _)
  refine ⟨α, ?_, hαx, ?_⟩
  · intro hα0
    have : (0 : F) = (x : F) := by rw [← hαx, hα0, map_zero]
    exact Units.ne_zero x this.symm
  · apply FractionalIdeal.coeIdeal_injective (K := F)
    show ((Ideal.span {α} : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = I
    rw [FractionalIdeal.coeIdeal_span_singleton, hαx, ← hx]

end DedekindZetaZeroFree.RayUnitary
