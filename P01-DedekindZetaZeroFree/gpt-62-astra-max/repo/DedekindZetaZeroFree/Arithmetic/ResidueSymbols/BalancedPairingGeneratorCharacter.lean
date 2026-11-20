module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Basic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : R → M → ℂ) (hzero : ∀ t, B 0 t = 1) (hadd : ∀ x y t, B (x + y) t = B x t * B y t)

def balancedPairingGeneratorChar (z : M) : AddChar R ℂ where
  toFun k := B k z
  map_zero_eq_one' := hzero z
  map_add_eq_mul' x y := hadd x y z

@[simp] theorem balancedPairingGeneratorChar_apply (z : M) (k : R) :
    balancedPairingGeneratorChar B hzero hadd z k = B k z := rfl

theorem balancedPairingGeneratorChar_primitive
    (hbalanced : ∀ r k t, B (r * k) t = B k (r • t))
    (hleft : ∀ k, (∀ t, B k t = 1) → k = 0)
    (z : M) (hz : Function.Surjective (fun r : R => r • z)) :
    ∀ J : Ideal R,
      (∀ x ∈ J, balancedPairingGeneratorChar B hzero hadd z x = 1) → J = ⊥ := by
  intro J hJ
  refine le_bot_iff.mp fun x hx => ?_
  simp
  refine hleft x fun t => ?_
  obtain ⟨r, hr⟩ := hz t
  rw [← hr]
  rw [← hbalanced r x z]
  exact hJ (r * x) (J.mul_mem_left r hx)

end DedekindZetaZeroFree.Hecke
