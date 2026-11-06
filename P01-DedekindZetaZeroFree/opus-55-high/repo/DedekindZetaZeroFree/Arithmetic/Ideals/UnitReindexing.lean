module

public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section


open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem tsum_fractionalIdeal_mul_unit
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) (f : K → ℂ) :
    (∑' x : ↥(I : Submodule (𝓞 K) K),
      f ((algebraMap (𝓞 K) K (u : 𝓞 K)) * (x : K))) =
      ∑' x : ↥(I : Submodule (𝓞 K) K), f (x : K) := by

  let e : ↥(I : Submodule (𝓞 K) K) ≃ ↥(I : Submodule (𝓞 K) K) :=
    { toFun := fun x =>
        ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          simp⟩
      invFun := fun x =>
        ⟨algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          simp⟩
      left_inv := fun x => by
        simp
      right_inv := fun x => by
        simp }

  exact Equiv.tsum_eq e (fun x : ↥(I : Submodule (𝓞 K) K) => f (x : K))
