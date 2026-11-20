module

public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem tsum_fractionalIdeal_mul_unit
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) (f : K → ℂ) :
    (∑' x : ↥(I : Submodule (𝓞 K) K),
      f ((algebraMap (𝓞 K) K (u : 𝓞 K)) * (x : K))) =
      ∑' x : ↥(I : Submodule (𝓞 K) K), f (x : K) := by

  let algebraMap₀ := algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
  let e : ↥(I : Submodule (𝓞 K) K) ≃ ↥(I : Submodule (𝓞 K) K) :=
    { toFun := fun x =>
        ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      invFun := fun x =>
        ⟨algebraMap₀ * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show algebraMap₀ *
            (algebraMap (𝓞 K) K u * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        show algebraMap (𝓞 K) K u *
            (algebraMap₀ * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] }

  exact Equiv.tsum_eq e (fun x : ↥I => f (x : K))

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end
