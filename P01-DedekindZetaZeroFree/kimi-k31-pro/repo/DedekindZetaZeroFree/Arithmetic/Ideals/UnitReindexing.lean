module

public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice
public import Mathlib.Tactic.NormNum

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

  let e : ↥(I : Submodule (𝓞 K) K) ≃ ↥(I : Submodule (𝓞 K) K) :=
    { toFun := fun x =>
        ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          norm_num⟩
      invFun := fun x =>
        ⟨algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          norm_num⟩
      left_inv := fun x => by
        norm_num
      right_inv := fun x => by
        norm_num }

  exact Equiv.tsum_eq e (fun x : ↥(I : Submodule (𝓞 K) K) => f (x : K))

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end
