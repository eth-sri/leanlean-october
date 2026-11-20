module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

namespace MonoidAlgebra

variable {G M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Take the linear combination of the indicated family with the coefficients of a group-ring vector. -/
noncomputable def coeffCombination (f : G → M) : MonoidAlgebra ℤ G →ₗ[ℤ] M :=
  (Finsupp.linearCombination ℤ f).comp (coeffLinearEquiv ℤ).toLinearMap

theorem eq_on_basis {f g : MonoidAlgebra ℤ G →ₗ[ℤ] M}
    (h : ∀ i, f (single i 1) = g (single i 1)) (a : MonoidAlgebra ℤ G) : f a = g a :=
  DFunLike.congr_fun ((basis G ℤ).ext h) a

@[simp] theorem coeffCombination_single (f : G → M) (i : G) (n : ℤ) :
    coeffCombination f (single i n) = n • f i := by
  simp [coeffCombination]

theorem coeffCombination_commutes (F : M →ₗ[ℤ] N) {f : G → M} {g : G → N}
    (h : ∀ i, F (f i) = g i) (a : MonoidAlgebra ℤ G) :
    F (coeffCombination f a) = coeffCombination g a :=
  eq_on_basis (f := F.comp (coeffCombination f)) (fun i => by simp [h]) a

theorem coeffCombination_add (f g : G → M) (a : MonoidAlgebra ℤ G) :
    coeffCombination (fun i => f i + g i) a = coeffCombination f a + coeffCombination g a :=
  eq_on_basis (g := coeffCombination f + coeffCombination g) (fun i => by simp) a

theorem coeffCombination_mem {f : G → M} {S : AddSubgroup M}
    (h : ∀ i, f i ∈ S) (a : MonoidAlgebra ℤ G) : coeffCombination f a ∈ S := by
  change Finsupp.linearCombination ℤ f a.coeff ∈ S
  exact S.sum_mem fun i _ => S.zsmul_mem (h i) _

end MonoidAlgebra
