module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R σ : Type*}

def linearForm [CommSemiring R] [Fintype σ] (a : σ → R) : MvPolynomial σ R :=
  ∑ i, C (a i) * X i

variable [CommSemiring R] [Fintype σ]

lemma linearForm_isHomogeneous (a : σ → R) : (linearForm a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i)

lemma linearForm_totalDegree_le (a : σ → R) : (linearForm a).totalDegree ≤ 1 :=
  (linearForm_isHomogeneous a).totalDegree_le

@[simp] lemma eval_linearForm (a x : σ → R) : eval x (linearForm a) = ∑ i, a i * x i := by
  simp [linearForm]

end
end CCDN
