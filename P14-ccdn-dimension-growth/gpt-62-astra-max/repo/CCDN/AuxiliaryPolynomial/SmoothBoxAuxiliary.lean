/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.BoxScaling
public import CCDN.Determinant.AffineCongruenceDeterminant
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- On any smooth residue family the lower determinant estimate is made in the
original affine chart. Its columns are the pullbacks of the forms on the lift. -/
theorem BoxScaling.auxiliary {n : ℕ} {f : IntegerPolynomial (n+2)} {B : ℝ} (S : BoxScaling f B)
    (hprim : PrimitiveIntegerPolynomial f) (hir : AbsolutelyIrreducible f) (hd : 0 < f.totalDegree)
    (X : Finset (IntPoint (n+2))) (hbox : ∀ x ∈ X, InBox x B) (hz : ∀ x ∈ X, eval x f = 0)
    (P : Finset ℕ) (a : ℕ → IntPoint (n+2)) (hres : IsSmoothResidueFamily f P a (fun x : X => x.val)) :
    ∃ g : IntegerPolynomial (n+2), ¬ f ∣ g ∧
      (∀ x ∈ X, eval x g = 0) ∧ let Q := ∑ p ∈ P, Real.log p
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree S.p
        (primeSetFactor (largeBadPrimes f hir ∪ P) / Real.exp Q) (integerCoefficientHeight S.equation) + (n+2 : ℝ)*Q := by
  classical
  let e := (Fintype.equivFin X).symm
  let x := fun i => (e i).val
  have hf := ne_zero_of_irreducible_map hir
  let bad := largeBadPrimes f hir
  let Q := ∑ p ∈ P, Real.log p
  let A := primeSetFactor (bad ∪ P) / Real.exp Q
  have heval : EvaluationLower (S.point ∘ x) f.totalDegree A Q := by
    intro s N M b F hs hF
    dsimp only
    intro hi
    have he : (Matrix.of fun i j => eval (x (b i)) (S.pull (F j))) = Matrix.of fun i j => eval (S.point (x (b i))) (F j) := by
      simp [S.pull_eval]
    have hh := affine_congruence_determinant_log_lower hs f hf bad (fun p hp hb => (mem_largeBadPrimes f hir p).2 ⟨hp,hb⟩) hd _ (fun j => S.pull_degree (hF j))
      (x ∘ b) (fun i => hz _ (e _).property) (by lia)
      P a ⟨hres.prime,hres.eval_eq_zero,hres.smooth,fun p hp i => hres.dvd_sub p hp _⟩
    simp only [valueMatrix, Function.comp_apply, he] at hh ⊢
    rw [show Real.log A = (∑ p ∈ bad ∪ P, Real.log p / p) - Q by simp [A, primeSetFactor, Real.log_div _ _, Real.log_exp]]
    dsimp only [hypersurfaceRankLowerBound,hypersurfaceDeterminantMain,factorialRoot,Q] at hh ⊢
    linear_combination hh
  obtain ⟨M,hM,G,hG⟩ := auxiliary_from_evaluation_lower S.equation S.homogeneous (S.ne_zero hf) hd _
    (fun i => by rw [S.eval_eq,hz _ (e i).property,mul_zero]) (by exact_mod_cast S.prime.one_le)
    (fun i => S.point_bound (hbox _ (e i).property)) (by positivity)
    (show 0 ≤ Q by positivity) heval
  refine ⟨S.pull G,S.pull_proper hf hprim hG.isHomogeneous hG.not_dvd,?_,(Nat.cast_le.mpr (S.pull_degree hG.isHomogeneous)).trans hM⟩
  intro y hy
  obtain ⟨i,hi⟩ := e.surjective ⟨y,hy⟩
  simpa [x, hi, S.pull_eval] using hG.eval_eq_zero i

end
end CCDN
