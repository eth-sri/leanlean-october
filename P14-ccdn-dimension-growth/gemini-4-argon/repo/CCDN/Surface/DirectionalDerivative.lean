/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineLineLeading
public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
import CCDN.Algebra.BinaryHomogeneousIrreducibility
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Surface.LineDirections
import CCDN.Surface.TopFormIrreducibility

/-! Directional derivatives of surfaces with absolutely irreducible top form. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The derivative `∑ i, v i * ∂f/∂xᵢ` of the polynomial `f` in the direction `v`. -/
def directionalDerivative {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, C (v i) * pderiv i f

/-- A directional derivative of `f` has total degree at most `f.totalDegree - 1`. -/
lemma directionalDerivative_totalDegree_le {K σ : Type*} [Field K] [Fintype σ]
    (v : σ → K) (f : MvPolynomial σ K) :
    (directionalDerivative v f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  exact totalDegree_finsetSum_le fun i _ =>
    (totalDegree_mul _ _).trans (by simpa using pderiv_totalDegree_le f i)

/-- If the integer surface equation `f` has degree at least two and an absolutely irreducible
top-degree form, then its derivative over `ℚ` in every nonzero direction `v` is nonzero. -/
theorem surface_directionalDerivative_ne_zero
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    directionalDerivative v (map (Int.castRingHom ℚ) f) ≠ 0 := by
  classical
  let K := AlgebraicClosure ℚ
  let φ := algebraMap ℚ K
  let fq := map (Int.castRingHom ℚ) f
  let d := f.totalDegree
  have hir' : Irreducible (map φ (homogeneousComponent d fq)) := by
    rw [← map_homogeneousComponent, map_map]; convert hir using 1; congr 1
  have hhom : (map φ (homogeneousComponent d fq)).IsHomogeneous d := by
    rw [map_homogeneousComponent]; exact homogeneousComponent_isHomogeneous _ _
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  let e : Fin 3 ≃ Fin 3 := Equiv.swap j 0
  let vK : Fin 3 → K := fun i => φ (v i)
  let w : Fin 3 → K := fun i => vK (e.symm i)
  have hw : w 0 ≠ 0 := by simpa [w, vK, e] using hj
  let F := rename e (map φ (homogeneousComponent d fq))
  let a : Fin 2 → K := fun i => w i.succ / w 0
  let G := homogeneousTranslation K a F
  have hG : G.IsHomogeneous d := homogeneousTranslation_homogeneous a hhom.rename_isHomogeneous
  have hiG : Irreducible G :=
    (MulEquiv.irreducible_iff (f := (homogeneousTranslation K a).toMulEquiv)).mpr
      ((MulEquiv.irreducible_iff (f := (renameEquiv K e).toMulEquiv)).mpr hir')
  intro hz
  have hpderiv_hom (i : Fin 3) :
      pderiv i (homogeneousComponent d fq) = homogeneousComponent (d - 1) (pderiv i fq) := by
    ext m
    have he : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      change (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1
      rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]; simp
    rw [coeff_pderiv, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_pderiv, he]
    by_cases hm : m.degree = d - 1
    · simp [hm, Nat.sub_add_cancel (by omega : 0 < d)]
    · simp [hm, show m.degree + 1 ≠ d by omega]
  have hmap : directionalDerivative vK (map φ (homogeneousComponent d fq)) = 0 := by
    calc directionalDerivative vK (map φ (homogeneousComponent d fq))
      _ = map φ (directionalDerivative v (homogeneousComponent d fq)) := by
        simp [vK, directionalDerivative, pderiv_map]
      _ = map φ (homogeneousComponent (d - 1) (directionalDerivative v fq)) := by
        simp only [directionalDerivative, map_sum, homogeneousComponent_C_mul, hpderiv_hom]
      _ = 0 := by rw [hz, map_zero, map_zero]
  have hzw : directionalDerivative w F = 0 := by
    calc directionalDerivative w F
      _ = rename e (directionalDerivative vK (map φ (homogeneousComponent d fq))) := by
        unfold directionalDerivative
        rw [← e.sum_comp]
        simp only [w, F, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul,
          rename_C]
      _ = 0 := by rw [hmap, map_zero]
  have h : C (w 0) * pderiv 0 G = homogeneousTranslation K a (directionalDerivative w F) := by
    let tr := homogeneousTranslation K a
    have hX (i : Fin 3) : C (w 0) * pderiv 0 (tr (X i)) = C (w i) := by
      refine Fin.cases (by simp [tr, homogeneousTranslation, homogeneousTranslationHom]) (fun k => ?_) i
      simp only [tr, a, homogeneousTranslation, homogeneousTranslationHom, AlgEquiv.ofAlgHom_apply,
        aeval_X, Fin.cons_succ, map_add, pderiv_mul, pderiv_X_of_ne (Fin.succ_ne_zero k), pderiv_C,
        zero_mul, pderiv_X_self, mul_one, zero_add, ← C_mul]
      rw [mul_div_cancel₀ _ hw]
    have hchain := MvPolynomial.pderiv_algHom tr.toAlgHom F 0
    change pderiv 0 G = ∑ i, tr (pderiv i F) * pderiv 0 (tr (X i)) at hchain
    rw [hchain, Finset.mul_sum]
    simp only [directionalDerivative, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show tr (C (w i)) = C (w i) from tr.commutes _, ← hX i]; ring
  rw [hzw, map_zero] at h
  have hpz : pderiv 0 G = 0 := (mul_eq_zero.mp h).resolve_left (by simpa using hw)
  have hv0 := notMem_vars_of_pderiv_eq_zero hpz fun n hn _ => Nat.cast_ne_zero.mpr hn.ne'
  have hs : ↑G.vars ⊆ Set.range (Fin.succ : Fin 2 → Fin 3) := fun i =>
    Fin.cases (fun hi => (hv0 hi).elim) (fun k _ => ⟨k, rfl⟩) i
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range G Fin.succ (Fin.succ_injective 2) hs
  have hgh : g.IsHomogeneous d :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective 2)).mp (hg ▸ hG)
  have hev (q : MvPolynomial (Fin 2) K) : eval₂Hom C (Fin.cons 0 X) (rename Fin.succ q) = q := by
    rw [eval₂Hom_rename, show Fin.cons (0 : MvPolynomial (Fin 2) K) X ∘ Fin.succ = X by
      funext i; simp]; simp
  have hgi : Irreducible g := by
    have hrg : Irreducible (rename Fin.succ g) := hg ▸ hiG
    refine ⟨fun hu => hrg.not_isUnit (hu.map (rename Fin.succ)), fun p q hpq => ?_⟩
    rcases hrg.isUnit_or_isUnit (by rw [hpq, map_mul]) with hp | hq
    · exact Or.inl (by simpa only [hev] using hp.map (eval₂Hom C (Fin.cons 0 X)))
    · exact Or.inr (by simpa only [hev] using hq.map (eval₂Hom C (Fin.cons 0 X)))
  have := binary_homogeneous_irreducible_degree_le_one g hgh hgi
  omega

/-- If the rational affine line through `a` with direction `v` lies on the hypersurface
`f = 0`, then it also lies on the zero set of the derivative of `f` in the direction `v`. -/
theorem rationalAffineLine_contained_directionalDerivative {n : ℕ}
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    rationalAffineLine a v ⊆ zeroLocus (directionalDerivative v f) := by
  /- Every directional derivative of a constant polynomial is zero. -/
  /- The derivative of the coordinate `X j` in the direction `v` is the constant `v j`. -/
  rintro z ⟨t, rfl⟩
  have hpoly : affineLinePolynomial a v f = 0 :=
    Polynomial.zero_of_eval_zero _ fun s => by rw [eval_affineLinePolynomial]; exact hline ⟨s, rfl⟩
  have hder (p : CoordinatePolynomial n) :
      Polynomial.derivative (affineLinePolynomial a v p) =
        affineLinePolynomial a v (directionalDerivative v p) := by
    induction p using MvPolynomial.induction_on with
    | C r => simp [affineLinePolynomial, directionalDerivative]
    | add p g hp hg =>
      simp only [map_add, hp, hg, directionalDerivative, mul_add, Finset.sum_add_distrib]
    | mul_X p j hp =>
      have hmul : directionalDerivative v (p * X j) =
          directionalDerivative v p * X j + p * C (v j) := by
        rw [show C (v j) = directionalDerivative v (X j) by
          simp [directionalDerivative, pderiv_X, Pi.single_apply]]
        simp only [directionalDerivative, pderiv_mul, mul_add, Finset.sum_add_distrib,
          Finset.sum_mul, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [map_mul, Polynomial.derivative_mul, hp, hmul, map_add, map_mul, map_mul]
      simp [affineLinePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]
  have hf := hder f
  rw [hpoly, Polynomial.derivative_zero] at hf
  change eval (a + t • v) (directionalDerivative v f) = 0
  rw [← eval_affineLinePolynomial, ← hf, Polynomial.eval_zero]

end
end CCDN
