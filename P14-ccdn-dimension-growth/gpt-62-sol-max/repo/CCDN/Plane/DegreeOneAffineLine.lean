/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.ForMathlib.KrullHeight
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
import CCDN.Algebra.LinearForm
import CCDN.Projection.HilbertProjectionDegree
import CCDN.Projection.DerivativeReconstruction
import CCDN.Hilbert.FilteredHilbertLinearity
import CCDN.Hilbert.LinearCoordinates
import CCDN.Hilbert.PrimeComponentTranscendence

/-! The linear projections of a degree-one curve yield its affine coordinate expressions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma eq_affine_of_totalDegree_le_one {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : f.totalDegree ≤ 1) :
    f = C (f.coeff 0) + linearForm (fun i => f.coeff (Finsupp.single i 1)) := by
  classical
  ext m
  by_cases h0 : m = 0
  · subst m
    simp [linearForm, C_mul_X_eq_monomial, coeff_monomial]
  by_cases h1 : m.degree = 1
  · obtain ⟨i, rfl⟩ : m ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rwa [Finsupp.range_single_one]
    simp [linearForm, C_mul_X_eq_monomial, coeff_monomial, coeff_C, Finsupp.single_eq_single_iff,
      (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero : Finsupp.single i 1 ≠ 0))]
  have hm : f.totalDegree < m.degree := by
    have := (Finsupp.degree_eq_zero_iff m).not.mpr h0
    omega
  have he (i : σ) : Finsupp.single i 1 ≠ m := fun h => h1 (h ▸ Finsupp.degree_single i 1)
  simp [coeff_eq_zero_of_totalDegree_lt hm, linearForm, C_mul_X_eq_monomial, coeff_monomial,
    coeff_C, Ne.symm h0, he]

/-- A degree-one prime curve has affine coordinate
formulas over that same field. In particular this holds directly over `ℚ`. -/
private theorem degree_one_coordinates_affine {K : Type*} [Field K] [CharZero K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (hdegree : HasFilteredCurveDegree p 1) :
    ∃ (j : Fin 3) (c d : Fin 3 → K), c j ≠ 0 ∧
      Transcendental K ((Ideal.Quotient.mk p) (X j)) ∧ ∀ k,
      (Ideal.Quotient.mk p) (X k) =
        c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k) := by
  obtain ⟨j, hj⟩ := exists_transcendental_coordinate_of_curve p one_pos hdegree
  let A := MvPolynomial (Fin 3) K ⧸ p
  let ι := algebraMap K A
  let u : A := (Ideal.Quotient.mk p) (X j)
  have hex (k : Fin 3) : ∃ c d : K, (Ideal.Quotient.mk p) (X k) = ι c * u + ι d := by
    let a : Fin 2 → MvPolynomial (Fin 3) K := ![X k, X j]
    have ha (i) : (a i).totalDegree ≤ 1 := by fin_cases i <;> simp [a]
    have hi : Function.Injective (projectionCoordinateMap p (fun i : Fin 1 => a i.succ)) :=
      injective_projectionCoordinateMap_iff.mpr
        ((algebraicIndependent_singleton_iff (i := (0 : Fin 1))).mpr hj)
    obtain ⟨f, hf, hfd, hker⟩ := exists_hypersurface_projection_equation_degree_le (n := 0) p a ha 1
      (hdegree.dimension_degree one_pos) (fun i : Fin 1 => X i.succ) (by simp)
      (by simpa using injective_projectionCoordinateMap_iff.mp hi)
    let α := f.coeff (Finsupp.single 1 1)
    let β := f.coeff (Finsupp.single 0 1)
    let γ := f.coeff 0
    have he : f = C γ + (C β * X 0 + C α * X 1) := by
      simpa only [linearForm, Fin.sum_univ_two] using eq_affine_of_totalDegree_le_one (σ := Fin 2) f hfd
    have hβ : β ≠ 0 := by
      intro hz
      have hder := projection_head_derivative_proper p a hi f hf.ne_zero hker
      rw [he] at hder
      apply hder
      simp [hz, pderiv_X]
    have hrel := (projectionCoordinateMap_eq_zero_iff hker).mpr (dvd_refl f)
    rw [he] at hrel
    simp only [projectionCoordinateMap, AlgHom.comp_apply, map_add, map_mul, aeval_C, aeval_X, a,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hrel
    change ι γ + (ι β * (Ideal.Quotient.mk p) (X k) + ι α * u) = 0 at hrel
    refine ⟨-(α / β), -(γ / β), ?_⟩
    apply mul_left_cancel₀ ((map_ne_zero_iff ι (FaithfulSMul.algebraMap_injective K A)).mpr hβ)
    have hc (t : K) : β * -(t / β) = -t := by field_simp
    simp only [mul_add, ← mul_assoc]
    rw [← map_mul ι, ← map_mul ι, hc, hc, map_neg, map_neg]
    linear_combination hrel
  choose c d hcd using hex
  have hcj : c j ≠ 0 := by
    intro hc
    have he := hcd j
    rw [hc, map_zero, zero_mul, zero_add] at he
    apply hj
    rw [he]
    exact isAlgebraic_algebraMap (d j)
  exact ⟨j, c, d, hcj, hj, fun k => (hcd k).trans (congrArg (· + ι (d k)) (Algebra.smul_def (c k) u).symm)⟩

/-- A degree-one prime component is a line.
Over `ℚ` the vanishing ideal of this line is the original prime. -/
theorem degree_one_zeroLocus_eq_rationalAffineLine
    (p : Ideal (CoordinatePolynomial 3)) [p.IsPrime] (hdegree : HasAffineCurveDegree p 1) :
    (∃ a v : RatPoint 3, v ≠ 0 ∧ idealZeroLocus p = rationalAffineLine a v) ∧
    ∀ f, idealZeroLocus p ⊆ zeroLocus f → f ∈ p := by
  obtain ⟨j, c, d, hc, hj, hcd⟩ := degree_one_coordinates_affine p hdegree
  let x := Ideal.Quotient.mk p (X j)
  let φ : CoordinatePolynomial 3 →ₐ[ℚ] Polynomial ℚ :=
    aeval (fun k => Polynomial.C (d k) + Polynomial.C (c k) * Polynomial.X)
  have hφ : (Polynomial.aeval x).comp φ = Ideal.Quotient.mkₐ ℚ p := by
    ext k
    simp [φ, x, Ideal.Quotient.mkₐ_eq_mk, hcd k, add_comm]
    exact (Algebra.smul_def (R := ℚ) (A := CoordinatePolynomial 3 ⧸ p) _ _).symm
  have hker (f) : φ f = 0 ↔ f ∈ p := by
    rw [← (transcendental_iff_injective.mp hj).eq_iff, map_zero]
    change ((Polynomial.aeval x).comp φ) f = 0 ↔ _
    rw [hφ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  have heval (t : ℚ) (f : CoordinatePolynomial 3) :
      (φ f).eval t = eval (d + t • c) f := by
    have he : (Polynomial.aeval t).comp φ = aeval (d + t • c) := by
      ext k
      simp [φ, smul_eq_mul]
      exact mul_comm _ _
    simpa [MvPolynomial.aeval_eq_eval, Polynomial.aeval_def] using DFunLike.congr_fun he f
  have hline : idealZeroLocus p = rationalAffineLine d c := by
    ext y
    constructor
    · intro hy
      refine ⟨y j, funext fun k => ?_⟩
      have he := congrArg (coordinatePoint p y hy) (hcd k)
      simpa [coordinatePoint_mk, mul_comm, add_comm] using he
    · rintro ⟨t, rfl⟩ f hf
      rw [← heval, (hker f).mpr hf, Polynomial.eval_zero]
  refine ⟨⟨d, c, fun h => hc (congrFun h j), hline⟩, fun f hf => (hker f).mp ?_⟩
  apply Polynomial.zero_of_eval_zero
  intro t
  exact (heval t f).trans (hf (hline ▸ ⟨t, rfl⟩))

end
end CCDN
