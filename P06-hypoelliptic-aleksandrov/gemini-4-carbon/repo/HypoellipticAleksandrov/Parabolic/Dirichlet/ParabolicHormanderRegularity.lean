module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyExistence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialWeakDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.TimeWeakDerivative
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.SpatialWeakDerivatives
import HypoellipticAleksandrov.KineticAleksandrov.HormanderBridge
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSqrt
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSpan
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped BigOperators Convolution ENNReal Matrix MatrixOrder Pointwise Topology

private def tvCLE (d : ℕ) : PDE.Vec (d + 1) ≃L[ℝ] TimeVelocity d :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x 0, fun i => x i.succ)
      invFun := fun z => Fin.cons z.1 z.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := Fin.cons_self_tail
      right_inv := fun _ => Prod.ext rfl (funext fun _ => rfl) }

@[simp] private theorem tvCLE_apply {d : ℕ} (x : PDE.Vec (d + 1)) :
    tvCLE d x = (x 0, fun i => x i.succ) := rfl

@[simp] private theorem tvCLE_symm_apply {d : ℕ} (z : TimeVelocity d) :
    (tvCLE d).symm z = Fin.cons z.1 z.2 := rfl



section Fields

open scoped Matrix.Norms.L2Operator

private def parabolicSqrt {d : ℕ} (B : CoefficientField d) (x : PDE.Vec (d + 1)) : PDE.Mat d :=
  CFC.sqrt (B (x 0) (fun j => x j.succ))

private theorem contDiff_parabolicSqrt {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {B : CoefficientField d} (hB : IsSmoothCoefficient B)
    (hlo : HasLowerEllipticity lam B) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PDE.Vec (d + 1) => parabolicSqrt B x i j) :=
  contDiff_sqrt_entry (fun x : PDE.Vec (d + 1) => B (x 0) (fun k => x k.succ))
    (fun r s => ((contDiff_apply_apply ℝ ℝ r s).comp hB).comp (tvCLE d).contDiff)
    (fun x => posDef_of_smul_one_le hlam (hlo (x 0) _)) i j

private theorem sum_parabolicSqrt_mul {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {B : CoefficientField d} (hlo : HasLowerEllipticity lam B)
    (x : PDE.Vec (d + 1)) (i j : Fin d) :
    ∑ k : Fin d, parabolicSqrt B x k i * parabolicSqrt B x k j =
      B (x 0) (fun r => x r.succ) i j := by
  set M := B (x 0) (fun r => x r.succ)
  have hsq := congrFun (congrFun (CFC.sqrt_mul_sqrt_self M
    (posDef_of_smul_one_le hlam (hlo _ _)).posSemidef.nonneg) i) j
  have hsymm := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  rw [Matrix.mul_apply] at hsq
  rw [← hsq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : CFC.sqrt M k i = CFC.sqrt M i k := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hsymm i) k
  change CFC.sqrt M k i * CFC.sqrt M k j = _; rw [hs]

private def parabolicDiffField {d : ℕ} (B : CoefficientField d) (k : Fin d)
    (x : PDE.Vec (d + 1)) : PDE.Vec (d + 1) :=
  Fin.cons 0 (fun j => parabolicSqrt B x k j)

private def parabolicDriftCorr {d : ℕ} (B : CoefficientField d) (i : Fin d)
    (x : PDE.Vec (d + 1)) : ℝ :=
  ∑ k : Fin d, ∑ j : Fin d,
    parabolicSqrt B x k j * fderiv ℝ (fun y => parabolicSqrt B y k i) x (PDE.basisVec j.succ)

private def parabolicDriftField {d : ℕ} (B : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (x : PDE.Vec (d + 1)) : PDE.Vec (d + 1) :=
  Fin.cons (-1) (fun i => b (x 0) (fun r => x r.succ) i - parabolicDriftCorr B i x)

private def parabolicFields {d : ℕ} (B : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) : Fin (d + 1) → PDE.Vec (d + 1) → PDE.Vec (d + 1) :=
  Fin.cons (parabolicDriftField B b) (parabolicDiffField B)

private theorem contDiff_parabolicFields {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {B : CoefficientField d} (hB : IsSmoothCoefficient B) (hlo : HasLowerEllipticity lam B)
    {b : ℝ → PDE.Vec d → PDE.Vec d}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2)) (m : Fin (d + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (parabolicFields B b m) := by
  have hβ := contDiff_parabolicSqrt hlam hB hlo
  refine Fin.cases ?_ (fun k => ?_) m
  · refine contDiff_pi.mpr fun r => Fin.cases contDiff_const (fun i => ?_) r
    exact (((contDiff_apply ℝ ℝ i).comp hb).comp (tvCLE d).contDiff).sub
      (ContDiff.sum fun k _ => ContDiff.sum fun j _ =>
        (hβ k j).mul (((hβ k i).fderiv_right (by simp)).clm_apply contDiff_const))
  · exact contDiff_pi.mpr fun r => Fin.cases contDiff_const (fun j => hβ k j) r

private theorem lieAlgebraSpansOn_parabolicFields {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {B : CoefficientField d} (hlo : HasLowerEllipticity lam B)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (S : Set (PDE.Vec (d + 1))) :
    LieAlgebraSpansOn S (parabolicFields B b) := by
  intro x _; rw [eq_top_iff]; intro v _
  set W := Submodule.span ℝ
    (Set.range (fun w : LieWord d => LieWord.eval (parabolicFields B b) w x))
  have hgen (m : Fin (d + 1)) : parabolicFields B b m x ∈ W :=
    Submodule.subset_span ⟨LieWord.generator m, rfl⟩
  have hspatial (u : PDE.Vec d) : Fin.cons 0 u ∈ W := by
    obtain ⟨a, ha⟩ := exists_row_combination
      (posDef_sqrt (posDef_of_smul_one_le hlam (hlo (x 0) _))) u
    have heq : Fin.cons (0 : ℝ) u = ∑ k : Fin d, a k • parabolicFields B b k.succ x := by
      funext r; refine Fin.cases ?_ (fun j => ?_) r
      · simp [parabolicFields, parabolicDiffField, Finset.sum_apply]
      · simp
        exact (ha j).symm
    exact heq ▸ W.sum_mem fun k _ => W.smul_mem _ (hgen k.succ)
  have ht : Fin.cons (1 : ℝ) 0 ∈ W := by
    have heq : Fin.cons (1 : ℝ) (0 : PDE.Vec d) =
        Fin.cons 0 (fun i => b (x 0) (fun r => x r.succ) i - parabolicDriftCorr B i x) -
          parabolicFields B b 0 x := by
      funext r; refine Fin.cases ?_ (fun _ => ?_) r <;> simp [parabolicFields, parabolicDriftField]
    exact heq ▸ W.sub_mem (hspatial _) (hgen 0)
  have hv : v = v 0 • Fin.cons (1 : ℝ) 0 + Fin.cons 0 (fun i => v i.succ) := by
    funext r; refine Fin.cases ?_ (fun _ => ?_) r <;> simp
  exact hv ▸ W.add_mem (W.smul_mem _ ht) (hspatial _)


private theorem hormanderAdjointTest_parabolicFields {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {B : CoefficientField d} (hB : IsSmoothCoefficient B) (hlo : HasLowerEllipticity lam B)
    {b : ℝ → PDE.Vec d → PDE.Vec d}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    {ψ : PDE.Vec (d + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : PDE.Vec (d + 1)) :
    hormanderAdjointTest (parabolicFields B b) (fun _ => 0) ψ x =
      timeDerivative (ψ ∘ (tvCLE d).symm) (tvCLE d x) +
        (∑ i : Fin d, ∑ j : Fin d,
          velocityGradient (fun z =>
            velocityGradient (fun w => B w.1 w.2 j i * ψ ((tvCLE d).symm w)) z j)
            (tvCLE d x) i) -
        ∑ i : Fin d,
          velocityGradient (fun z => b z.1 z.2 i * ψ ((tvCLE d).symm z)) (tvCLE d x) i  := by
  have euclideanDivergence_finCons {s : PDE.Vec (d + 1) → ℝ} {g : PDE.Vec (d + 1) → PDE.Vec d} {x : PDE.Vec (d + 1)} (hs : DifferentiableAt ℝ s x) (hg : ∀ i, DifferentiableAt ℝ (fun y => g y i) x) :
      euclideanDivergence (fun y => Fin.cons (s y) (g y)) x =
      fderiv ℝ s x (PDE.basisVec 0) +
        ∑ i : Fin d, fderiv ℝ (fun y => g y i) x (PDE.basisVec i.succ) := by
    have hcomp : ∀ r : Fin (d + 1),
        DifferentiableAt ℝ (fun y => (Fin.cons (s y) (g y) : PDE.Vec (d + 1)) r) x :=
      Fin.cases hs hg
    have key (r : Fin (d + 1)) (w : PDE.Vec (d + 1)) :
        fderiv ℝ (fun y => (Fin.cons (s y) (g y) : PDE.Vec (d + 1))) x w r =
          fderiv ℝ (fun y => (Fin.cons (s y) (g y) : PDE.Vec (d + 1)) r) x w := by
      change (fderiv ℝ (fun y r => (Fin.cons (s y) (g y) : PDE.Vec (d + 1)) r) x w) r = _
      rw [fderiv_pi hcomp]; rfl
    unfold euclideanDivergence
    simp [Fin.sum_univ_succ, key]
  have hβ := contDiff_parabolicSqrt hlam hB hlo
  have hdψ := hψ.differentiable (by simp)
  have hdβ (k i : Fin d) := (hβ k i).differentiable (by simp)
  have hcorr (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (parabolicDriftCorr B i) :=
    ContDiff.sum fun k _ => ContDiff.sum fun j _ =>
      (hβ k j).mul (((hβ k i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)
  have hbi (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec (d + 1) => b (y 0) (fun r => y r.succ) i) :=
    ((contDiff_apply ℝ ℝ i).comp hb).comp (tvCLE d).contDiff
  have hdir0 {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : PDE.Vec (d + 1)) :
      fderiv ℝ (f ∘ tvCLE d) y (PDE.basisVec 0) = timeDerivative f (tvCLE d y) := by
    have hb0 : (tvCLE d : PDE.Vec (d + 1) →L[ℝ] TimeVelocity d) (PDE.basisVec 0) = (1, 0) :=
      Prod.ext (by simp [PDE.basisVec]) (funext fun _ => by simp [PDE.basisVec, Fin.succ_ne_zero])
    rw [((hf.differentiable (by simp) (tvCLE d y)).hasFDerivAt.comp y (tvCLE d).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply, hb0]
    rfl
  have hdiri {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (i : Fin d) (y : PDE.Vec (d + 1)) :
      fderiv ℝ (f ∘ tvCLE d) y (PDE.basisVec i.succ) = velocityGradient f (tvCLE d y) i := by
    have hbi' : (tvCLE d : PDE.Vec (d + 1) →L[ℝ] TimeVelocity d) (PDE.basisVec i.succ) =
        (0, Pi.single i 1) :=
      Prod.ext (by simp [PDE.basisVec, (Fin.succ_ne_zero i).symm])
        (funext fun j => by by_cases hj : j = i <;> simp [PDE.basisVec, Pi.single_apply, hj])
    rw [((hf.differentiable (by simp) (tvCLE d y)).hasFDerivAt.comp y (tvCLE d).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply, hbi']
    rfl
  have hdiv0 : euclideanDivergence (fun y => ψ y • parabolicFields B b 0 y) x =
      -fderiv ℝ ψ x (PDE.basisVec 0) +
        (∑ i : Fin d, fderiv ℝ (fun y => ψ y * b (y 0) (fun r => y r.succ) i) x (PDE.basisVec i.succ)) -
        ∑ i : Fin d, fderiv ℝ (fun y => ψ y * parabolicDriftCorr B i y) x (PDE.basisVec i.succ) := by
    have hfun : (fun y => ψ y • parabolicFields B b 0 y) =
        fun y => Fin.cons (-ψ y)
          (fun i => ψ y * b (y 0) (fun r => y r.succ) i - ψ y * parabolicDriftCorr B i y) := by
      funext y r; refine Fin.cases ?_ (fun _ => ?_) r <;>
        simp [parabolicFields, parabolicDriftField, mul_sub]
    rw [hfun, euclideanDivergence_finCons (hdψ x).fun_neg fun i =>
      ((hdψ x).fun_mul ((hbi i).differentiable (by simp) x)).fun_sub
        ((hdψ x).fun_mul ((hcorr i).differentiable (by simp) x))]
    have hneg_fd : fderiv ℝ (fun y => -ψ y) x (PDE.basisVec 0) = -fderiv ℝ ψ x (PDE.basisVec 0) := by
      change fderiv ℝ (-ψ) x (PDE.basisVec 0) = _; rw [fderiv_neg]; rfl
    have hsum_sub :
        (∑ i : Fin d, fderiv ℝ (fun y =>
          ψ y * b (y 0) (fun r => y r.succ) i - ψ y * parabolicDriftCorr B i y) x
          (PDE.basisVec i.succ)) =
        (∑ i : Fin d, fderiv ℝ (fun y => ψ y * b (y 0) (fun r => y r.succ) i) x
          (PDE.basisVec i.succ)) -
        ∑ i : Fin d, fderiv ℝ (fun y => ψ y * parabolicDriftCorr B i y) x
          (PDE.basisVec i.succ) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [fderiv_fun_sub ((hdψ x).fun_mul ((hbi i).differentiable (by simp) x))
        ((hdψ x).fun_mul ((hcorr i).differentiable (by simp) x)), sub_apply]
    rw [hneg_fd, hsum_sub]; ring
  have hdiv_inner (k : Fin d) (y : PDE.Vec (d + 1)) :
      euclideanDivergence (fun q => ψ q • parabolicFields B b k.succ q) y =
        ∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ) := by
    have hfun : (fun q => ψ q • parabolicFields B b k.succ q) =
        fun q => Fin.cons 0 (fun j => ψ q * parabolicSqrt B q k j) := by
      funext q r; refine Fin.cases ?_ (fun _ => ?_) r <;> simp [parabolicFields, parabolicDiffField]
    rw [hfun, euclideanDivergence_finCons (differentiableAt_const (0 : ℝ))
      fun j => (hdψ y).fun_mul (hdβ k j y)]
    simp
  have hdiv_outer :
      (∑ k : Fin d, euclideanDivergence (fun y =>
        euclideanDivergence (fun q => ψ q • parabolicFields B b k.succ q) y •
          parabolicFields B b k.succ y) x) =
      (∑ i : Fin d, ∑ j : Fin d,
        fderiv ℝ (fun y => fderiv ℝ (fun q =>
          B (q 0) (fun r => q r.succ) j i * ψ q) y (PDE.basisVec j.succ)) x (PDE.basisVec i.succ)) -
      ∑ i : Fin d, fderiv ℝ (fun y => ψ y * parabolicDriftCorr B i y) x (PDE.basisVec i.succ) := by
    have h_each (k : Fin d) :
        euclideanDivergence (fun y =>
          euclideanDivergence (fun q => ψ q • parabolicFields B b k.succ q) y •
            parabolicFields B b k.succ y) x =
        ∑ i : Fin d, fderiv ℝ (fun y =>
          (∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ)) *
            parabolicSqrt B y k i) x (PDE.basisVec i.succ) := by
      simp_rw [hdiv_inner k]
      have h_in : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
          ∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ)) :=
        ContDiff.sum fun j _ =>
          ((hψ.mul (hβ k j)).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
      have hfun : (fun y => (∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y
            (PDE.basisVec j.succ)) • parabolicFields B b k.succ y) =
          fun y => Fin.cons 0 (fun i =>
            (∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y
              (PDE.basisVec j.succ)) * parabolicSqrt B y k i) := by
        funext y r; refine Fin.cases ?_ (fun _ => ?_) r <;> simp [parabolicFields, parabolicDiffField]
      rw [hfun, euclideanDivergence_finCons (differentiableAt_const (0 : ℝ))
        fun i => (h_in.differentiable (by simp) x).fun_mul (hdβ k i x)]
      simp
    simp_rw [h_each]; rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm_diff (k : Fin d) : DifferentiableAt ℝ (fun y =>
        (∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ)) *
          parabolicSqrt B y k i) x :=
      ((ContDiff.sum fun j _ => ((hψ.mul (hβ k j)).fderiv_right (m := (⊤ : ℕ∞))
        (by simp)).clm_apply contDiff_const).differentiable (by simp) x).fun_mul (hdβ k i x)
    rw [← sum_apply, ← fderiv_fun_sum (u := Finset.univ) (fun k _ => hterm_diff k)]
    have hfun_eq : (fun y => ∑ k : Fin d,
        (∑ j : Fin d, fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ)) *
          parabolicSqrt B y k i) =
        (fun y => ∑ j : Fin d, fderiv ℝ (fun q =>
          B (q 0) (fun r => q r.succ) j i * ψ q) y (PDE.basisVec j.succ)) -
        fun y => ψ y * parabolicDriftCorr B i y := by
      funext y; simp [Finset.sum_mul, parabolicDriftCorr]
      have hprod (k j : Fin d) :
          fderiv ℝ (fun q => ψ q * parabolicSqrt B q k j) y (PDE.basisVec j.succ) *
            parabolicSqrt B y k i =
          fderiv ℝ (fun q => (ψ q * parabolicSqrt B q k j) * parabolicSqrt B q k i) y
            (PDE.basisVec j.succ) -
          ψ y * (parabolicSqrt B y k j *
            fderiv ℝ (fun q => parabolicSqrt B q k i) y (PDE.basisVec j.succ)) := by
        change _ = fderiv ℝ ((fun q => ψ q * parabolicSqrt B q k j) *
          (fun q => parabolicSqrt B q k i)) y (PDE.basisVec j.succ) - _
        rw [fderiv_mul ((hdψ y).fun_mul (hdβ k j y)) (hdβ k i y),
          add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]; ring
      simp_rw [hprod, Finset.sum_sub_distrib, ← Finset.mul_sum]; congr 1
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
      have hfn_j : (fun q => ∑ k : Fin d, ψ q * parabolicSqrt B q k j * parabolicSqrt B q k i) =
          fun q => B (q 0) (fun r => q r.succ) j i * ψ q := by
        funext q; rw [← sum_parabolicSqrt_mul hlam hlo q j i, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [← sum_apply, ← fderiv_fun_sum (u := Finset.univ)
        (fun k _ => (((hdψ y).fun_mul (hdβ k j y)).fun_mul (hdβ k i y))), hfn_j]
    rw [hfun_eq]
    have hd_each (j : Fin d) : DifferentiableAt ℝ (fun y => fderiv ℝ (fun q =>
        B (q 0) (fun r => q r.succ) j i * ψ q) y (PDE.basisVec j.succ)) x := by
      have hBji :=
        ((contDiff_apply_apply ℝ ℝ j i).comp hB).comp (tvCLE d).contDiff
      exact (((hBji.mul hψ).fderiv_right (m := (⊤ : ℕ∞))
        (by simp)).clm_apply contDiff_const).differentiable (by simp) x
    change fderiv ℝ ((fun y => ∑ j, fderiv ℝ (fun q => B (q 0) (fun r => q r.succ) j i * ψ q) y
        (PDE.basisVec j.succ)) - fun y => ψ y * parabolicDriftCorr B i y) x
        (PDE.basisVec i.succ) = _
    rw [fderiv_sub (f := fun y => ∑ j, fderiv ℝ (fun q => B (q 0) (fun r => q r.succ) j i * ψ q) y
        (PDE.basisVec j.succ)) (g := fun y => ψ y * parabolicDriftCorr B i y)
        (DifferentiableAt.fun_sum fun j _ => hd_each j)
        ((hdψ x).fun_mul ((hcorr i).differentiable (by simp) x)),
      sub_apply, fderiv_fun_sum (u := Finset.univ) (fun j _ => hd_each j), sum_apply]
  unfold hormanderAdjointTest
  rw [hdiv0, hdiv_outer]
  have hψ_tv : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ (tvCLE d).symm) := hψ.comp (tvCLE d).symm.contDiff
  have h0_eq : fderiv ℝ ψ x (PDE.basisVec 0) = timeDerivative (ψ ∘ (tvCLE d).symm) (tvCLE d x) := by
    simpa only [show (ψ ∘ (tvCLE d).symm) ∘ tvCLE d = ψ from
      funext fun y => congrArg ψ (Fin.cons_self_tail y)] using hdir0 hψ_tv x
  have hb_eq (i : Fin d) :
      fderiv ℝ (fun y => ψ y * b (y 0) (fun r => y r.succ) i) x (PDE.basisVec i.succ) =
        velocityGradient (fun z => b z.1 z.2 i * ψ ((tvCLE d).symm z)) (tvCLE d x) i := by
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 i * ψ ((tvCLE d).symm z)) :=
      ((contDiff_apply ℝ ℝ i).comp hb).mul hψ_tv
    have hcomp : (fun z : TimeVelocity d => b z.1 z.2 i * ψ ((tvCLE d).symm z)) ∘ tvCLE d =
        fun y => ψ y * b (y 0) (fun r => y r.succ) i := by
      funext y; simp
      rw [show (Fin.cons (y 0) fun r => y r.succ) = y from Fin.cons_self_tail y, mul_comm]
    simpa only [hcomp] using hdiri hf i x
  have hA_eq (i j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ (fun q =>
        B (q 0) (fun r => q r.succ) j i * ψ q) y (PDE.basisVec j.succ)) x (PDE.basisVec i.succ) =
      velocityGradient (fun z =>
        velocityGradient (fun w => B w.1 w.2 j i * ψ ((tvCLE d).symm w)) z j) (tvCLE d x) i := by
    have hBji : ContDiff ℝ (⊤ : ℕ∞) (fun w : TimeVelocity d =>
        B w.1 w.2 j i * ψ ((tvCLE d).symm w)) :=
      ((contDiff_apply_apply ℝ ℝ j i).comp hB).mul hψ_tv
    have hinner (y) : fderiv ℝ (fun q => B (q 0) (fun r => q r.succ) j i * ψ q) y
        (PDE.basisVec j.succ) =
        velocityGradient (fun w => B w.1 w.2 j i * ψ ((tvCLE d).symm w)) (tvCLE d y) j := by
      have hcomp : (fun w : TimeVelocity d => B w.1 w.2 j i * ψ ((tvCLE d).symm w)) ∘ tvCLE d =
          fun q => B (q 0) (fun r => q r.succ) j i * ψ q := by
        funext q; simp only [Function.comp_apply, tvCLE_apply, tvCLE_symm_apply]
        rw [show (Fin.cons (q 0) fun r => q r.succ) = q from Fin.cons_self_tail q]
      simpa only [hcomp] using hdiri hBji j y
    simp_rw [hinner]
    have houter : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
        velocityGradient (fun w => B w.1 w.2 j i * ψ ((tvCLE d).symm w)) z j) :=
      (hBji.fderiv_right (by simp)).clm_apply contDiff_const
    exact hdiri houter i x
  simp_rw [h0_eq, hb_eq, hA_eq, zero_mul, add_zero]; ring

end Fields

section Main

open scoped Matrix.Norms.Elementwise

theorem exists_classicalInterior_of_variational_hormander
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hA : IsSmoothCoefficient A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
      (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g),
      IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
        b (fun _ _ => 0) (fun t y => F (t, y))
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu ∧
      ∃ w : TimeVelocity d → ℝ,
        MemLp w 2 (timeVelocityVolumeOn (Ioo a T ×ˢ Ω)) ∧
        (∀ᵐ t ∂volume.restrict (Ioo a T),
          (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) ∧
        IsScalarC12On w (scalarParabolicOpenCylinder a T Ω) ∧
        ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
          scalarTimeDerivative w z +
            matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) +
            PDE.vecDot (b z.1 z.2) (scalarSpatialGradient w z) = F z   := by
  have measurableEmbedding_tvCLE : MeasurableEmbedding (tvCLE d) :=
    (tvCLE d).toHomeomorph.measurableEmbedding
  have measurePreserving_tvCLE : MeasurePreserving (tvCLE d) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  classical
  have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) := ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  have hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) := ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
  have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  obtain ⟨u, g, hdu, hu⟩ := exists_reverseTime_variational_energy_solution a T lam Lam
    haT hlam hLam hΩ hΩb A b (fun _ _ => 0) (fun t y => F (t, y))
    hAs hbs hcs hFs (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2) (fun _ _ => le_rfl) 0
  let T₀ : ℝ := T - a
  let QR : Set (TimeVelocity d) := reverseTimeOpenInterval T₀ ×ˢ Ω
  have hQR_open : IsOpen QR := isOpen_Ioo.prod hΩ
  let μR := timeVelocityVolumeOn QR
  let : IsFiniteMeasure μR := ⟨by
    rw [show μR = timeVelocityVolumeOn QR from rfl, timeVelocityVolumeOn, Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono ?_)
      (isCompact_scalarParabolicClosedCylinder 0 T₀ hΩb).measure_lt_top
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩; exact ⟨⟨hτ.1.le, hτ.2.le⟩, subset_closure hy⟩⟩
  obtain ⟨U, hU, hUslice⟩ := exists_reverseTimeL2V_value_product_representative hΩ T₀ u
  obtain ⟨G, hG, hGslice⟩ := exists_reverseTimeL2V_gradient_coord_product_representatives hΩ T₀ u
  have hGweak := reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
    hΩ T₀ u U hU hUslice G hG hGslice
  have hU_L1 : Integrable U μR := hU.integrable one_le_two
  have hG_L1 (j : Fin d) : Integrable (G j) μR := (hG j).integrable one_le_two
  let AR : CoefficientField d := reverseTimeCoefficient T A
  let bR : ℝ → PDE.Vec d → PDE.Vec d := reverseTimeVectorCoefficient T b
  let dR : ℝ → PDE.Vec d → PDE.Vec d := reverseTimeDivergenceDrift T A b
  let FR : TimeVelocity d → ℝ := fun z => F (T - z.1, z.2)
  have hrev_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => (T - z.1, z.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hAR_smooth : IsSmoothCoefficient AR := hA.comp hrev_smooth
  have hbR_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => bR z.1 z.2) := hb.comp hrev_smooth
  have hFR_smooth : ContDiff ℝ (⊤ : ℕ∞) FR := hF.comp hrev_smooth
  have hAR_lo : HasLowerEllipticity lam AR := fun τ y => hlo (T - τ) y
  have hdR_smooth (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => dR z.1 z.2 j) := by
    refine (ContDiff.sum fun i _ => ?_).sub ((contDiff_apply ℝ ℝ j).comp hbR_smooth)
    have hAij : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => AR z.1 z.2 i j) :=
      (contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth
    have heq : (fun z : TimeVelocity d =>
        (fderiv ℝ (fun y : PDE.Vec d => AR z.1 y i j) z.2) (PDE.basisVec i)) =
        fun z => velocityGradient (fun w => AR w.1 w.2 i j) z i := by
      funext z
      have hf := (hAij.differentiable (by simp) (z.1, z.2)).hasFDerivAt.comp z.2
        (hasFDerivAt_prodMk_right z.1 z.2)
      change (fderiv ℝ ((fun w : TimeVelocity d => AR w.1 w.2 i j) ∘ Prod.mk z.1) z.2)
        (PDE.basisVec i) = _
      rw [hf.fderiv]; rfl
    rw [heq]; exact (hAij.fderiv_right (by simp)).clm_apply contDiff_const
  have hraw_any (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφsub : tsupport φ ⊆ QR) :
      (∫ z, (U z * timeDerivative φ z -
        (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z * velocityGradient φ z i) -
        (∑ j : Fin d, dR z.1 z.2 j * G j z * φ z) - FR z * φ z) ∂μR) = 0 := by
    obtain ⟨δ, hδ, hthick⟩ := hφc.isCompact.exists_cthickening_subset_open hQR_open hφsub
    let r_n : ℕ → ℝ := fun n => δ / (2 * ((n : ℝ) + 1))
    have hr_pos (n : ℕ) : 0 < r_n n := by dsimp [r_n]; positivity
    have hr_le (n : ℕ) : r_n n ≤ δ / 2 := by
      dsimp [r_n]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hδ, Nat.cast_nonneg (α := ℝ) n]
    have hr_lim : Tendsto r_n atTop (nhds 0) :=
      ((tendsto_const_nhds (x := δ / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat).congr'
        (Eventually.of_forall fun n => by dsimp [r_n]; field_simp) |>.trans (by simp)
    let bump (n : ℕ) : ContDiffBump (0 : ℝ) := ⟨r_n n / 2, r_n n, by positivity, half_lt_self (hr_pos n)⟩
    let ρ (n : ℕ) : ℝ → ℝ := (bump n).normed (volume : Measure ℝ)
    have hρ_cd (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ρ n) := (bump n).contDiff_normed (n := ⊤)
    have hρ_supp (n : ℕ) : Function.support (ρ n) = Metric.ball (0 : ℝ) (r_n n) :=
      (bump n).support_normed_eq (μ := (volume : Measure ℝ))
    let ψ (s : ℝ) : PDE.WeakTestFunction Ω :=
      { toFun := fun y => φ (s, y)
        contDiff := hφ.comp (contDiff_const.prodMk contDiff_id)
        hasCompactSupport := HasCompactSupport.of_support_subset_isCompact
          (hφc.isCompact.image continuous_snd) fun y hy => ⟨(s, y), subset_tsupport φ hy, rfl⟩
        tsupport_subset := fun y hy =>
          (hφsub (closure_minimal (s := Function.support fun x => φ (s, x))
            (fun _ hx => subset_tsupport φ hx)
            ((isClosed_tsupport φ).preimage (continuous_const.prodMk continuous_id)) hy)).2 }
    have hψ_grad (s : ℝ) (y : PDE.Vec d) (i : Fin d) :
        (ψ s).partialDeriv i y = velocityGradient φ (s, y) i := by
      have hf := (hφ.differentiable (by simp) (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
      change fderiv ℝ (φ ∘ Prod.mk s) y (PDE.basisVec i) = fderiv ℝ φ (s, y) (0, Pi.single i 1)
      rw [hf.fderiv]; rfl
    let act (s : ℝ) : Prop := ∃ y₀, (s, y₀) ∈ tsupport φ
    have hsupp_ρ (n : ℕ) (s : ℝ) : Function.support (fun r => ρ n (r - s)) = Metric.ball s (r_n n) := by
      ext r; change ρ n (r - s) ≠ 0 ↔ r ∈ Metric.ball s (r_n n)
      rw [← Function.mem_support, hρ_supp n, Metric.mem_ball, dist_zero_right, Metric.mem_ball, dist_eq_norm]
    let η (n : ℕ) (s : ℝ) : ReverseTimeScalarTest T₀ :=
      { toFun := fun τ => if act s then ρ n (τ - s) else 0
        contDiff' := by split_ifs; exacts [(hρ_cd n).comp (contDiff_id.sub contDiff_const), contDiff_const]
        hasCompactSupport' := by
          split_ifs
          · exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall s (r_n n))
              ((hsupp_ρ n s).symm ▸ Metric.ball_subset_closedBall)
          · exact HasCompactSupport.intro isCompact_empty fun _ _ => rfl
        tsupport_subset' := by
          split_ifs with hs
          · obtain ⟨y₀, hy₀⟩ := hs
            intro τ hτ
            rw [tsupport, hsupp_ρ, closure_ball s (hr_pos n).ne'] at hτ
            have hd_le : dist ((τ, y₀) : TimeVelocity d) (s, y₀) ≤ δ := by
              rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
              exact (Metric.mem_closedBall.mp hτ).trans ((hr_le n).trans (by linarith))
            exact (hthick (Metric.mem_cthickening_of_dist_le _ _ δ _ hy₀ hd_le)).1
          · simp }
    have hη_mul (n : ℕ) (s τ : ℝ) (y : PDE.Vec d) :
        η n s τ * ψ s y = ρ n (τ - s) * φ (s, y) ∧
        (η n s).deriv τ * ψ s y = _root_.deriv (ρ n) (τ - s) * φ (s, y) ∧
        ∀ i, η n s τ * (ψ s).partialDeriv i y = ρ n (τ - s) * velocityGradient φ (s, y) i := by
      by_cases hs : act s
      · have hd : (η n s).deriv τ = _root_.deriv (ρ n) (τ - s) := by
          change _root_.deriv (fun r => if act s then ρ n (r - s) else 0) τ = _
          simpa [hs] using _root_.deriv_comp_sub_const (ρ n) s τ
        exact ⟨by simp [η, ψ, hs], by rw [hd], fun i => by simp [η, hs, hψ_grad]⟩
      · have hφ0 : φ (s, y) = 0 := image_eq_zero_of_notMem_tsupport fun hm => hs ⟨y, hm⟩
        have hg0 (i : Fin d) : velocityGradient φ (s, y) i = 0 := by
          simp [velocityGradient, (notMem_tsupport_iff_eventuallyEq.mp fun hm => hs ⟨y, hm⟩).fderiv_eq]
        have hd0 : (η n s).deriv τ = 0 := by
          change _root_.deriv (fun _ : ℝ => if act s then _ else (0 : ℝ)) τ = 0; simp [hs]
        exact ⟨by simp [η, ψ, hs, hφ0], by rw [hd0, hφ0, zero_mul, mul_zero],
          fun i => by simp [η, hs, hg0 i]⟩
    have hconv1D {Φ : TimeVelocity d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
        (∃ B : ℝ, 0 ≤ B ∧ ∀ n (z : TimeVelocity d), |∫ s : ℝ, ρ n (z.1 - s) * Φ (s, z.2)| ≤ B) ∧
        ∀ z : TimeVelocity d, Tendsto (fun n => ∫ s : ℝ, ρ n (z.1 - s) * Φ (s, z.2)) atTop (nhds (Φ z)) := by
      obtain ⟨M₀, hM₀⟩ := hΦc.exists_bound_of_continuous hΦ.continuous
      let B := max M₀ 0
      refine ⟨⟨B, le_max_right _ _, fun n z => ?_⟩, fun z => ?_⟩
      · have hiρ : Integrable (fun s : ℝ => ρ n (z.1 - s)) volume :=
          ((hρ_cd n).continuous.integrable_of_hasCompactSupport
            (bump n).hasCompactSupport_normed).comp_sub_left z.1
        refine abs_integral_le_integral_abs.trans ((integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (hiρ.mul_const B)
          (Eventually.of_forall fun s => ?_)).trans ?_)
        · dsimp only; rw [abs_mul, abs_of_nonneg ((bump n).nonneg_normed _)]
          exact mul_le_mul_of_nonneg_left
            ((Real.norm_eq_abs _ ▸ hM₀ (s, z.2)).trans (le_max_left _ _)) ((bump n).nonneg_normed _)
        · rw [integral_mul_const, integral_sub_left_eq_self (ρ n) volume z.1,
            (bump n).integral_normed, one_mul]
      · have heq (n) : (∫ s : ℝ, ρ n (z.1 - s) * Φ (s, z.2)) =
            ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun s => Φ (s, z.2))) z.1 := by
          rw [← convolution_flip]
          simp only [ρ, convolution_def, ContinuousLinearMap.flip_apply,
            ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        have hcont_y : Continuous (fun s : ℝ => Φ (s, z.2)) :=
          hΦ.continuous.comp (continuous_id.prodMk continuous_const)
        simpa only [heq] using ContDiffBump.convolution_tendsto_right_of_continuous hr_lim hcont_y z.1
    have h_s_int {Φ : TimeVelocity d → ℝ} (hΦ : Continuous Φ) (n : ℕ) (z : TimeVelocity d) :
        Integrable (fun s : ℝ => ρ n (z.1 - s) * Φ (s, z.2)) volume :=
      (((hρ_cd n).continuous.comp (continuous_const.sub continuous_id)).mul
        (hΦ.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z.1 (r_n n))
          fun s hs => by
            have hm : z.1 - s ∈ Metric.ball (0 : ℝ) (r_n n) :=
              (hρ_supp n) ▸ left_ne_zero_of_mul hs
            rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hm
            rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]; exact hm.le)
    have hibp1D (n : ℕ) (z : TimeVelocity d) :
        (∫ s : ℝ, _root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) =
          ∫ s : ℝ, ρ n (z.1 - s) * timeDerivative φ (s, z.2) := by
      let g : ℝ → ℝ := fun s => ρ n (z.1 - s) * φ (s, z.2)
      let R : ℝ := |z.1| + r_n n + 1
      have hρ_out {s : ℝ} (hs : r_n n ≤ |z.1 - s|) : ρ n (z.1 - s) = 0 := by
        by_contra hne
        have hm : z.1 - s ∈ Metric.ball (0 : ℝ) (r_n n) := (hρ_supp n) ▸ hne
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hm; linarith
      have hderiv_g (s : ℝ) : HasDerivAt g
          (-_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2) + ρ n (z.1 - s) * timeDerivative φ (s, z.2)) s :=
        ((((hρ_cd n).differentiable (by simp) (z.1 - s)).hasDerivAt.comp s
          ((hasDerivAt_const s z.1).sub (hasDerivAt_id s))).congr_deriv (by ring)).mul
          ((((hφ.differentiable (by simp) (s, z.2)).hasFDerivAt.comp s
            ((hasDerivAt_id s).prodMk (hasDerivAt_const s z.2)))).hasDerivAt.congr_deriv (by simp; rfl))
      have hi1 : Integrable (fun s => -_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) volume :=
        (((((hρ_cd n).continuous_deriv (by simp)).comp (continuous_const.sub continuous_id)).neg).mul
          (hφ.continuous.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact (hφc.isCompact.image continuous_fst)
            fun s hs => ⟨(s, z.2), subset_tsupport φ fun h0 => hs (by simp [h0]), rfl⟩)
      have hi2 := h_s_int (Φ := timeDerivative φ)
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) n z
      have heq_d : _root_.deriv g = fun s =>
          -_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2) + ρ n (z.1 - s) * timeDerivative φ (s, z.2) :=
        funext fun s => (hderiv_g s).deriv
      have h0 : (∫ s : ℝ, _root_.deriv g s) = 0 := by
        have hvan : ∀ s ∉ Ioc (-R) R, _root_.deriv g s = 0 := fun s hs => by
          have hfar : r_n n + 1 / 2 < |z.1 - s| := by
            rw [mem_Ioc, not_and_or] at hs
            rcases hs with h1 | h2
            · rw [abs_of_nonneg (by dsimp [R] at h1; linarith [neg_abs_le z.1, hr_pos n])]
              dsimp [R] at h1; linarith [neg_abs_le z.1]
            · rw [abs_sub_comm, abs_of_pos (by dsimp [R] at h2; linarith [le_abs_self z.1, hr_pos n])]
              dsimp [R] at h2; linarith [le_abs_self z.1]
          have hev : g =ᶠ[𝓝 s] 0 := by
            filter_upwards [(isOpen_lt continuous_const
              (continuous_const.sub continuous_id).abs).mem_nhds hfar] with r hr
            exact mul_eq_zero_of_left (hρ_out (by linarith [show r_n n + 1 / 2 < |z.1 - r| from hr])) _
          exact hev.deriv_eq.trans (deriv_const s 0)
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan,
          ← intervalIntegral.integral_of_le (by dsimp [R]; linarith [abs_nonneg z.1, hr_pos n]),
          intervalIntegral.integral_deriv_eq_sub (fun s _ => (hderiv_g s).differentiableAt)
            (heq_d ▸ (hi1.add hi2).intervalIntegrable)]
        have hgR : g R = 0 := mul_eq_zero_of_left (hρ_out (by
          rw [abs_sub_comm, abs_of_nonneg (by dsimp [R]; linarith [le_abs_self z.1, hr_pos n])]
          dsimp [R]; linarith [le_abs_self z.1])) _
        have hgmR : g (-R) = 0 := mul_eq_zero_of_left (hρ_out (by
          rw [abs_of_nonneg (by dsimp [R]; linarith [neg_abs_le z.1, hr_pos n])]
          dsimp [R]; linarith [neg_abs_le z.1])) _
        rw [hgR, hgmR, sub_self]
      rw [heq_d, integral_add hi1 hi2, show (fun s => -_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) =
        fun s => -(_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) by funext s; ring, integral_neg] at h0
      linarith
    have hK_comp := isCompact_scalarParabolicClosedCylinder 0 T₀ hΩb
    have hQR_sub : QR ⊆ scalarParabolicClosedCylinder 0 T₀ Ω :=
      fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
    have hbd_cont {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ QR, |f z| ≤ C := by
      obtain ⟨C₀, hC₀⟩ := hK_comp.exists_bound_of_continuousOn hf.continuous.continuousOn
      exact ⟨max C₀ 0, le_max_right _ _, fun z hz =>
        (Real.norm_eq_abs _ ▸ hC₀ z (hQR_sub hz)).trans (le_max_left _ _)⟩
    choose CA hCA0 hCA using fun i j => hbd_cont ((contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth)
    choose Cd hCd0 hCd using fun j => hbd_cont (hdR_smooth j)
    obtain ⟨CF, hCF0, hCF⟩ := hbd_cont hFR_smooth
    have hzero_n (n : ℕ) :
        (∫ z, (U z * (∫ s : ℝ, ρ n (z.1 - s) * timeDerivative φ (s, z.2)) -
          (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z *
            (∫ s : ℝ, ρ n (z.1 - s) * velocityGradient φ (s, z.2) i)) -
          (∑ j : Fin d, dR z.1 z.2 j * G j z * (∫ s : ℝ, ρ n (z.1 - s) * φ (s, z.2))) -
          FR z * (∫ s : ℝ, ρ n (z.1 - s) * φ (s, z.2))) ∂μR) = 0 := by
      let F_ker (s : ℝ) (z : TimeVelocity d) : ℝ :=
        U z * (η n s).deriv z.1 * ψ s z.2 -
          (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z * (ψ s).partialDeriv i z.2) * η n s z.1 -
          (∑ j : Fin d, dR z.1 z.2 j * G j z * ψ s z.2) * η n s z.1 -
          FR z * ψ s z.2 * η n s z.1
      have hF_eq (s : ℝ) (z : TimeVelocity d) :
          F_ker s z = U z * (_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) -
            (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z *
              (ρ n (z.1 - s) * velocityGradient φ (s, z.2) i)) -
            (∑ j : Fin d, dR z.1 z.2 j * G j z * (ρ n (z.1 - s) * φ (s, z.2))) -
            FR z * (ρ n (z.1 - s) * φ (s, z.2)) := by
        obtain ⟨h1, h2, h3⟩ := hη_mul n s z.1 z.2
        simp only [F_ker, mul_assoc, h2, Finset.sum_mul]
        congr 1; congr 1; congr 1
        · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun _ _ => by rw [← h3 i]; ring
        · exact Finset.sum_congr rfl fun _ _ => by rw [← h1]; ring
        · rw [← h1]; ring
      obtain ⟨Mρ, hMρ⟩ := (bump n).hasCompactSupport_normed.exists_bound_of_continuous (hρ_cd n).continuous
      obtain ⟨Mdρ, hMdρ⟩ := (bump n).hasCompactSupport_normed.deriv.exists_bound_of_continuous
        ((hρ_cd n).continuous_deriv (by simp))
      obtain ⟨Mφ, hMφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
      choose Mgφ hMgφ using fun i =>
        (hφc.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1)).exists_bound_of_continuous
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      let C_s : ℝ := max Mρ 0 + max Mdρ 0 + 1
      let C_φ : ℝ := max Mφ 0 + (∑ i : Fin d, max (Mgφ i) 0) + 1
      have hCs0 : 0 ≤ C_s := by dsimp [C_s]; linarith [le_max_right Mρ 0, le_max_right Mdρ 0]
      have hCφ0 : 0 ≤ C_φ := by
        have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => le_max_right (Mgφ i) 0
        dsimp [C_φ]; linarith [le_max_right Mφ 0]
      have hF_meas : AEStronglyMeasurable (Function.uncurry F_ker) (volume.prod μR) := by
        have hc1 : Continuous (fun p : ℝ × TimeVelocity d =>
            _root_.deriv (ρ n) (p.2.1 - p.1) * φ (p.1, p.2.2)) :=
          ((((hρ_cd n).continuous_deriv (by simp)).comp
            ((continuous_fst.comp continuous_snd).sub continuous_fst)).mul
            (hφ.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
        have hc2 (i : Fin d) : Continuous (fun p : ℝ × TimeVelocity d =>
            ρ n (p.2.1 - p.1) * velocityGradient φ (p.1, p.2.2) i) :=
          (((hρ_cd n).continuous.comp
            ((continuous_fst.comp continuous_snd).sub continuous_fst)).mul
            (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
              (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
        have hc3 : Continuous (fun p : ℝ × TimeVelocity d => ρ n (p.2.1 - p.1) * φ (p.1, p.2.2)) :=
          (((hρ_cd n).continuous.comp ((continuous_fst.comp continuous_snd).sub continuous_fst)).mul
            (hφ.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
        have heq_u : Function.uncurry F_ker = fun p =>
            U p.2 * (_root_.deriv (ρ n) (p.2.1 - p.1) * φ (p.1, p.2.2)) -
            (∑ i : Fin d, ∑ j : Fin d, AR p.2.1 p.2.2 i j * G j p.2 *
              (ρ n (p.2.1 - p.1) * velocityGradient φ (p.1, p.2.2) i)) -
            (∑ j : Fin d, dR p.2.1 p.2.2 j * G j p.2 * (ρ n (p.2.1 - p.1) * φ (p.1, p.2.2))) -
            FR p.2 * (ρ n (p.2.1 - p.1) * φ (p.1, p.2.2)) := funext fun ⟨s, z⟩ => hF_eq s z
        rw [heq_u]
        exact (((hU_L1.aestronglyMeasurable.comp_snd.mul hc1.aestronglyMeasurable).sub
          (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
            Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
              (((((contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth).continuous.comp
                continuous_snd).aestronglyMeasurable.mul (hG_L1 j).aestronglyMeasurable.comp_snd).mul
                (hc2 i).aestronglyMeasurable))).sub
          (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
            ((((hdR_smooth j).continuous.comp continuous_snd).aestronglyMeasurable.mul
              (hG_L1 j).aestronglyMeasurable.comp_snd).mul hc3.aestronglyMeasurable))).sub
          ((hFR_smooth.continuous.comp continuous_snd).aestronglyMeasurable.mul hc3.aestronglyMeasurable)
      let dom_z : TimeVelocity d → ℝ := fun z =>
        C_s * C_φ * (|U z| + (∑ i : Fin d, ∑ j : Fin d, CA i j * |G j z|) +
          (∑ j : Fin d, Cd j * |G j z|) + CF)
      have hdom_z_int : Integrable dom_z μR :=
        (((hU_L1.norm.add (integrable_finsetSum _ fun i _ =>
          integrable_finsetSum _ fun j _ => (hG_L1 j).norm.const_mul (CA i j))).add
          (integrable_finsetSum _ fun j _ => (hG_L1 j).norm.const_mul (Cd j))).add
          (integrable_const CF)).const_mul (C_s * C_φ)
      have hdom_s_int : Integrable ((Icc 0 T₀).indicator fun _ : ℝ => (1 : ℝ)) volume :=
        (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
      have hdom_prod_int : Integrable (fun p : ℝ × TimeVelocity d =>
          (Icc 0 T₀).indicator (fun _ : ℝ => (1 : ℝ)) p.1 * dom_z p.2) (volume.prod μR) := by
        refine (integrable_prod_iff (hdom_s_int.aestronglyMeasurable.comp_fst.mul
          hdom_z_int.aestronglyMeasurable.comp_snd)).mpr
          ⟨Eventually.of_forall fun s =>
            hdom_z_int.const_mul ((Icc 0 T₀).indicator (fun _ : ℝ => (1 : ℝ)) s), ?_⟩
        refine (hdom_s_int.mul_const (∫ z, dom_z z ∂μR)).congr (Eventually.of_forall fun s => ?_)
        dsimp only [Pi.mul_apply]; rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        have hz_nn : 0 ≤ dom_z z := mul_nonneg (mul_nonneg hCs0 hCφ0) (add_nonneg (add_nonneg
          (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
            mul_nonneg (hCA0 i j) (abs_nonneg _)))
          (Finset.sum_nonneg fun j _ => mul_nonneg (hCd0 j) (abs_nonneg _))) hCF0)
        rw [norm_mul, Real.norm_of_nonneg (indicator_nonneg (fun _ _ => zero_le_one) s),
          Real.norm_of_nonneg hz_nn]
      have hF_int : Integrable (Function.uncurry F_ker) (volume.prod μR) := by
        refine hdom_prod_int.mono' hF_meas ?_
        filter_upwards [Measure.quasiMeasurePreserving_snd.ae
          (ae_restrict_mem hQR_open.measurableSet)] with ⟨s, z⟩ hz
        rw [Function.uncurry_apply_pair, hF_eq s z, Real.norm_eq_abs]
        by_cases hs : s ∈ Icc 0 T₀
        · simp only [indicator_of_mem hs, one_mul]
          have hb_ρ : |ρ n (z.1 - s)| ≤ C_s := by
            have := (Real.norm_eq_abs _ ▸ hMρ (z.1 - s)).trans (le_max_left Mρ 0)
            dsimp [C_s]; linarith [le_max_right Mdρ 0]
          have hb_dρ : |_root_.deriv (ρ n) (z.1 - s)| ≤ C_s := by
            have := (Real.norm_eq_abs _ ▸ hMdρ (z.1 - s)).trans (le_max_left Mdρ 0)
            dsimp [C_s]; linarith [le_max_right Mρ 0]
          have hb_φ : |φ (s, z.2)| ≤ C_φ := by
            have := (Real.norm_eq_abs _ ▸ hMφ (s, z.2)).trans (le_max_left Mφ 0)
            have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => le_max_right (Mgφ i) 0
            dsimp [C_φ]; linarith
          have hb_gφ (i : Fin d) : |velocityGradient φ (s, z.2) i| ≤ C_φ := by
            have h1 : |velocityGradient φ (s, z.2) i| ≤ max (Mgφ i) 0 :=
              (Real.norm_eq_abs _ ▸ hMgφ i (s, z.2)).trans (le_max_left _ 0)
            have h2 : max (Mgφ i) 0 ≤ ∑ k : Fin d, max (Mgφ k) 0 :=
              Finset.single_le_sum (fun k _ => le_max_right (Mgφ k) 0) (Finset.mem_univ i)
            dsimp [C_φ]; linarith [le_max_right Mφ 0]
          refine (((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
            (add_le_add (abs_sub _ _) le_rfl)) le_rfl)).trans
            (add_le_add (add_le_add (add_le_add
              (b := C_s * C_φ * |U z|) (d := C_s * C_φ * ∑ i, ∑ j, CA i j * |G j z|) ?_ ?_)
              (d := C_s * C_φ * ∑ j, Cd j * |G j z|) ?_)
              (d := C_s * C_φ * CF) ?_)).trans_eq (by dsimp [dom_z]; ring)
          · rw [abs_mul, abs_mul, mul_comm |U z|]
            exact mul_le_mul_of_nonneg_right (mul_le_mul hb_dρ hb_φ (abs_nonneg _) hCs0) (abs_nonneg _)
          · rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_mul, abs_mul, mul_comm (C_s * C_φ)]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (hCA i j z hz) (abs_nonneg _))
              (mul_le_mul hb_ρ (hb_gφ i) (abs_nonneg _) hCs0)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (hCA0 i j) (abs_nonneg _))
          · rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_mul, abs_mul, mul_comm (C_s * C_φ)]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (hCd j z hz) (abs_nonneg _))
              (mul_le_mul hb_ρ hb_φ (abs_nonneg _) hCs0)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (hCd0 j) (abs_nonneg _))
          · rw [abs_mul, abs_mul, mul_comm (C_s * C_φ)]
            exact mul_le_mul (hCF z hz) (mul_le_mul hb_ρ hb_φ (abs_nonneg _) hCs0)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCF0
        · have hnot : (s, z.2) ∉ tsupport φ := fun hm => hs ⟨(hφsub hm).1.1.le, (hφsub hm).1.2.le⟩
          simp [indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport hnot, velocityGradient,
            (notMem_tsupport_iff_eventuallyEq.mp hnot).fderiv_eq]
      have hswap := integral_integral_swap hF_int
      have h_s_zero (s : ℝ) : (∫ z, F_ker s z ∂μR) = 0 := by
        simpa only [F_ker, AR, dR, FR, reverseTimeScalarCoefficient, zero_mul, add_zero] using
          (reverseTime_global_separated_product_distribution_of_reverseTimeVariationalEnergy
            a T haT hΩ hΩb A b (fun _ _ => 0) (fun t y => F (t, y))
            hAs hbs hcs hFs 0 u g hdu hu U hU hUslice G hG hGslice (η n s) (ψ s)).2
      simp_rw [h_s_zero, integral_zero] at hswap
      rw [hswap]; refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).symm
      have hi_dρ : Integrable (fun s : ℝ => _root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) volume :=
        ((((hρ_cd n).continuous_deriv (by simp)).comp (continuous_const.sub continuous_id)).mul
          (hφ.continuous.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact (hφc.isCompact.image continuous_fst)
            fun s hs => ⟨(s, z.2), subset_tsupport φ fun h0 => hs (by simp [h0]), rfl⟩)
      have hi_ρ := h_s_int hφ.continuous n z
      have hi_g (i : Fin d) := h_s_int (Φ := fun w => velocityGradient φ w i)
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) n z
      have h1 := hi_dρ.const_mul (U z)
      have h2 := integrable_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ => (hi_g i).const_mul (AR z.1 z.2 i j * G j z)
      have h3 := integrable_finsetSum Finset.univ fun j _ => hi_ρ.const_mul (dR z.1 z.2 j * G j z)
      simp_rw [hF_eq _ z]
      rw [integral_sub (f := fun s => U z * (_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) -
            (∑ i, ∑ j, AR z.1 z.2 i j * G j z * (ρ n (z.1 - s) * velocityGradient φ (s, z.2) i)) -
            ∑ j, dR z.1 z.2 j * G j z * (ρ n (z.1 - s) * φ (s, z.2)))
          (g := fun s => FR z * (ρ n (z.1 - s) * φ (s, z.2)))
          ((h1.sub h2).sub h3) (hi_ρ.const_mul (FR z)),
        integral_sub (f := fun s => U z * (_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)) -
            ∑ i, ∑ j, AR z.1 z.2 i j * G j z * (ρ n (z.1 - s) * velocityGradient φ (s, z.2) i))
          (g := fun s => ∑ j, dR z.1 z.2 j * G j z * (ρ n (z.1 - s) * φ (s, z.2))) (h1.sub h2) h3,
        integral_sub (f := fun s => U z * (_root_.deriv (ρ n) (z.1 - s) * φ (s, z.2)))
          (g := fun s => ∑ i, ∑ j, AR z.1 z.2 i j * G j z * (ρ n (z.1 - s) * velocityGradient φ (s, z.2) i))
          h1 h2,
        integral_const_mul, hibp1D n z, integral_const_mul,
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi_g i).const_mul _,
        integral_finsetSum _ fun j _ => hi_ρ.const_mul _]
      congr 2
      · congr 1; refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => (hi_g i).const_mul _]
        exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _
      · exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _
    obtain ⟨⟨B0, _, hb0⟩, hlim0⟩ := hconv1D hφ hφc
    obtain ⟨⟨Bt, _, hbt⟩, hlimt⟩ := hconv1D
      ((hφ.fderiv_right (by simp)).clm_apply contDiff_const) (hφc.fderiv_apply (𝕜 := ℝ) (1, 0))
    have hlimg (i : Fin d) := (hconv1D ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
      (hφc.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1))).2
    choose Bg _ hbg using fun i => (hconv1D ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
      (hφc.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1))).1
    let seq (n : ℕ) (z : TimeVelocity d) : ℝ :=
      U z * (∫ s : ℝ, ρ n (z.1 - s) * timeDerivative φ (s, z.2)) -
        (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z *
          (∫ s : ℝ, ρ n (z.1 - s) * velocityGradient φ (s, z.2) i)) -
        (∑ j : Fin d, dR z.1 z.2 j * G j z * (∫ s : ℝ, ρ n (z.1 - s) * φ (s, z.2))) -
        FR z * (∫ s : ℝ, ρ n (z.1 - s) * φ (s, z.2))
    let bound (z : TimeVelocity d) : ℝ :=
      Bt * |U z| + (∑ i : Fin d, ∑ j : Fin d, CA i j * Bg i * |G j z|) +
        (∑ j : Fin d, Cd j * B0 * |G j z|) + CF * B0
    have hbound_int : Integrable bound μR :=
      (((hU_L1.norm.const_mul Bt).add
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hG_L1 j).norm.const_mul (CA i j * Bg i))).add
        (integrable_finsetSum _ fun j _ => (hG_L1 j).norm.const_mul (Cd j * B0))).add
        (integrable_const (CF * B0))
    have hconv_cont {Φ : TimeVelocity d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
        (hΦc : HasCompactSupport Φ) (n : ℕ) :
        Continuous (fun z : TimeVelocity d => ∫ s : ℝ, ρ n (z.1 - s) * Φ (s, z.2)) := by
      have heq : (fun z : TimeVelocity d => ∫ s : ℝ, ρ n (z.1 - s) * Φ (s, z.2)) =
          fun z => ∫ r : ℝ, ρ n r * Φ (z.1 - r, z.2) := funext fun z =>
        (integral_congr_ae (Eventually.of_forall fun s => by rw [sub_sub_cancel])).trans
          (integral_sub_left_eq_self (fun r => ρ n r * Φ (z.1 - r, z.2)) volume z.1)
      rw [heq]
      obtain ⟨M₀, hM₀⟩ := hΦc.exists_bound_of_continuous hΦ.continuous
      exact continuous_of_dominated
        (fun _ => ((hρ_cd n).continuous.mul (hΦ.continuous.comp
          ((continuous_const.sub continuous_id).prodMk continuous_const))).aestronglyMeasurable)
        (bound := fun r => |ρ n r| * max M₀ 0)
        (fun z => Eventually.of_forall fun r => by
          show |ρ n r * Φ (z.1 - r, z.2)| ≤ |ρ n r| * max M₀ 0
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left
            ((Real.norm_eq_abs _ ▸ hM₀ _).trans (le_max_left _ _)) (abs_nonneg _))
        (((hρ_cd n).continuous.integrable_of_hasCompactSupport
          (bump n).hasCompactSupport_normed).norm.mul_const _)
        (Eventually.of_forall fun _ => continuous_const.mul
          (hΦ.continuous.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)))
    have hseq_meas (n : ℕ) : AEStronglyMeasurable (seq n) μR := by
      have ht := (hconv_cont ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
        (hφc.fderiv_apply (𝕜 := ℝ) (1, 0)) n).aestronglyMeasurable (μ := μR)
      have h0 := (hconv_cont hφ hφc n).aestronglyMeasurable (μ := μR)
      have hg (i : Fin d) := (hconv_cont ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
        (hφc.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1)) n).aestronglyMeasurable (μ := μR)
      exact (((hU_L1.aestronglyMeasurable.mul ht).sub
        (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
          Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
            ((((contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth).continuous.aestronglyMeasurable.mul
              (hG_L1 j).aestronglyMeasurable).mul (hg i)))).sub
        (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          (((hdR_smooth j).continuous.aestronglyMeasurable.mul
            (hG_L1 j).aestronglyMeasurable).mul h0))).sub
        (hFR_smooth.continuous.aestronglyMeasurable.mul h0)
    have hdom (n : ℕ) : ∀ᵐ z ∂μR, ‖seq n z‖ ≤ bound z := by
      filter_upwards [ae_restrict_mem hQR_open.measurableSet] with z hz
      rw [Real.norm_eq_abs]
      refine ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)) le_rfl)).trans
        (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_)
      · rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbt n z) (abs_nonneg _)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
        rw [abs_mul, abs_mul, mul_right_comm (CA i j)]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hCA i j z hz) (abs_nonneg _))
          (hbg i n z) (abs_nonneg _) (mul_nonneg (hCA0 i j) (abs_nonneg _))
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul, mul_right_comm (Cd j)]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hCd j z hz) (abs_nonneg _))
          (hb0 n z) (abs_nonneg _) (mul_nonneg (hCd0 j) (abs_nonneg _))
      · rw [abs_mul]; exact mul_le_mul (hCF z hz) (hb0 n z) (abs_nonneg _) hCF0
    exact tendsto_nhds_unique
      ((tendsto_integral_of_dominated_convergence bound hseq_meas hbound_int hdom
        (Eventually.of_forall fun z => (((tendsto_const_nhds.mul (hlimt z)).sub
          (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun _ _ =>
            tendsto_const_nhds.mul (hlimg i z))).sub
          (tendsto_finsetSum _ fun _ _ => tendsto_const_nhds.mul (hlim0 z))).sub
          (tendsto_const_nhds.mul (hlim0 z)))).congr hzero_n) tendsto_const_nhds
  have hadj_any (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφsub : tsupport φ ⊆ QR) :
      (∫ z in QR, U z * (timeDerivative φ z +
        (∑ j : Fin d, ∑ i : Fin d,
          velocityGradient (fun w => velocityGradient (fun q => AR q.1 q.2 i j * φ q) w i) z j) -
        ∑ j : Fin d, velocityGradient (fun w => bR w.1 w.2 j * φ w) z j)) =
      ∫ z in QR, FR z * φ z := by
    have hint_c {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
        Integrable (fun z => U z * f z) μR ∧ ∀ j, Integrable (fun z => G j z * f z) μR := by
      have hm := hf.continuous.memLp_top_of_hasCompactSupport hfc μR
      exact ⟨(hU_L1.smul_of_top_right hm).congr (Eventually.of_forall fun _ => mul_comm _ _),
        fun j => ((hG_L1 j).smul_of_top_right hm).congr (Eventually.of_forall fun _ => mul_comm _ _)⟩
    let Φ (j : Fin d) (z : TimeVelocity d) : ℝ :=
      (∑ i : Fin d, velocityGradient (fun q => AR q.1 q.2 i j * φ q) z i) - bR z.1 z.2 j * φ z
    have hΦ_eq (j : Fin d) (z : TimeVelocity d) :
        Φ j z = (∑ i : Fin d, AR z.1 z.2 i j * velocityGradient φ z i) + dR z.1 z.2 j * φ z := by
      dsimp only [Φ, dR, reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence,
        Pi.sub_apply, sub_mul]
      have hprod (i : Fin d) :
          velocityGradient (fun q => AR q.1 q.2 i j * φ q) z i =
            (fderiv ℝ (fun y => AR z.1 y i j) z.2) (PDE.basisVec i) * φ z +
              AR z.1 z.2 i j * velocityGradient φ z i := by
        have hAij : ContDiff ℝ (⊤ : ℕ∞) (fun q : TimeVelocity d => AR q.1 q.2 i j) :=
          (contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth
        have hslice : (fderiv ℝ (fun y => AR z.1 y i j) z.2) (PDE.basisVec i) =
            velocityGradient (fun q => AR q.1 q.2 i j) z i := by
          have hf := (hAij.differentiable (by simp) (z.1, z.2)).hasFDerivAt.comp z.2
            (hasFDerivAt_prodMk_right z.1 z.2)
          change (fderiv ℝ ((fun q : TimeVelocity d => AR q.1 q.2 i j) ∘ Prod.mk z.1) z.2)
            (PDE.basisVec i) = _
          rw [hf.fderiv]; rfl
        rw [hslice]; unfold velocityGradient
        have hfn_mul : (fun q : TimeVelocity d => AR q.1 q.2 i j * φ q) =
            (fun q => AR q.1 q.2 i j) * φ := rfl
        rw [hfn_mul, fderiv_mul (hAij.differentiable (by simp) z) (hφ.differentiable (by simp) z),
          add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]; ring
      simp_rw [hprod]; rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring
    have hΦ_smooth (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (Φ j) :=
      (ContDiff.sum fun i _ => ((((contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth).mul hφ).fderiv_right
        (by simp)).clm_apply contDiff_const).sub (((contDiff_apply ℝ ℝ j).comp hbR_smooth).mul hφ)
    have hΦ_supp (j : Fin d) : tsupport (Φ j) ⊆ tsupport φ :=
      closure_minimal (fun z hz => by
        rw [Function.mem_support, hΦ_eq] at hz; by_contra hnot
        exact hz (by simp [image_eq_zero_of_notMem_tsupport hnot, velocityGradient,
          (notMem_tsupport_iff_eventuallyEq.mp hnot).fderiv_eq])) (isClosed_tsupport φ)
    have hΦ_comp (j : Fin d) : HasCompactSupport (Φ j) :=
      HasCompactSupport.of_support_subset_isCompact hφc.isCompact
        ((subset_tsupport _).trans (hΦ_supp j))
    have hibp_j (j : Fin d) :
        (∫ z in QR, G j z * Φ j z) = -∫ z in QR, U z * velocityGradient (Φ j) z j := by
      linarith [hGweak j (Φ j) (hΦ_smooth j) (hΦ_comp j) ((hΦ_supp j).trans hφsub)]
    have hdΦ_eq (j : Fin d) (z : TimeVelocity d) :
        velocityGradient (Φ j) z j =
          (∑ i : Fin d,
            velocityGradient (fun w => velocityGradient (fun q => AR q.1 q.2 i j * φ q) w i) z j) -
          velocityGradient (fun w => bR w.1 w.2 j * φ w) z j := by
      have hd_i (i : Fin d) : DifferentiableAt ℝ
          (fun w => fderiv ℝ (fun q => AR q.1 q.2 i j * φ q) w (0, Pi.single i 1)) z :=
        (((((contDiff_apply_apply ℝ ℝ i j).comp hAR_smooth).mul hφ).fderiv_right
          (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).differentiable (by simp) z
      unfold velocityGradient Φ
      change fderiv ℝ ((fun w => ∑ i : Fin d, fderiv ℝ (fun q => AR q.1 q.2 i j * φ q) w
        (0, Pi.single i 1)) - fun w => bR w.1 w.2 j * φ w) z (0, Pi.single j 1) = _
      rw [fderiv_sub (f := fun w => ∑ i : Fin d, fderiv ℝ (fun q => AR q.1 q.2 i j * φ q) w
          (0, Pi.single i 1)) (g := fun w => bR w.1 w.2 j * φ w)
          (DifferentiableAt.fun_sum fun i _ => hd_i i)
          ((((contDiff_apply ℝ ℝ j).comp hbR_smooth).mul hφ).differentiable (by simp) z),
        sub_apply, fderiv_fun_sum (u := Finset.univ) (fun i _ => hd_i i), sum_apply]
    have hraw := hraw_any φ hφ hφc hφsub
    have hrew (z) :
        U z * timeDerivative φ z -
          (∑ i : Fin d, ∑ j : Fin d, AR z.1 z.2 i j * G j z * velocityGradient φ z i) -
          (∑ j : Fin d, dR z.1 z.2 j * G j z * φ z) - FR z * φ z =
        U z * timeDerivative φ z - (∑ j : Fin d, G j z * Φ j z) - FR z * φ z := by
      simp_rw [hΦ_eq]
      rw [Finset.sum_comm (f := fun i j => AR z.1 z.2 i j * G j z * velocityGradient φ z i)]
      have : (∑ j : Fin d, G j z * ((∑ i : Fin d, AR z.1 z.2 i j * velocityGradient φ z i) +
          dR z.1 z.2 j * φ z)) =
          (∑ j : Fin d, ∑ i : Fin d, AR z.1 z.2 i j * G j z * velocityGradient φ z i) +
          ∑ j : Fin d, dR z.1 z.2 j * G j z * φ z := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => by ring
      linarith
    simp_rw [hrew] at hraw
    have hi_Ut : Integrable (fun z => U z * timeDerivative φ z) μR :=
      (hint_c ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
        (hφc.fderiv_apply (𝕜 := ℝ) (1, 0))).1
    have hi_GΦ (j : Fin d) : Integrable (fun z => G j z * Φ j z) μR :=
      (hint_c (hΦ_smooth j) (hΦ_comp j)).2 j
    have hi_UdΦ (j : Fin d) : Integrable (fun z => U z * velocityGradient (Φ j) z j) μR :=
      (hint_c (((hΦ_smooth j).fderiv_right (by simp)).clm_apply contDiff_const)
        ((hΦ_comp j).fderiv_apply (𝕜 := ℝ) (0, Pi.single j 1))).1
    have hi_Fφ : Integrable (fun z => FR z * φ z) μR :=
      ((hFR_smooth.mul hφ).continuous.integrable_of_hasCompactSupport hφc.mul_left).restrict
    have hsum_GΦ : Integrable (fun z => ∑ j : Fin d, G j z * Φ j z) μR :=
      integrable_finsetSum Finset.univ fun j _ => hi_GΦ j
    dsimp only [μR] at hi_Ut hi_GΦ hi_UdΦ hi_Fφ hsum_GΦ hraw
    rw [integral_sub (f := fun z => U z * timeDerivative φ z - ∑ j, G j z * Φ j z)
        (g := fun z => FR z * φ z) (hi_Ut.sub hsum_GΦ) hi_Fφ,
      integral_sub (f := fun z => U z * timeDerivative φ z)
        (g := fun z => ∑ j, G j z * Φ j z) hi_Ut hsum_GΦ,
      integral_finsetSum _ fun j _ => hi_GΦ j] at hraw
    change (∫ z in QR, U z * timeDerivative φ z) -
      (∑ j, ∫ z in QR, G j z * Φ j z) - (∫ z in QR, FR z * φ z) = 0 at hraw
    simp_rw [hibp_j, Finset.sum_neg_distrib] at hraw
    have hsum_U : (∑ j : Fin d, ∫ z in QR, U z * velocityGradient (Φ j) z j) =
        ∫ z in QR, U z * ∑ j : Fin d, velocityGradient (Φ j) z j := by
      rw [← integral_finsetSum _ fun j _ => hi_UdΦ j]
      exact integral_congr_ae (Eventually.of_forall fun _ => (Finset.mul_sum _ _ _).symm)
    rw [sub_neg_eq_add, hsum_U, ← integral_add hi_Ut
      (by simpa only [Finset.mul_sum] using integrable_finsetSum _ fun j _ => hi_UdΦ j)] at hraw
    have hlhs : (∫ z in QR, (U z * timeDerivative φ z +
        U z * ∑ j : Fin d, velocityGradient (Φ j) z j)) =
        ∫ z in QR, U z * (timeDerivative φ z +
          (∑ j : Fin d, ∑ i : Fin d,
            velocityGradient (fun w => velocityGradient (fun q => AR q.1 q.2 i j * φ q) w i) z j) -
          ∑ j : Fin d, velocityGradient (fun w => bR w.1 w.2 j * φ w) z j) :=
      integral_congr_ae (Eventually.of_forall fun z => by simp_rw [hdΦ_eq, Finset.sum_sub_distrib]; ring)
    linarith
  let Ωx : Set (PDE.Vec (d + 1)) := tvCLE d ⁻¹' QR
  have hΩx : IsOpen Ωx := hQR_open.preimage (tvCLE d).continuous
  have hmp_QR := (measurePreserving_tvCLE).restrict_preimage_emb (measurableEmbedding_tvCLE) QR
  have hweak_x : HasWeakHormanderEquation Ωx (parabolicFields AR bR) (fun _ => 0)
      (FR ∘ tvCLE d) (U ∘ tvCLE d) := by
    refine ⟨fun _ _ => ⟨Ωx, self_mem_nhdsWithin,
      ((measurePreserving_tvCLE).integrableOn_comp_preimage (measurableEmbedding_tvCLE)).mpr hU_L1⟩,
      (hFR_smooth.comp (tvCLE d).contDiff).contDiffOn, fun ψ hψ hψc hψsub => ?_⟩
    let φ : TimeVelocity d → ℝ := ψ ∘ (tvCLE d).symm
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (tvCLE d).symm.contDiff
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph (tvCLE d).symm.toHomeomorph
    have hφsub : tsupport φ ⊆ QR := fun z hz => by
      have := hψsub (closure_minimal (s := Function.support φ) (fun _ h => subset_tsupport ψ h)
        ((isClosed_tsupport ψ).preimage (tvCLE d).symm.continuous) hz)
      simpa only [Ωx, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using this
    have hlhs := (measurePreserving_tvCLE).setIntegral_preimage_emb (measurableEmbedding_tvCLE)
      (fun z => U z * hormanderAdjointTest (parabolicFields AR bR) (fun _ => 0) ψ ((tvCLE d).symm z)) QR
    have hrhs := (measurePreserving_tvCLE).setIntegral_preimage_emb (measurableEmbedding_tvCLE)
      (fun z => FR z * φ z) QR
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hlhs hrhs
    have hrhs' : (∫ x in tvCLE d ⁻¹' QR, FR (tvCLE d x) * ψ x) = ∫ z in QR, FR z * φ z := by
      simp_rw [show ∀ x, ψ x = φ (tvCLE d x) from fun x =>
        (congrArg ψ (Fin.cons_self_tail x)).symm]
      exact hrhs
    dsimp only [Ωx, Function.comp_apply]
    rw [hlhs, hrhs', ← hadj_any φ hφ hφc hφsub]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only; congr 1
    have hadj := hormanderAdjointTest_parabolicFields hlam hAR_smooth hAR_lo hbR_smooth hψ
      ((tvCLE d).symm z)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hadj
    rw [hadj]; rfl
  obtain ⟨fx, hfx_smooth, hfx_ae⟩ := exists_smooth_aeRepresentative_of_hormander_aux hΩx
    (parabolicFields AR bR) (fun _ => 0) (FR ∘ tvCLE d) (U ∘ tvCLE d)
    (fun m => (contDiff_parabolicFields hlam hAR_smooth hAR_lo hbR_smooth m).contDiffOn)
    (lieAlgebraSpansOn_parabolicFields hlam hAR_lo bR Ωx) contDiffOn_const hweak_x
  let V : TimeVelocity d → ℝ := fx ∘ (tvCLE d).symm
  have hV_smooth : ContDiffOn ℝ (⊤ : ℕ∞) V QR :=
    hfx_smooth.comp (tvCLE d).symm.contDiff.contDiffOn fun _ hz => hz
  have hUV_ae : U =ᵐ[μR] V := by
    change U =ᵐ[volume.restrict QR] V
    rw [← hmp_QR.map_eq, Filter.EventuallyEq, (measurableEmbedding_tvCLE).ae_map_iff]
    refine hfx_ae.mono fun x hx => ?_
    dsimp only [V, Function.comp_apply, tvCLE_apply, tvCLE_symm_apply]
    rwa [show (Fin.cons (x 0) fun i => x i.succ) = x from Fin.cons_self_tail x]
  let D : Set (TimeVelocity d) := Ioo a T ×ˢ Ω
  have hD_open : IsOpen D := isOpen_Ioo.prod hΩ
  let revHomeo : TimeVelocity d ≃ₜ TimeVelocity d :=
    { toFun := fun z => (T - z.1, z.2)
      invFun := fun z => (T - z.1, z.2)
      left_inv := fun ⟨t, _⟩ => Prod.ext (sub_sub_cancel T t) rfl
      right_inv := fun ⟨t, _⟩ => Prod.ext (sub_sub_cancel T t) rfl
      continuous_toFun := hrev_smooth.continuous
      continuous_invFun := hrev_smooth.continuous }
  have hrev_coe (z : TimeVelocity d) : revHomeo z = (T - z.1, z.2) := rfl
  have hrev_inv (z : TimeVelocity d) : revHomeo (revHomeo z) = z := revHomeo.left_inv z
  have href : MeasurePreserving (fun r : ℝ => T - r) (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) T).comp (Measure.measurePreserving_neg volume)
  have hrev_mp : MeasurePreserving revHomeo volume volume := by
    rw [volume_timeVelocity_eq_prod]; exact href.prod (MeasurePreserving.id volume)
  have hpre_QR : revHomeo ⁻¹' QR = D := by
    ext ⟨t, y⟩; simp only [mem_preimage, hrev_coe, QR, D, reverseTimeOpenInterval, mem_prod, mem_Ioo]
    dsimp [T₀]; constructor <;> rintro ⟨⟨h1, h2⟩, hy⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hy⟩
  let w : TimeVelocity d → ℝ := V ∘ revHomeo
  have hw_c12 : IsScalarC12On w D := isScalarC12On_of_isOpen_contDiffOn_two hD_open
    ((hV_smooth.comp hrev_smooth.contDiffOn (hpre_QR ▸ mapsTo_preimage _ _)).of_le (by simp))
  have htime_mp : MeasurePreserving (fun r : ℝ => T - r)
      (volume.restrict (Ioo a T)) (reverseTimeVolume T₀) := by
    have hpre : (fun r : ℝ => T - r) ⁻¹' Ioo 0 T₀ = Ioo a T := by
      rw [preimage_const_sub_Ioo]; dsimp only [T₀]; congr 1 <;> ring
    rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpre]
    exact href.restrict_preimage isOpen_Ioo.measurableSet
  have hw_memLp : MemLp w 2 (timeVelocityVolumeOn D) :=
    (hU.ae_eq hUV_ae).comp_measurePreserving
      (hpre_QR ▸ hrev_mp.restrict_preimage_emb revHomeo.measurableEmbedding QR)
  have hUV_prod : U =ᵐ[(reverseTimeVolume T₀).prod (PDE.volumeOn Ω)] V :=
    (reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn T₀ Ω).symm ▸ hUV_ae
  have hw_slice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y :=
    htime_mp.quasiMeasurePreserving.ae (by
      filter_upwards [Measure.ae_ae_eq_curry_of_prod hUV_prod.symm, hUslice] with _ hVU hUu
      exact hVU.trans hUu)
  refine ⟨u, g, hdu, hu, w, hw_memLp, hw_slice, hw_c12, ?_⟩
  let R_D (z : TimeVelocity d) : ℝ :=
    scalarTimeDerivative w z + matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) +
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient w z) - F z
  have hRD_cont : ContinuousOn R_D D :=
    (((hw_c12.continuousOn_scalarTimeDerivative.add
      (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        (((contDiff_apply_apply ℝ ℝ i j).comp hA).continuous.continuousOn).mul
          ((continuous_apply j).comp_continuousOn
            ((continuous_apply i).comp_continuousOn hw_c12.continuousOn_scalarSpatialHessian)))).add
      (continuousOn_finsetSum _ fun j _ =>
        (((contDiff_apply ℝ ℝ j).comp hb).continuous.continuousOn).mul
          ((continuous_apply j).comp_continuousOn hw_c12.continuousOn_scalarSpatialGradient))).sub
      hF.continuous.continuousOn)
  have hRD_ae : ∀ᵐ z ∂volume, z ∈ D → R_D z = 0 := by
    refine hD_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hRD_cont.locallyIntegrableOn hD_open.measurableSet) fun ψ hψ hψc hψsub => ?_
    let φ : TimeVelocity d → ℝ := ψ ∘ revHomeo
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp hrev_smooth
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph revHomeo
    have hφsub : tsupport φ ⊆ QR := fun z hz => by
      have hzD : revHomeo z ∈ D := hψsub (closure_minimal
        (s := Function.support φ) (t := revHomeo ⁻¹' tsupport ψ)
        (fun _ h => subset_tsupport ψ h)
        ((isClosed_tsupport ψ).preimage revHomeo.continuous) hz)
      rwa [← hpre_QR, mem_preimage, hrev_inv] at hzD
    have hV_adj : (∫ z in QR, V z * (timeDerivative φ z +
        (∑ j : Fin d, ∑ i : Fin d,
          velocityGradient (fun x => velocityGradient (fun q => AR q.1 q.2 i j * φ q) x i) z j) -
        ∑ j : Fin d, velocityGradient (fun x => bR x.1 x.2 j * φ x) z j)) =
        ∫ z in QR, FR z * φ z := by
      rw [← hadj_any φ hφ hφc hφsub]
      exact integral_congr_ae (hUV_ae.mono fun _ hz => by dsimp only; rw [hz])
    have hlhs_pull := hrev_mp.setIntegral_preimage_emb revHomeo.measurableEmbedding
      (fun z => V z * (timeDerivative φ z +
        (∑ j : Fin d, ∑ i : Fin d,
          velocityGradient (fun x => velocityGradient (fun q => AR q.1 q.2 i j * φ q) x i) z j) -
        ∑ j : Fin d, velocityGradient (fun x => bR x.1 x.2 j * φ x) z j)) QR
    have hrhs_pull := hrev_mp.setIntegral_preimage_emb revHomeo.measurableEmbedding
      (fun z => FR z * φ z) QR
    rw [hpre_QR] at hlhs_pull hrhs_pull
    rw [← hlhs_pull, ← hrhs_pull] at hV_adj
    let dRev : TimeVelocity d →L[ℝ] TimeVelocity d :=
      ((0 : TimeVelocity d →L[ℝ] ℝ) - ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).prod
        (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
    have hdRev (x : TimeVelocity d) : HasFDerivAt revHomeo dRev x :=
      ((hasFDerivAt_const (x := x) T).sub hasFDerivAt_fst).prodMk hasFDerivAt_snd
    have hφ_dt (z : TimeVelocity d) : timeDerivative φ (revHomeo z) = -timeDerivative ψ z := by
      have hf := (hψ.differentiable (by simp) (revHomeo (revHomeo z))).hasFDerivAt.comp
        (revHomeo z) (hdRev (revHomeo z))
      change fderiv ℝ (ψ ∘ revHomeo) (revHomeo z) (1, 0) = _
      rw [hf.fderiv, ContinuousLinearMap.comp_apply,
        show fderiv ℝ ψ (revHomeo (revHomeo z)) = fderiv ℝ ψ z by rw [hrev_inv z],
        show dRev (1, 0) = -((1 : ℝ), (0 : PDE.Vec d)) by ext <;> simp [dRev], map_neg]; rfl
    have hvg_rev {g : TimeVelocity d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : Fin d)
        (z : TimeVelocity d) :
        velocityGradient (g ∘ revHomeo) (revHomeo z) k = velocityGradient g z k := by
      have hf := (hg.differentiable (by simp) (revHomeo (revHomeo z))).hasFDerivAt.comp
        (revHomeo z) (hdRev (revHomeo z))
      change fderiv ℝ (g ∘ revHomeo) (revHomeo z) (0, Pi.single k 1) = _
      rw [hf.fderiv, ContinuousLinearMap.comp_apply,
        show fderiv ℝ g (revHomeo (revHomeo z)) = fderiv ℝ g z by rw [hrev_inv z],
        show dRev (0, Pi.single k 1) = (0, Pi.single k 1) by ext <;> simp [dRev]]; rfl
    have hw_adj :
        (∫ z in D, w z * (-timeDerivative ψ z +
          (∑ j : Fin d, ∑ i : Fin d,
            velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j) -
          ∑ j : Fin d, velocityGradient (fun x => b x.1 x.2 j * ψ x) z j)) =
        ∫ z in D, F z * ψ z := by
      have hrhs_eq : (∫ z in D, FR (revHomeo z) * φ (revHomeo z)) = ∫ z in D, F z * ψ z :=
        setIntegral_congr_fun hD_open.measurableSet fun z _ => by simp [FR, φ, hrev_coe, sub_sub_cancel]
      rw [← hrhs_eq, ← hV_adj]
      refine setIntegral_congr_fun hD_open.measurableSet fun z _ => ?_
      dsimp only [w, Function.comp_apply]; congr 1; rw [hφ_dt z]; congr 1
      · congr 1; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        let g1 : TimeVelocity d → ℝ := fun q => A q.1 q.2 i j * ψ q
        have hg1 : ContDiff ℝ (⊤ : ℕ∞) g1 := ((contDiff_apply_apply ℝ ℝ i j).comp hA).mul hψ
        have heq2 : (fun x => velocityGradient (g1 ∘ revHomeo) x i) =
            (fun x => velocityGradient g1 x i) ∘ revHomeo :=
          funext fun x => by simpa only [Function.comp_apply, hrev_inv x] using hvg_rev hg1 i (revHomeo x)
        rw [show (fun q => AR q.1 q.2 i j * φ q) = g1 ∘ revHomeo from funext fun _ => rfl, heq2]
        exact (hvg_rev ((hg1.fderiv_right (by simp)).clm_apply contDiff_const) j z).symm
      · refine Finset.sum_congr rfl fun j _ => ?_
        let gb : TimeVelocity d → ℝ := fun x => b x.1 x.2 j * ψ x
        rw [show (fun x => bR x.1 x.2 j * φ x) = gb ∘ revHomeo from funext fun _ => rfl]
        exact (hvg_rev (((contDiff_apply ℝ ℝ j).comp hb).mul hψ) j z).symm
    have hint_D {f : TimeVelocity d → ℝ} (hf : ContinuousOn f D)
        {g : TimeVelocity d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
        (hgc : HasCompactSupport g) (hgD : tsupport g ⊆ D) :
        IntegrableOn (fun z => f z * g z) D volume :=
      (((hf.mono hgD).integrableOn_compact hgc.isCompact).mul_continuousOn
        hg.continuous.continuousOn hgc.isCompact).of_forall_sdiff_eq_zero hD_open.measurableSet
        fun _ hz => by simp [image_eq_zero_of_notMem_tsupport hz.2]
    have htsupp_vg {g : TimeVelocity d → ℝ} (k : Fin d) :
        tsupport (fun x => velocityGradient g x k) ⊆ tsupport g :=
      (closure_mono fun z (hz : fderiv ℝ g z (0, Pi.single k 1) ≠ 0) =>
        fun (h0 : fderiv ℝ g z = 0) => hz (by simp [h0])).trans (tsupport_fderiv_subset ℝ)
    have htsupp_dt {g : TimeVelocity d → ℝ} : tsupport (timeDerivative g) ⊆ tsupport g :=
      (closure_mono fun z (hz : fderiv ℝ g z (1, 0) ≠ 0) =>
        fun (h0 : fderiv ℝ g z = 0) => hz (by simp [h0])).trans (tsupport_fderiv_subset ℝ)
    have hibp_wt := hw_c12.hasWeakTimeDerivOn hD_open ψ hψ hψc hψsub
    have hibp_wb (j : Fin d) :
        (∫ z in D, w z * velocityGradient (fun x => b x.1 x.2 j * ψ x) z j) =
          -∫ z in D, scalarSpatialGradient w z j * (b z.1 z.2 j * ψ z) :=
      hw_c12.hasWeakVelocityPartialDerivOn hD_open j _
        (((contDiff_apply ℝ ℝ j).comp hb).mul hψ) hψc.mul_left (tsupport_mul_subset_right.trans hψsub)
    have hibp_wA (j i : Fin d) :
        (∫ z in D, w z *
          velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j) =
          ∫ z in D, scalarSpatialHessian w z j i * (A z.1 z.2 i j * ψ z) := by
      let g1 := fun q : TimeVelocity d => A q.1 q.2 i j * ψ q
      have hg1 : ContDiff ℝ (⊤ : ℕ∞) g1 := ((contDiff_apply_apply ℝ ℝ i j).comp hA).mul hψ
      have hg1D : tsupport g1 ⊆ D := tsupport_mul_subset_right.trans hψsub
      let g2 := fun x : TimeVelocity d => velocityGradient g1 x i
      rw [hw_c12.hasWeakVelocityPartialDerivOn hD_open j g2
          ((hg1.fderiv_right (by simp)).clm_apply contDiff_const)
          (hψc.mul_left.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1)) ((htsupp_vg i).trans hg1D),
        hw_c12.hasWeakVelocitySecondPartialDerivOn hD_open j i g1 hg1 hψc.mul_left hg1D, neg_neg]
    have hi_wt : IntegrableOn (fun z => -(w z * timeDerivative ψ z)) D volume :=
      (hint_D hw_c12.continuousOn ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)
        (hψc.fderiv_apply (𝕜 := ℝ) (1, 0)) (htsupp_dt.trans hψsub)).neg
    have hi_wA (j i : Fin d) : IntegrableOn (fun z => w z *
        velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j)
        D volume := by
      let g1 := fun q : TimeVelocity d => A q.1 q.2 i j * ψ q
      have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => velocityGradient g1 x i) :=
        ((((contDiff_apply_apply ℝ ℝ i j).comp hA).mul hψ).fderiv_right (by simp)).clm_apply contDiff_const
      exact hint_D hw_c12.continuousOn ((hg2.fderiv_right (by simp)).clm_apply contDiff_const)
        ((hψc.mul_left.fderiv_apply (𝕜 := ℝ) (0, Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (0, Pi.single j 1))
        ((htsupp_vg j).trans ((htsupp_vg i).trans (tsupport_mul_subset_right.trans hψsub)))
    have hi_wb (j : Fin d) : IntegrableOn
        (fun z => w z * velocityGradient (fun x => b x.1 x.2 j * ψ x) z j) D volume :=
      hint_D hw_c12.continuousOn
        (((((contDiff_apply ℝ ℝ j).comp hb).mul hψ).fderiv_right (by simp)).clm_apply contDiff_const)
        (hψc.mul_left.fderiv_apply (𝕜 := ℝ) (0, Pi.single j 1))
        ((htsupp_vg j).trans (tsupport_mul_subset_right.trans hψsub))
    have hi_sumA := integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun i _ => hi_wA j i
    have hi_sumb := integrable_finsetSum Finset.univ fun j _ => hi_wb j
    have hsplit_w :
        (∫ z in D, w z * (-timeDerivative ψ z +
          (∑ j : Fin d, ∑ i : Fin d,
            velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j) -
          ∑ j : Fin d, velocityGradient (fun x => b x.1 x.2 j * ψ x) z j)) =
        (∫ z in D, scalarTimeDerivative w z * ψ z) +
        (∑ j : Fin d, ∑ i : Fin d, ∫ z in D, scalarSpatialHessian w z j i * (A z.1 z.2 i j * ψ z)) +
        ∑ j : Fin d, ∫ z in D, scalarSpatialGradient w z j * (b z.1 z.2 j * ψ z) := by
      have hfn : (fun z => w z * (-timeDerivative ψ z +
          (∑ j, ∑ i, velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j) -
          ∑ j, velocityGradient (fun x => b x.1 x.2 j * ψ x) z j)) =
          fun z => (-(w z * timeDerivative ψ z) +
            ∑ j, ∑ i, w z * velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j) -
            ∑ j, w z * velocityGradient (fun x => b x.1 x.2 j * ψ x) z j := by
        funext z; simp only [mul_sub, mul_add, mul_neg, Finset.mul_sum]
      rw [hfn, integral_sub (f := fun z => -(w z * timeDerivative ψ z) +
            ∑ j, ∑ i, w z * velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j)
          (g := fun z => ∑ j, w z * velocityGradient (fun x => b x.1 x.2 j * ψ x) z j)
          (hi_wt.add hi_sumA) hi_sumb,
        integral_add (f := fun z => -(w z * timeDerivative ψ z))
          (g := fun z => ∑ j, ∑ i, w z * velocityGradient (fun x => velocityGradient (fun q => A q.1 q.2 i j * ψ q) x i) z j)
          hi_wt hi_sumA,
        integral_neg, hibp_wt, neg_neg,
        integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hi_wA j i,
        integral_finsetSum _ fun j _ => hi_wb j]
      simp_rw [hibp_wb, Finset.sum_neg_distrib, sub_neg_eq_add]
      congr 2; refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun i _ => hi_wA j i]
      exact Finset.sum_congr rfl fun i _ => hibp_wA j i
    rw [hsplit_w] at hw_adj
    have hi_dt := hint_D hw_c12.continuousOn_scalarTimeDerivative hψ hψc hψsub
    have hi_h (j i : Fin d) := hint_D (f := fun z => scalarSpatialHessian w z j i * A z.1 z.2 i j)
      (((continuous_apply i).comp_continuousOn
        ((continuous_apply j).comp_continuousOn hw_c12.continuousOn_scalarSpatialHessian)).mul
        (((contDiff_apply_apply ℝ ℝ i j).comp hA).continuous.continuousOn)) hψ hψc hψsub
    have hi_g (j : Fin d) := hint_D (f := fun z => scalarSpatialGradient w z j * b z.1 z.2 j)
      (((continuous_apply j).comp_continuousOn hw_c12.continuousOn_scalarSpatialGradient).mul
        (((contDiff_apply ℝ ℝ j).comp hb).continuous.continuousOn)) hψ hψc hψsub
    have hi_F := hint_D hF.continuous.continuousOn hψ hψc hψsub
    have hi_sumh := integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun i _ => hi_h j i
    have hi_sumg := integrable_finsetSum Finset.univ fun j _ => hi_g j
    have hpt : ∀ z ∈ D, ψ z * R_D z =
        scalarTimeDerivative w z * ψ z +
        (∑ j : Fin d, ∑ i : Fin d, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z) +
        (∑ j : Fin d, (scalarSpatialGradient w z j * b z.1 z.2 j) * ψ z) - F z * ψ z := by
      intro z hz; dsimp [R_D, matrixContraction, PDE.vecDot, coefficientAt]
      have h1 : (∑ i : Fin d, ∑ j : Fin d, A z.1 z.2 i j * scalarSpatialHessian w z i j) * ψ z =
          ∑ j : Fin d, ∑ i : Fin d, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z := by
        rw [Finset.sum_comm, Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [(scalarSpatialHessian_isSymm_of_c12 hw_c12 hz).apply i j]; ring
      have h2 : (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient w z j) * ψ z =
          ∑ j : Fin d, (scalarSpatialGradient w z j * b z.1 z.2 j) * ψ z := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
      linarith
    simp only [smul_eq_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport fun hm => hz (hψsub hm)],
      setIntegral_congr_fun hD_open.measurableSet hpt,
      integral_sub (f := fun z => scalarTimeDerivative w z * ψ z +
          (∑ j, ∑ i, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z) +
          ∑ j, (scalarSpatialGradient w z j * b z.1 z.2 j) * ψ z)
        (g := fun z => F z * ψ z) ((hi_dt.add hi_sumh).add hi_sumg) hi_F,
      integral_add (f := fun z => scalarTimeDerivative w z * ψ z +
          ∑ j, ∑ i, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z)
        (g := fun z => ∑ j, (scalarSpatialGradient w z j * b z.1 z.2 j) * ψ z)
        (hi_dt.add hi_sumh) hi_sumg,
      integral_add (f := fun z => scalarTimeDerivative w z * ψ z)
        (g := fun z => ∑ j, ∑ i, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z)
        hi_dt hi_sumh,
      integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hi_h j i,
      integral_finsetSum _ fun j _ => hi_g j]
    have hhh : (∑ j : Fin d, ∫ z in D, ∑ i : Fin d, (scalarSpatialHessian w z j i * A z.1 z.2 i j) * ψ z) =
        ∑ j : Fin d, ∑ i : Fin d, ∫ z in D, scalarSpatialHessian w z j i * (A z.1 z.2 i j * ψ z) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun i _ => hi_h j i]
      exact Finset.sum_congr rfl fun _ _ => setIntegral_congr_fun hD_open.measurableSet fun _ _ => by ring
    have hgg : (∑ j : Fin d, ∫ z in D, (scalarSpatialGradient w z j * b z.1 z.2 j) * ψ z) =
        ∑ j : Fin d, ∫ z in D, scalarSpatialGradient w z j * (b z.1 z.2 j * ψ z) :=
      Finset.sum_congr rfl fun _ _ => setIntegral_congr_fun hD_open.measurableSet fun _ _ => by ring
    linarith
  have hEq0 : EqOn R_D 0 D := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hD_open.measurableSet).mpr hRD_ae) hD_open hRD_cont continuousOn_const
  intro z hz; have := hEq0 hz; dsimp [R_D, Pi.zero_apply] at this; linarith

end Main

end HypoellipticAleksandrov.Parabolic.Dirichlet
