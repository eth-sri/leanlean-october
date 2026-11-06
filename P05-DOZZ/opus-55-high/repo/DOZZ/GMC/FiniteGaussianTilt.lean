/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GaussianCovariance
public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Finite-dimensional Gaussian translation from the standard Gaussian density. -/

public section

open MeasureTheory ProbabilityTheory ENNReal Matrix
open scoped Distributions NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace DOZZ.Proofs

lemma gaussianPDF_tilt (c x : ℝ) :
    gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2)) = gaussianPDF c 1 x := by
  unfold gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_one]
  calc
    _ = (Real.sqrt _)⁻¹ * (Real.exp _ * Real.exp (c * x - c ^ 2 / 2)) := by ring
    _ = (Real.sqrt _)⁻¹ * Real.exp _ := by rw [← Real.exp_add]
    _ = (Real.sqrt _)⁻¹ * Real.exp (-(x - c) ^ 2 / (2 * 1)) := by ring

lemma gaussianReal_tilt (c : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2))) = gaussianReal c 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num), gaussianReal_of_var_ne_zero c (by norm_num), ← withDensity_mul volume (measurable_gaussianPDF ..) (by fun_prop)]
  congr 1
  funext x
  exact gaussianPDF_tilt c x

lemma lintegral_pi_prod_fin : ∀ n (α : Type*) [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f : Fin n → α → ENNReal),
    (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ : Fin n => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  intro n
  induction n with
  | zero =>
      intro α _ μ _ f hf
      simp
  | succ n ih =>
      intro α _ μ _ f hf
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      let F : α × (Fin n → α) → ENNReal :=
        fun y => f 0 y.1 * ∏ j, f j.succ (y.2 j)
      have htail : Measurable (fun y : Fin n → α => ∏ j, f j.succ (y j)) := by
        fun_prop
      have hF : Measurable F := by fun_prop
      calc
        ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ : Fin (n + 1) => μ)
            = ∫⁻ y, F y ∂μ.prod (Measure.pi (fun _ : Fin n => μ)) := by
                calc
                  _ = ∫⁻ x, F (e x) ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
                        congr 1
                        funext x
                        simp [F, e, Fin.prod_univ_succ, Fin.tail]
                  _ = _ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).lintegral_map_equiv F e |>.symm
        _ = (∫⁻ x, f 0 x ∂μ) * ∫⁻ y, ∏ j, f j.succ (y j) ∂Measure.pi (fun _ : Fin n => μ) := by
              simpa using (lintegral_prod_mul
               
               
                (hf 0).aemeasurable htail.aemeasurable)
        _ = ∏ i, ∫⁻ x, f i x ∂μ := by
              rw [ih α μ (fun j => f j.succ) (fun j => hf j.succ), Fin.prod_univ_succ]
section
variable {n : ℕ}

lemma ennreal_exp_fin_sum (b : Fin n → ℝ) :
    ENNReal.ofReal (Real.exp (∑ i, b i)) = ∏ i, ENNReal.ofReal (Real.exp (b i)) := by
  have h : ∀ s : Finset (Fin n),
      ENNReal.ofReal (Real.exp (∑ i ∈ s, b i)) = ∏ i ∈ s, ENNReal.ofReal (Real.exp (b i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simp only [Finset.sum_insert his, Finset.prod_insert his, Real.exp_add]
        rw [ENNReal.ofReal_mul (by positivity), ih]
  simp_all

lemma pi_gaussian_tilt (c : Fin n → ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).withDensity
      (fun x => ENNReal.ofReal (Real.exp ((∑ i, c i * x i) - (∑ i, c i ^ 2) / 2))) =
      Measure.pi (fun i => gaussianReal (c i) 1) := by
  classical
  let base : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  let tilt : Fin n → ℝ → ENNReal := fun i x => ENNReal.ofReal (Real.exp (c i * x - c i ^ 2 / 2))
  let density : (Fin n → ℝ) → ENNReal := fun x => ENNReal.ofReal (Real.exp ((∑ i, c i * x i) - (∑ i, c i ^ 2) / 2))
  have hdensity (x : Fin n → ℝ) : density x = ∏ i, tilt i (x i) := by
    dsimp [density, tilt]
    have hsum : (∑ i, c i * x i) - (∑ i, c i ^ 2) / 2 = ∑ i, (c i * x i - c i ^ 2 / 2) := by
      calc
        _ = (∑ i, c i * x i) - ∑ i, c i ^ 2 / 2 := by rw [Finset.sum_div]
        _ = ∑ i, (c i * x i - c i ^ 2 / 2) := by simp
    rw [hsum, ennreal_exp_fin_sum]
  have htilt_meas (i : Fin n) : Measurable (tilt i) := by
    fun_prop
  have hrect : ∀ s : Fin n → Set ℝ, (∀ i, MeasurableSet (s i)) →
      ((Measure.pi base).withDensity density) (Set.univ.pi s) =
        ∏ i, (gaussianReal (c i) 1) (s i) := by
    intro s hs
    rw [withDensity_apply density (MeasurableSet.univ_pi hs)]
    let f : (i : Fin n) → ℝ → ENNReal := fun i x => (s i).indicator (tilt i) x
    have hf : ∀ i, Measurable (f i) := by
      intro i
      exact (htilt_meas i).indicator (hs i)
    have hpoint (x : Fin n → ℝ) :
        (Set.univ.pi s).indicator (fun x => ∏ i, tilt i (x i)) x = ∏ i, f i (x i) := by
      by_cases hx : ∀ i, x i ∈ s i
      · aesop
      · obtain ⟨i, hi⟩ := not_forall.mp hx
        have hr : x ∉ Set.univ.pi s := by
          intro h
          exact hi ((Set.mem_univ_pi.mp h) i)
        have hz : ∏ j, f j (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by aesop)
        simp_all
    calc
      _ = ∫⁻ x, (Set.univ.pi s).indicator (fun x => ∏ i, tilt i (x i)) x ∂Measure.pi base := by
            rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
            apply lintegral_congr_ae
            have hd : density = fun x => ∏ i, tilt i (x i) := funext hdensity
            exact ae_of_all _ (fun x => congrArg (fun g => (Set.univ.pi s).indicator g x) hd)
      _ = ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi base := by
            congr 1
            funext x
            exact hpoint x
      _ = ∏ i, ∫⁻ x, f i x ∂gaussianReal 0 1 := lintegral_pi_prod_fin n ℝ _ f hf
      _ = ∏ i, gaussianReal (c i) 1 (s i) := by
            apply Finset.prod_congr rfl
            intro i hi
            change ∫⁻ x, (s i).indicator (tilt i) x ∂gaussianReal 0 1 = _
            rw [lintegral_indicator (hs i), ← withDensity_apply (tilt i) (hs i), gaussianReal_tilt]
  refine (Measure.pi_eq hrect).symm

end

lemma stdGaussian_tilt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (v : E)
    (F : E → ENNReal) (hF : Measurable F) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (⟪v, z⟫ - ‖v‖ ^ 2 / 2)) * F z ∂(stdGaussian E) =
      ∫⁻ z, F (z + v) ∂(stdGaussian E) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let B : (Fin (Module.finrank ℝ E) → ℝ) → E := fun x => ∑ i, x i • b i
  let c : Fin (Module.finrank ℝ E) → ℝ := fun i => ⟪v, b i⟫
  let base : Fin (Module.finrank ℝ E) → Measure ℝ := fun _ => gaussianReal 0 1
  let density : (Fin (Module.finrank ℝ E) → ℝ) → ENNReal :=
    fun x => ENNReal.ofReal (Real.exp ((∑ i, c i * x i) - (∑ i, c i ^ 2) / 2))
  let shift : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun x i => x i + c i
  have hB : Measurable B := by fun_prop
  have hc (i : Fin (Module.finrank ℝ E)) : c i = ⟪b i, v⟫ := by
    dsimp [c]
    exact real_inner_comm ..
  have hnorm : ‖v‖ ^ 2 = ∑ i, c i ^ 2 := by
    calc
      ‖v‖ ^ 2 = ‖b.repr v‖ ^ 2 := by simp
      _ = ∑ i, (b.repr v).ofLp i ^ 2 := EuclideanSpace.real_norm_sq_eq _
      _ = ∑ i, c i ^ 2 := by simp [c, OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have hinner (x : Fin (Module.finrank ℝ E) → ℝ) : ⟪v, B x⟫ = ∑ i, c i * x i := by
    simp [B, c, inner_sum, real_inner_smul_right, mul_comm]
  have hweight (x : Fin (Module.finrank ℝ E) → ℝ) :
      ENNReal.ofReal (Real.exp (⟪v, B x⟫ - ‖v‖ ^ 2 / 2)) = density x := by
    aesop
  have hrepr : ∑ i, c i • b i = v := by
    simpa [hc] using b.sum_repr' v
  have hBshift (x : Fin (Module.finrank ℝ E) → ℝ) : B (shift x) = B x + v := by
    calc
      B (shift x) = (∑ i, x i • b i) + ∑ i, c i • b i := by
        dsimp [B, shift]
        calc
          ∑ i, (x i + c i) • b i = ∑ i, (x i • b i + c i • b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [add_smul]
          _ = (∑ i, x i • b i) + ∑ i, c i • b i := by rw [Finset.sum_add_distrib]
      _ = B x + v := by tauto
  have htilt : (Measure.pi base).withDensity density = Measure.pi (fun i => gaussianReal (c i) 1) := by
    simpa [base, density] using pi_gaussian_tilt c
  have hshift_meas : Measurable shift := by fun_prop
  have hshift : (Measure.pi base).map shift = Measure.pi (fun i => gaussianReal (c i) 1) := by
    rw [Measure.pi_map_pi (f := fun i x => x + c i) (fun i => by fun_prop)]
    simp_rw [base, gaussianReal_map_add_const]
    simp
  calc
    ∫⁻ z, ENNReal.ofReal _ * F z ∂(stdGaussian E)
        = ∫⁻ x, ENNReal.ofReal _ * F (B x)
            ∂Measure.pi base := by
              exact lintegral_map (by fun_prop) hB
    _ = ∫⁻ x, F (B x) ∂(Measure.pi base).withDensity density := by
          rw [lintegral_withDensity_eq_lintegral_mul (Measure.pi base) (by fun_prop) (by fun_prop)]
          apply lintegral_congr_ae
          exact ae_of_all _ (fun x => by
            change ENNReal.ofReal _ * F (B x) = density x * F (B x)
            rw [hweight x])
    _ = ∫⁻ x, F (B x) ∂Measure.pi (fun i => gaussianReal (c i) 1) := by simp_all
    _ = ∫⁻ x, F _ ∂Measure.pi base := by
          rw [← hshift]
          exact lintegral_map (hF.comp hB) hshift_meas
    _ = ∫⁻ x, F _ ∂Measure.pi base := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun x => congrArg F (hBshift x))
    _ = ∫⁻ z, F _ ∂(stdGaussian E) := by
          exact (lintegral_map (hF.comp (measurable_id.add_const v)) hB).symm

lemma multivariateGaussian_tilt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (a : EuclideanSpace ℝ ι)
    (F : EuclideanSpace ℝ ι → ENNReal) (hF : Measurable F) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (⟪a, y⟫ - ⟪a, WithLp.toLp 2 (Matrix.mulVec S a.ofLp)⟫ / 2)) * F y
        ∂multivariateGaussian 0 S =
      ∫⁻ y, F (y + WithLp.toLp 2 (Matrix.mulVec S a.ofLp)) ∂multivariateGaussian 0 S := by
  classical
  let A :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let sh := WithLp.toLp 2 (Matrix.mulVec S a.ofLp)
  have hAself : IsSelfAdjoint A := ((CFC.sqrt_nonneg S).isSelfAdjoint).map (toEuclideanCLM (𝕜 := ℝ))
  have hAinner (x z : EuclideanSpace ℝ ι) : ⟪x, A z⟫ = ⟪A x, z⟫ := by
    calc
      ⟪x, A z⟫ = ⟪A.adjoint x, z⟫ := (ContinuousLinearMap.adjoint_inner_left A z x).symm
      _ = ⟪A x, z⟫ := by tauto
  have hA2 : A (A a) = sh := by
    ext i
    change (CFC.sqrt S *ᵥ (CFC.sqrt S *ᵥ a.ofLp)) i = (S *ᵥ a.ofLp) i
    rw [Matrix.mulVec_mulVec, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hnorm : ‖A a‖ ^ 2 = ⟪a, sh⟫ := by
    calc
      ‖A a‖ ^ 2 = ⟪A a, A a⟫ := (real_inner_self_eq_norm_sq (A a)).symm
      _ = ⟪a, A (A a)⟫ := (hAinner a (A a)).symm
      _ = ⟪a, sh⟫ := by simp_all
  have hshift (z : EuclideanSpace ℝ ι) : A (z + A a) = A z + sh := by
    rw [map_add, hA2]
  calc
    ∫⁻ y, ENNReal.ofReal _ * F y ∂multivariateGaussian 0 S
        = ∫⁻ z, ENNReal.ofReal _ * F (A z)
            ∂stdGaussian _ := by
              rw [multivariateGaussian]
              simp
              exact lintegral_map (by fun_prop) A.continuous.measurable
    _ = ∫⁻ z, ENNReal.ofReal _ * F (A z)
            ∂stdGaussian _ := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun z => by
                change ENNReal.ofReal _ * F (A z) =
                  ENNReal.ofReal _ * F (A z)
                rw [hAinner a z, hnorm])
    _ = ∫⁻ z, F _ ∂stdGaussian _ := (stdGaussian_tilt (A a) (fun z => F (A z)) (hF.comp A.continuous.measurable))
    _ = ∫⁻ z, F _ ∂stdGaussian _ := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun z => congrArg F (hshift z))
    _ = ∫⁻ y, F _ ∂multivariateGaussian 0 S := by
          rw [multivariateGaussian]
          simp
          exact (lintegral_map (μ := stdGaussian _)
            (hF.comp (measurable_id.add_const sh)) A.continuous.measurable).symm
section
variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
section
variable (P : Measure Ω) (Z : Ω → ι → ℝ)
section
variable (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (i : ι) [DecidableEq ι]
include hZ


lemma coord_mean : ∫ ω, Z ω i ∂P = 0 := by
  let a : ι → ℝ := fun j => if j = i then 1 else 0
  obtain ⟨hmem, ⟨v, hmap⟩⟩ := hZ.2.2 a
  have hsum : (fun ω => ∑ j, a j * Z ω j) = fun ω => Z ω i := by
    aesop
  have hmap' : P.map (fun ω => Z ω i) = gaussianReal 0 v := by
    simp_all
  have hIntId : Integrable id (P.map (fun ω => Z ω i)) := by
    rw [hmap']
    exact (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable (by norm_num)
  calc
    ∫ ω, Z ω i ∂P = ∫ x, x ∂P.map (fun ω => Z ω i) := by
      symm
      exact integral_map (hZ.2.1 i) hIntId.aestronglyMeasurable
    _ = ∫ x, x ∂gaussianReal 0 v := by simp_all
    _ = 0 := by simp

lemma coord_memLp : MemLp (fun ω => Z ω i) 2 P := by
  let a : ι → ℝ := fun j => if j = i then 1 else 0
  have hm := (hZ.2.2 a).1
  aesop

end

end

theorem represent [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z) :
    ∃ S : Matrix ι ι ℝ, S.PosSemidef ∧
      P.map (fun ω => WithLp.toLp 2 (Z ω)) = multivariateGaussian 0 S ∧
      ∀ i j, S i j = DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
  classical
  let : IsProbabilityMeasure P := hZ.1
  let Y : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (Z ω)
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  have hYmeas : AEMeasurable Y P := by fun_prop
  have hYgauss : IsGaussian (P.map Y) := by
    refine isGaussian_of_map_eq_gaussianReal ?_
    intro L
    let a : ι → ℝ := fun i => L (EuclideanSpace.basisFun ι ℝ i)
    have hlin : (fun ω => L (Y ω)) = fun ω => ∑ i, a i * Z ω i := by
      funext ω
      rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr (Y ω)]
      simp
      simp [a, Y, mul_comm]
    obtain ⟨_, ⟨v, hmap⟩⟩ := hZ.2.2 a
    refine ⟨0, v, ?_⟩
    calc
      (P.map Y).map L = P.map _ :=
        AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hYmeas
      _ = P.map (fun ω => ∑ i, a i * Z ω i) := by
        congr 1
      _ = gaussianReal 0 v := hmap
  let μ := P.map Y
  let b := EuclideanSpace.basisFun ι ℝ
  let S := LinearMap.BilinForm.toMatrix b.toBasis (covarianceBilin μ).toBilinForm
  have hIntCoords : ∀ i, MemLp (fun ω => Z ω i) 2 P := fun i => coord_memLp P Z hZ i
  have hentry (i j : ι) : S i j = DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
    have hbase := covarianceBilin_apply_basisFun hIntCoords i j
    have hcentered := covariance_eq_sub (hIntCoords i) (hIntCoords j)
    rw [coord_mean P Z hZ i, coord_mean P Z hZ j] at hcentered
    calc
      S i j = covarianceBilin μ (b i) (b j) := by
        simp [S, LinearMap.BilinForm.toMatrix_apply]
      _ = cov[fun ω => Z ω i, fun ω => Z ω j; P] := hbase
      _ = DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
        rw [hcentered]
        simp [DOZZ.gaussianCovariance]
  have hS : S.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      simp [S, LinearMap.BilinForm.toMatrix_apply, covarianceBilin_comm]
    · intro x
      have hp := (isPosSemidef_covarianceBilin (μ := μ)).nonneg (b.toBasis.equivFun.symm x)
      have heq : x ⬝ᵥ S *ᵥ x = covarianceBilin μ (b.toBasis.equivFun.symm x) (b.toBasis.equivFun.symm x) := by
        rw [LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
        rfl
      simp_all
  have hmean : ∫ x, x ∂μ = 0 := by
    have hIdInt : Integrable id μ := by
      let : IsGaussian μ := hYgauss
      exact ProbabilityTheory.IsGaussian.integrable_id
    change ∫ x, (id x) ∂P.map Y = 0
    rw [integral_map hYmeas hIdInt.aestronglyMeasurable]
    have hIntY : Integrable Y P := by
      apply Integrable.of_eval_piLp
      intro i
      simpa [Y] using (hIntCoords i).integrable (by norm_num)
    ext i
    have hp := (EuclideanSpace.proj i).integral_comp_comm hIntY
    simp at hp
    change (∫ ω, Y ω ∂P).ofLp i = 0
    rw [← hp]
    simpa [Y] using coord_mean P Z hZ i
  have hcov : covarianceBilin μ = covarianceBilin (multivariateGaussian 0 S) := by
    ext x y
    rw [covarianceBilin_multivariateGaussian hS]
    have hx : (b.toBasis.repr x) = x.ofLp := by
      funext i
      rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    have hy : (b.toBasis.repr y) = y.ofLp := by
      funext i
      rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    calc
      covarianceBilin μ x y = (b.toBasis.repr x) ⬝ᵥ S *ᵥ (b.toBasis.repr y) := by
        simpa [S] using (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
          b.toBasis (covarianceBilin μ).toBilinForm x y)
      _ = x.ofLp ⬝ᵥ S *ᵥ y.ofLp := by rfl
  refine ⟨S, hS, ?_, hentry⟩
  change μ = multivariateGaussian 0 S
  let : IsGaussian μ := hYgauss
  have hmean' : ∫ x, x ∂μ = ∫ x, x ∂multivariateGaussian 0 S := by
    rw [hmean]
    simp
  exact IsGaussian.ext hmean' hcov

/-- Finite Cameron--Martin tilt, proved through the covariance square root and the standard
Gaussian density identity. This proof also covers singular covariance matrices. -/
theorem finite_gaussian_tilt
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (a : ι → ℝ)
    (F : (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω,
      ENNReal.ofReal (Real.exp
        ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P (fun ω => Z ω i)
            (fun ω => Z ω j) * a j) / 2)) * F (Z ω) ∂P) =
    ∫⁻ ω, F (fun i => Z ω i +
      ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) ∂P := by
  classical
  obtain ⟨S, hS, hLaw, hEntry⟩ := represent P Z hZ
  let Y : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (Z ω)
  let aE := WithLp.toLp 2 a
  let sh := WithLp.toLp 2 (S *ᵥ a)
  let F' : EuclideanSpace ℝ ι → ℝ≥0∞ := fun y => F y.ofLp
  let weight : EuclideanSpace ℝ ι → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (⟪aE, y⟫ - ⟪aE, sh⟫ / 2)) * F' y
  have hweight : Measurable weight := by
    fun_prop
  have hY : AEMeasurable Y P := by
    have hZae : AEMeasurable Z P := by
      apply AEMeasurable.of_eval
      intro i
      exact hZ.2.1 i
    fun_prop
  have hlin (ω : Ω) : ⟪aE, Y ω⟫ = ∑ i, a i * Z ω i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [aE, Y, dotProduct, star_trivial, mul_comm]
  have hquad : ⟪aE, sh⟫ = ∑ i, ∑ j, a i * S i j * a j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [aE, sh, star_trivial, dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hvariance :
      ⟪aE, sh⟫ = ∑ i, ∑ j, a i * DOZZ.gaussianCovariance P
        (fun ω => Z ω i) (fun ω => Z ω j) * a j := by
    rw [hquad]
    simp_rw [hEntry]
  have hshift (y : EuclideanSpace ℝ ι) :
      F' (y + sh) = F (fun i => y.ofLp i +
        ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) := by
    change F ((y + sh).ofLp) = F _
    apply congrArg F
    funext i
    simp [sh, Matrix.mulVec, hEntry, dotProduct, mul_comm]
  calc
    _ = ∫⁻ ω, weight (Y ω) ∂P := by
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        simp only [weight, F', Y]
        rw [hlin, hvariance])
    _ = ∫⁻ y, weight y ∂P.map Y := (lintegral_map' hweight.aemeasurable hY).symm
    _ = ∫⁻ y, weight y ∂multivariateGaussian 0 S := by tauto
    _ = ∫⁻ y, F' (y + sh) ∂multivariateGaussian 0 S := by
      dsimp [weight, F', aE, sh]
      exact multivariateGaussian_tilt S hS _
        (fun y => F y.ofLp) (hF.comp (WithLp.measurable_ofLp 2 (ι → ℝ)))
    _ = ∫⁻ y, F' _ ∂P.map Y := by tauto
    _ = ∫⁻ ω, F' _ ∂P :=
      lintegral_map' ((hF.comp (WithLp.measurable_ofLp 2 (ι → ℝ))).comp (measurable_id.add_const sh)).aemeasurable hY
    _ = ∫⁻ ω, F (fun i => Z ω i +
        ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) ∂P := by
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        simpa [Y] using hshift (Y ω))

end


end DOZZ.Proofs
