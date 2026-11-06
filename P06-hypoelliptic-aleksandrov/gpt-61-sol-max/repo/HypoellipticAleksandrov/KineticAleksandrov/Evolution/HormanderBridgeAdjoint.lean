module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeDiv
public import PDEFoundation.Calculus.RegularityOrder


/-!
# The formal adjoint of `Lop`, in the paper's form and in Hörmander's form

The companion paper, (A.2), writes the formal adjoint of
`Lop = ∂_σ + ∑ B_ij ∂_{v_i v_j} + b(v) · ∇_z` as
`Lop^* ψ = -∂_σ ψ + ∑_{i,j} ∂_{v_i v_j}(B_ij ψ) - b(v) · ∇_z ψ`.
`transportedAdjoint` is this expression in the packed coordinates `(σ, v, z)` of `BracketCoord`
(`regularizedAdjoint` adds `ε Δ_z ψ`).

The main results `hormanderAdjointTest_transportedFields` and
`hormanderAdjointTest_regularizedFields` identify `hormanderAdjointTest` (the carrier,
`-div(ψ X_0) + ∑ div(div(ψ X_i) X_i) + c ψ`, with `c = 0`) for the field families
`transportedFields B b` and `regularizedFields B b ε` with these expressions, for every smooth
test function `ψ` and at every point.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

variable (B : FullKineticCoefficient n) (b : PDE.VectorField n)

/-- The formal adjoint `Lop^* ψ = -∂_σ ψ + ∑_{i,j} ∂_{v_i v_j}(B_ij ψ) - b(v) · ∇_z ψ`
of the transported operator ((A.2)), in packed coordinates. -/
def transportedAdjoint
    (ψ : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  -fderiv ℝ ψ x basisT +
    ∑ i, ∑ j, fderiv ℝ (fun y => fderiv ℝ (fun w =>
      B (timeCoord n w) (diffusedCoord n w) (transportedCoord n w) i j * ψ w) y (basisV j))
        x (basisV i) -
    ∑ l, b (diffusedCoord n x) l * fderiv ℝ ψ x (basisZ l)

/-- The formal adjoint `Lop^* ψ + ε Δ_z ψ` of the regularised operator `L_ε = Lop + ε Δ_z`
(companion paper, (A.2)), in packed coordinates. -/
def regularizedAdjoint  (ε : ℝ)
    (ψ : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  transportedAdjoint B b ψ x +
    ε * ∑ l, fderiv ℝ (fun y => fderiv ℝ ψ y (basisZ l)) x (basisZ l)

/-! ### Smoothness helpers -/

section
variable {f : EvolutionVec n → ℝ} (hf : ContDiff ℝ PDE.smoothOrder f)

include hf
theorem contDiff_fderiv_apply
    (w : EvolutionVec n) : ContDiff ℝ PDE.smoothOrder (fun y => fderiv ℝ f y w) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem differentiableAt_of_contDiff
    (x : EvolutionVec n) : DifferentiableAt ℝ f x :=
  hf.differentiable (by simp) x
end


/-! ### Divergence of the squared fields -/

variable {B : FullKineticCoefficient n}

theorem smul_diffusionField  (w : ℝ) (i : Fin n)
    (x : EvolutionVec n) :
    w • diffusionField B i x = packPoint 0 (fun j => w * sqrtCoeffAt B x i j) 0 := by
  rw [diffusionField, ← packPoint_smul]
  simp [Pi.smul_def]

/-- The divergence of `w X_i` is `∑_k ∂_{v_k}(w β_ik)`. -/
theorem euclideanDivergence_smul_diffusionField
    (hβ : ∀ i j, ContDiff ℝ PDE.smoothOrder (fun x => sqrtCoeffAt B x i j)) {w : EvolutionVec n → ℝ}
    {x : EvolutionVec n} (hw : DifferentiableAt ℝ w x) (i : Fin n) :
    euclideanDivergence (fun y => w y • diffusionField B i y) x =
      ∑ k, fderiv ℝ (fun y => w y * sqrtCoeffAt B y i k) x (basisV k) := by

  rw [(funext fun y => smul_diffusionField (B := B) (w y) i y), euclideanDivergence_packPoint (s := fun _ => (0 ))
    (g := fun y j => w y * sqrtCoeffAt B y i j) (h := fun _ => (0 ))
    (differentiableAt_const _) (fun j => hw.mul (differentiableAt_of_contDiff (hβ i j) x))
    (fun l => differentiableAt_const _)]
  simp

/-! ### Divergence of the drift field -/

theorem smul_driftField  {b : PDE.VectorField n} (w : ℝ)
    (x : EvolutionVec n) :
    w • driftField B b x =
      packPoint w (fun k => -(w * driftCorrection B k x))
        (fun l => w * b (diffusedCoord n x) l) := by
  rw [driftField, ← packPoint_smul]
  simp only [mul_one]
  congr 1
  funext k
  simp

theorem fderiv_drift_transported_zero {b : PDE.VectorField n} (hb : ContDiff ℝ PDE.smoothOrder b)
    (x : EvolutionVec n) (l m : Fin n) :
    fderiv ℝ (fun y => b (diffusedCoord n y) l) x (basisZ m) = 0 := by


  have := ((contDiff_pi.1 hb l).differentiable (by simp) _).hasFDerivAt.comp x (diffusedCoord n).hasFDerivAt

  change fderiv ℝ ((((fun v : PDE.Vec n => b v l))) ∘ (diffusedCoord n)) x (basisZ m) = 0
  rw [this.fderiv]
  simp [basisZ]

theorem euclideanDivergence_smul_driftField {B : FullKineticCoefficient n}
    {b : PDE.VectorField n}
    (hβ : ∀ i j, ContDiff ℝ PDE.smoothOrder (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ PDE.smoothOrder b) {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (x : EvolutionVec n) :
    euclideanDivergence (fun y => φ y • driftField B b y) x =
      fderiv ℝ φ x basisT + ∑ k, fderiv ℝ (fun y => -(φ y * driftCorrection B k y)) x (basisV k)
        + ∑ l, b (diffusedCoord n x) l * fderiv ℝ φ x (basisZ l) := by

  have hbl : ∀ l, ContDiff ℝ PDE.smoothOrder (fun y => b (diffusedCoord n y) l) := fun l =>
    (contDiff_pi.1 hb l).comp (diffusedCoord n).contDiff

  rw [(funext fun y => smul_driftField (B := B) (b := b) (φ y) y), euclideanDivergence_packPoint (s := φ)
    (g := fun y k => -(φ y * driftCorrection B k y))
    (h := fun y l => φ y * b (diffusedCoord n y) l) (differentiableAt_of_contDiff hφ x)
    (fun k => ((differentiableAt_of_contDiff hφ x).mul
      (differentiableAt_of_contDiff ((contDiff_driftCorrection hβ) k) x)).neg)
    (fun l => (differentiableAt_of_contDiff hφ x).mul (differentiableAt_of_contDiff (hbl l) x))]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_fun_mul (differentiableAt_of_contDiff hφ x) (differentiableAt_of_contDiff (hbl l) x)]
  simp only [add_apply, smul_apply,
    fderiv_drift_transported_zero hb, smul_eq_mul, mul_zero, zero_add]

/-! ### The identity for `Lop` -/

section Identity

variable {B : FullKineticCoefficient n} {b : PDE.VectorField n} {lam Lam : ℝ}

section
variable (hβ : ∀ i j, ContDiff ℝ PDE.smoothOrder (fun x => sqrtCoeffAt B x i j)) {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ) (i : Fin n)

include hβ hφ
theorem contDiff_divDiffusion
     :
    ContDiff ℝ PDE.smoothOrder (fun y => ∑ j, fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y
      (basisV j)) :=
  ContDiff.sum fun j _ => contDiff_fderiv_apply (hφ.mul (hβ i j)) _

/-- The iterated divergence `div(div(φ X_i) X_i)` in explicit form. -/
theorem euclideanDivergence_euclideanDivergence_diffusion
     (x : EvolutionVec n) :
    euclideanDivergence (fun y =>
        euclideanDivergence (fun q => φ q • diffusionField B i q) y • diffusionField B i y) x =
      ∑ k, fderiv ℝ (fun y => (∑ j, fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y (basisV j)) *
        sqrtCoeffAt B y i k) x (basisV k) := by
  have hw'  := fun y =>
    euclideanDivergence_smul_diffusionField hβ (differentiableAt_of_contDiff hφ y) i

  rw [euclideanDivergence_smul_diffusionField hβ (show DifferentiableAt ℝ (fun y => euclideanDivergence
      (fun q => φ q • diffusionField B i q) y) x by
      simp only [hw']
      exact differentiableAt_of_contDiff (contDiff_divDiffusion hβ hφ i) x) i]
  simp only [hw']
end


/-- Coefficient identity: `∑_j ∂_j(B_kj φ) = φ c_k + ∑_i div(φ X_i) β_ik`. -/
theorem sum_fderiv_coeff_mul (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hβ : ∀ i j, ContDiff ℝ PDE.smoothOrder (fun x => sqrtCoeffAt B x i j))
    {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ) (k : Fin n) (y : EvolutionVec n) :
    ∑ j, fderiv ℝ (fun w => B (timeCoord n w) (diffusedCoord n w) (transportedCoord n w) k j *
        φ w) y (basisV j) =
      φ y * driftCorrection B k y +
        ∑ i, (∑ j, fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y (basisV j)) *
          sqrtCoeffAt B y i k := by
  have hB' : ∀ j, (fun w => B (timeCoord n w) (diffusedCoord n w) (transportedCoord n w) k j *
      φ w) = fun w => ∑ i, sqrtCoeffAt B w i k * (φ w * sqrtCoeffAt B w i j) := by
    intro j
    funext w
    rw [← sum_sqrtCoeffAt_mul hlam hell w k j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hB']
  have hd : ∀ i j, DifferentiableAt ℝ (fun w => sqrtCoeffAt B w i k * (φ w *
      sqrtCoeffAt B w i j)) y := fun i j =>
    (differentiableAt_of_contDiff (hβ i k) y).mul
      ((differentiableAt_of_contDiff hφ y).mul (differentiableAt_of_contDiff (hβ i j) y))
  have hs : ∀ j, fderiv ℝ (fun w => ∑ i, sqrtCoeffAt B w i k * (φ w * sqrtCoeffAt B w i j)) y
      (basisV j) = ∑ i, (sqrtCoeffAt B y i k * fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y
        (basisV j) + fderiv ℝ (fun w => sqrtCoeffAt B w i k) y (basisV j) *
          (φ y * sqrtCoeffAt B y i j)) := by
    intro j
    rw [fderiv_fun_sum fun i _ => hd i j, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_fun_mul (c := fun w => sqrtCoeffAt B w i k)
      (d := fun w => φ w * sqrtCoeffAt B w i j) (differentiableAt_of_contDiff (hβ i k) y)
      ((differentiableAt_of_contDiff hφ y).mul (differentiableAt_of_contDiff (hβ i j) y))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have h1 : ∑ j, ∑ i, fderiv ℝ (fun w => sqrtCoeffAt B w i k) y (basisV j) *
      (φ y * sqrtCoeffAt B y i j) = φ y * driftCorrection B k y := by
    rw [Finset.sum_comm, driftCorrection, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [basisV]; ring
  have h2 : ∑ j, ∑ i, sqrtCoeffAt B y i k * fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y
      (basisV j) = ∑ i, (∑ j, fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y (basisV j)) *
        sqrtCoeffAt B y i k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hs, Finset.sum_add_distrib]
  rw [h1, h2, add_comm]

/-- **Weak-form bridge for `Lop`.**  For a smooth test function `φ`, the carrier
`hormanderAdjointTest` of the field family `transportedFields B b` (with `c = 0`) is the paper's
formal adjoint `Lop^* φ` ((A.2)). -/
theorem hormanderAdjointTest_transportedFields (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (x : EvolutionVec n) :
    hormanderAdjointTest (transportedFields B b) (fun _ => 0) φ x = transportedAdjoint B b φ x := by
  have hβ := contDiff_sqrtCoeffAt_entry hlam hB hell

  have hF : ∀ k i, ContDiff ℝ PDE.smoothOrder (fun y => (∑ j, fderiv ℝ (fun z => φ z *
      sqrtCoeffAt B z i j) y (basisV j)) * sqrtCoeffAt B y i k) := fun k i =>
    (contDiff_divDiffusion hβ hφ i).mul (hβ i k)
  have hφc  := fun k =>
    hφ.mul ((contDiff_driftCorrection hβ) k)

  have hRHS : ∀ k, ∑ j, fderiv ℝ (fun y => fderiv ℝ (fun w =>
      B (timeCoord n w) (diffusedCoord n w) (transportedCoord n w) k j * φ w) y (basisV j))
        x (basisV k) =
      fderiv ℝ (fun y => φ y * driftCorrection B k y) x (basisV k) +
        ∑ i, fderiv ℝ (fun y => (∑ j, fderiv ℝ (fun z => φ z * sqrtCoeffAt B z i j) y
          (basisV j)) * sqrtCoeffAt B y i k) x (basisV k) := by
    intro k
    rw [← sum_apply, ← fderiv_fun_sum fun j _ => differentiableAt_of_contDiff ((fun i j => contDiff_fderiv_apply ((contDiff_coeffAt_entry hB i j).mul hφ) _) k j) x]
    simp only [sum_fderiv_coeff_mul hlam hell hβ hφ k]
    rw [fderiv_fun_add (differentiableAt_of_contDiff (hφc k) x)
      (differentiableAt_of_contDiff (ContDiff.sum fun i _ => hF k i) x),
      fderiv_fun_sum fun i _ => differentiableAt_of_contDiff (hF k i) x]
    simp only [add_apply, sum_apply]
  unfold hormanderAdjointTest transportedAdjoint
  simp only [transportedFields, Fin.cons_zero, Fin.cons_succ, zero_mul, add_zero]
  rw [euclideanDivergence_smul_driftField hβ hb hφ x]
  simp only [euclideanDivergence_euclideanDivergence_diffusion hβ hφ, hRHS,
    fderiv_fun_neg, neg_apply, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i k => fderiv ℝ (fun y => (∑ j, fderiv ℝ (fun z => φ z *
    sqrtCoeffAt B z i j) y (basisV j)) * sqrtCoeffAt B y i k) x (basisV k))]
  ring

/-! ### The regularising fields -/

theorem smul_regularizingField (ε w : ℝ) (l : Fin n) (x : EvolutionVec n) :
    w • regularizingField ε l x =
      packPoint 0 0 (fun m => w * (Pi.single l (Real.sqrt ε) : PDE.Vec n) m) := by
  rw [regularizingField, ← packPoint_smul]
  simp [Pi.smul_def]

/-- The divergence of `w Y_l` is `√ε ∂_{z_l} w`. -/
theorem euclideanDivergence_smul_regularizingField {w : EvolutionVec n → ℝ} {x : EvolutionVec n}
    (hw : DifferentiableAt ℝ w x) (ε : ℝ) (l : Fin n) :
    euclideanDivergence (fun y => w y • regularizingField ε l y) x =
      Real.sqrt ε * fderiv ℝ w x (basisZ l) := by

  rw [(funext fun y => smul_regularizingField ε (w y) l y), euclideanDivergence_packPoint (s := fun _ => (0 ))
    (g := fun _ => (0 : PDE.Vec n))
    (h := fun y m => w y * (Pi.single l (Real.sqrt ε) : PDE.Vec n) m)
    (differentiableAt_const _) (fun j => differentiableAt_const _)
    (fun m => hw.mul (differentiableAt_const _))]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, Finset.sum_const_zero,
    zero_add]
  rw [Finset.sum_eq_single l]
  · rw [fderiv_mul_const hw]
    simp
  · intro m _ hm
    simp [hm]
  · simp

variable {ε : ℝ} (hε : 0 ≤ ε)

include hε
/-- The iterated divergence `div(div(φ Y_l) Y_l) = ε ∂_{z_l}² φ`. -/
theorem euclideanDivergence_euclideanDivergence_regularizing
    {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ) (l : Fin n) (x : EvolutionVec n) :
    euclideanDivergence (fun y => euclideanDivergence (fun q => φ q • regularizingField ε l q) y •
        regularizingField ε l y) x =
      ε * fderiv ℝ (fun y => fderiv ℝ φ y (basisZ l)) x (basisZ l) := by
  have hw'  := fun y =>
    euclideanDivergence_smul_regularizingField (differentiableAt_of_contDiff hφ y) ε l
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ φ y (basisZ l)) x :=
    differentiableAt_of_contDiff (contDiff_fderiv_apply hφ _) x

  rw [euclideanDivergence_smul_regularizingField (show DifferentiableAt ℝ (fun y => euclideanDivergence
      (fun q => φ q • regularizingField ε l q) y) x by
      simp only [hw']
      exact hd.const_mul _) ε l]
  simp only [hw']
  rw [fderiv_const_mul hd, smul_apply, smul_eq_mul, ← mul_assoc,
    Real.mul_self_sqrt hε]

/-- **Weak-form bridge for `L_ε`.**  For `ε ≥ 0` and a smooth test function `φ`, the carrier
`hormanderAdjointTest` of `regularizedFields B b ε` (with `c = 0`) is `Lop^* φ + ε Δ_z φ`. -/
theorem hormanderAdjointTest_regularizedFields  (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {φ : EvolutionVec n → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (x : EvolutionVec n) :
    hormanderAdjointTest (regularizedFields B b ε) (fun _ => 0) φ x =
      regularizedAdjoint B b ε φ x := by

  have h0 := hormanderAdjointTest_transportedFields hlam hB hell hb hφ x
  unfold hormanderAdjointTest at h0 ⊢
  simp only [transportedFields, Fin.cons_zero, Fin.cons_succ, zero_mul, add_zero] at h0
  simp only [regularizedFields, Fin.cons_zero, Fin.cons_succ, zero_mul, add_zero,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    euclideanDivergence_euclideanDivergence_regularizing hε hφ]
  unfold regularizedAdjoint
  rw [← h0, add_assoc, ← Finset.mul_sum]

end Identity

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
