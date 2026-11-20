module

public import RequestProject.PhysicalDrivenODE
public import RequestProject.CircleFourier
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set ContinuousLinearMap NormedSpace Filter AbsolutelyContinuousOnInterval
open scoped ComplexConjugate

local notation "s₂" => (Real.sqrt 2 : ℂ)
local notation "e₀" => basisVec 0
local notation "Q" => physicalDrivenQ
local notation "T" => Ell2 →L[ℂ] Ell2
local notation "ev" => lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2

/-- Normalize the exceptional zeroth row before applying the factorial gauge. -/
def rowD : T := 1 + (s₂ - 1) • (ev 0).smulRight e₀

def back : T := shiftNAdj - (s₂ - 1) • (ev 1).smulRight e₀

theorem rowD_coord (x : Ell2) (j : ℕ) :
    (rowD x : ℕ → ℂ) j = shiftWeight j * x j := by
  change x j + ((s₂ - 1) * (x 0 * (e₀ : ℕ → ℂ) j)) = _
  by_cases hj : j = 0
  grind [shiftWeight, basisVec_coord]
  simp_all [shiftWeight, basisVec_coord]

theorem back_coord (x : Ell2) (j : ℕ) :
    (back x : ℕ → ℂ) j = x (j + 1) := by
  change (shiftNAdj x : ℕ → ℂ) j - ((s₂ - 1) * (x 1 * (e₀ : ℕ → ℂ) j)) = _
  rw [shiftNAdj_apply]
  by_cases hj : j = 0
  grind [shiftWeight, basisVec_coord]
  simp_all [shiftWeight, basisVec_coord]

private theorem back_pow_apply (x : Ell2) (n j : ℕ) :
    ((back ^ n) x : ℕ → ℂ) j = x (n + j) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, back_coord, ih, Nat.succ_add, Nat.add_succ]

private theorem rowD_e₀ : rowD e₀ = s₂ • e₀ := by
  apply lp.ext; funext j
  simp only [rowD_coord, lp.coeFn_smul, smul_eq_mul]
  by_cases hj : j = 0 <;> simp [hj, shiftWeight, basisVec_coord]

theorem rowD_shiftAdj (x : Ell2) : rowD (shiftNAdj x) = back (rowD x) + x 1 • e₀ := by
  apply lp.ext; funext j
  simp only [rowD_coord, back_coord, shiftNAdj_apply, lp.coeFn_add, Pi.add_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, shiftWeight_mul_self]
  grind [shiftWeight, basisVec_coord, two_mul]

theorem back_rowD_shift (x : Ell2) : back (rowD (shiftN x)) = rowD x := by
  apply lp.ext; funext j
  simp [back_coord, rowD_coord, shiftWeight]

/-- The factorial transform is the exponential of the ordinary backward shift. -/
def gaugeOp (γ : ℝ → ℂ) (E θ : ℝ) : T :=
  exp ((-physicalDrivenCentered γ θ * Q E) • back)

private theorem gaugeOp_comm (γ : ℝ → ℂ) (E θ : ℝ) : Commute back (gaugeOp γ E θ) :=
  ((Commute.refl back).smul_right _).exp_right

private theorem gaugeOp_e₀ (γ : ℝ → ℂ) (E θ : ℝ) : gaugeOp γ E θ e₀ = e₀ := by
  have h := (exp_series_hasSum_exp' (𝕂 := ℂ) ((-physicalDrivenCentered γ θ * Q E) • back)).mapL
    (ContinuousLinearMap.apply ℂ Ell2 e₀)
  simp only [ContinuousLinearMap.apply_apply] at h
  unfold gaugeOp
  rw [← h.tsum_eq, tsum_eq_single 0]
  · simp
  · intro n hn
    have hz : (back ^ n) e₀ = 0 := by
      apply lp.ext; funext j
      rw [back_pow_apply]
      simp only [basisVec_coord, if_neg (show n + j ≠ 0 by omega), lp.coeFn_zero, Pi.zero_apply]
    rw [smul_pow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hz, smul_zero, smul_zero]

/-- The scaled coordinates after applying the exponential of the backward shift. -/
def physicalDrivenGauge (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (j : ℕ) (θ : ℝ) : ℂ :=
  Q E ^ j * (gaugeOp γ E θ (rowD (y θ)) : ℕ → ℂ) j

theorem exp_back_hasSum (a : ℂ) (x : Ell2) (k : ℕ) :
    HasSum (fun j : ℕ => a ^ j / (j.factorial : ℂ) * x (j + k))
      (ev k (exp (a • back) x)) := by
  have h := (exp_series_hasSum_exp' (𝕂 := ℂ) (a • back)).mapL
    ((ev k).comp (ContinuousLinearMap.apply ℂ Ell2 x))
  convert h using 1 <;> try rfl
  funext j
  simp only [ContinuousLinearMap.apply_apply, smul_pow,
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, div_eq_mul_inv]
  change _ = (j.factorial : ℂ)⁻¹ * (a ^ j * ((back ^ j) x : ℕ → ℂ) k)
  rw [back_pow_apply]
  ring



theorem physicalDrivenGauge_continuousOn (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    (y : ℝ → Ell2) (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) (j : ℕ) :
    ContinuousOn (physicalDrivenGauge γ E y j) (Icc 0 (2 * Real.pi)) := by
  have hexp : Continuous (exp : T → T) :=
    continuous_iff_continuousAt.mpr fun x => (exp_analytic (𝕂 := ℂ) x).continuousAt
  have hA : Continuous (gaugeOp γ E) := hexp.comp (by unfold physicalDrivenCentered; fun_prop)
  exact continuousOn_const.mul ((ev j).continuous.comp_continuousOn
    (hA.continuousOn.clm_apply (rowD.continuous.comp_continuousOn hy)))

private theorem gaugeOp_smooth {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) :
    ContDiff ℝ 1 (gaugeOp γ E) := by
  have he : ContDiff ℂ 1 (exp : T → T) :=
    (show AnalyticOnNhd ℂ (exp : T → T) univ from fun x _ => exp_analytic (𝕂 := ℂ) x).contDiff
  unfold gaugeOp physicalDrivenCentered
  exact (he.restrict_scalars ℝ).comp (by fun_prop)

theorem gaugeVector_absolutelyContinuous {γ : ℝ → ℂ} {y : ℝ → Ell2} {a b : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hy : AbsolutelyContinuousOnInterval y a b) (E : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => gaugeOp γ E t (rowD (y t))) a b :=
  absolutelyContinuousOnInterval_clm_apply (gaugeOp_smooth hγ E).contDiffOn.absolutelyContinuousOnInterval
    (rowD.lipschitz.comp_absolutelyContinuousOnInterval hy)

theorem physicalDrivenGauge_absolutelyContinuous {γ : ℝ → ℂ} {y : ℝ → Ell2} {a b : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hy : AbsolutelyContinuousOnInterval y a b) (E : ℝ) (j : ℕ) :
    AbsolutelyContinuousOnInterval (physicalDrivenGauge γ E y j) a b :=
  ((ev j).lipschitz.comp_absolutelyContinuousOnInterval (gaugeVector_absolutelyContinuous hγ hy E)).const_smul (Q E ^ j)


/-- At a vector in the zeroth coordinate, the gauge is just row normalization. -/
theorem physicalDrivenGauge_of_eq_smul_basisVec_zero (γ : ℝ → ℂ) (E : ℝ) {y : ℝ → Ell2}
    {θ : ℝ} {a : ℂ} (hy : y θ = a • e₀) (j : ℕ) :
    physicalDrivenGauge γ E y j θ = if j = 0 then s₂ * a else 0 := by
  simp only [physicalDrivenGauge, hy, map_smul, rowD_e₀, gaugeOp_e₀, lp.coeFn_smul,
    Pi.smul_apply, basisVec_coord]
  cases j <;> simp <;> ring

/-- The backward-shift part cancels on differentiating the exponential gauge.
The input may include a rough zeroth row, while the differentiated correction is AC. -/
private theorem hasDerivAt_gaugeVector {γ : ℝ → ℂ} {y : ℝ → Ell2} {E θ : ℝ} {a b : ℂ}
    (hγ : DifferentiableAt ℝ γ θ)
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ + a • e₀) + b • e₀) θ) :
    HasDerivAt (fun t => gaugeOp γ E t (rowD (y t)))
      ((Q E * deriv γ θ * y θ 1 + s₂ * b) • e₀ +
        (Q E * conj (deriv γ θ)) • gaugeOp γ E θ (rowD (shiftN (y θ + a • e₀)))) θ := by
  have ht : HasDerivAt (fun t => -physicalDrivenCentered γ t * Q E) (-deriv γ θ * Q E) θ :=
    ((hγ.hasDerivAt.sub_const _).neg.mul_const _)
  have hd := ((hasDerivAt_exp_smul_const back (-physicalDrivenCentered γ θ * Q E)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt θ ht
  have hD := (rowD.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ hy
  have h := ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := Ell2) (F := Ell2)).hasFDerivAt
    (gaugeOp γ E θ, rowD (y θ))).restrictScalars ℝ
  have h := h.comp_hasDerivAt θ (hd.prodMk hD)
  change HasDerivAt (fun t => gaugeOp γ E t (rowD (y t))) _ θ at h
  refine h.congr_deriv ?_
  simp only [coe_restrictScalars', IsBoundedBilinearMap.deriv_apply, toSpanSingleton_apply,
    ContinuousLinearMap.smul_apply, gaugeOp]
  rw [add_comm]
  change (-deriv γ θ * Q E) • gaugeOp γ E θ (back (rowD (y θ))) +
    gaugeOp γ E θ (rowD (transportCoeff γ E θ (y θ + a • e₀) + b • e₀)) = _
  have hz : back e₀ = 0 := by
    apply lp.ext; funext j; simp [back_coord, basisVec_coord]
  have h1 : (y θ + a • e₀ : Ell2) 1 = y θ 1 := by
    simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply,
      basisVec_coord, Nat.one_ne_zero, if_false, smul_zero, add_zero]
  have h2 : back (rowD (y θ + a • e₀)) = back (rowD (y θ)) := by
    simp [map_add, map_smul, rowD_e₀, hz]
  let v := y θ + a • e₀
  have hc : rowD (transportCoeff γ E θ v) =
      Q E • (deriv γ θ • (back (rowD (y θ)) + y θ 1 • e₀) +
        conj (deriv γ θ) • rowD (shiftN v)) := by
    unfold transportCoeff
    rw [← shiftNAdj_eq_adjoint]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
    rw [map_smul, map_add, map_smul, map_smul, rowD_shiftAdj]
    change _ = _
    rw [show back (rowD v) = _ from h2, show v 1 = _ from h1]
    rfl
  let A := gaugeOp γ E θ
  have he : A e₀ = e₀ := gaugeOp_e₀ γ E θ
  change (-deriv γ θ * Q E) • A (back (rowD (y θ))) +
    A (rowD (transportCoeff γ E θ v + b • e₀)) =
      (Q E * deriv γ θ * y θ 1 + s₂ * b) • e₀ +
        (Q E * conj (deriv γ θ)) • A (rowD (shiftN v))
  rw [map_add, hc, map_smul, rowD_e₀]
  simp only [map_add, map_smul, he]
  module

/-- Removing the zeroth coordinate gives the triangular primitive equation. -/
theorem hasDerivAt_back_gauge {γ : ℝ → ℂ} {y : ℝ → Ell2} {E θ : ℝ} {a b : ℂ}
    (hγ : DifferentiableAt ℝ γ θ)
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ + a • e₀) + b • e₀) θ) :
    HasDerivAt (fun t => back (gaugeOp γ E t (rowD (y t))))
      ((Q E * conj (deriv γ θ)) • gaugeOp γ E θ (rowD (y θ + a • e₀))) θ := by
  refine ((back.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_gaugeVector hγ hy)).congr_deriv ?_
  change back (_ + _) = _
  have hz : back e₀ = 0 := lp.ext (funext fun j => by simp [back_coord, basisVec_coord])
  rw [map_add, map_smul, map_smul, hz, smul_zero, zero_add, ← ContinuousLinearMap.mul_apply,
    (gaugeOp_comm γ E θ).eq, ContinuousLinearMap.mul_apply, back_rowD_shift]

/-- In the positive rows, the gauge equation lowers the row by one. -/
theorem hasDerivAt_physicalDrivenGauge_succ {γ : ℝ → ℂ} {y : ℝ → Ell2} {E θ : ℝ} {a b : ℂ}
    (hγ : DifferentiableAt ℝ γ θ)
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ + a • e₀) + b • e₀) θ) (j : ℕ) :
    HasDerivAt (physicalDrivenGauge γ E y (j + 1))
      (Q E ^ 2 * conj (deriv γ θ) * physicalDrivenGauge γ E (fun t => y t + a • e₀) j θ) θ := by
  have he := ((ev j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_back_gauge hγ hy)
  change HasDerivAt (fun t => (back (gaugeOp γ E t (rowD (y t)))) j)
    (((Q E * conj (deriv γ θ)) • gaugeOp γ E θ (rowD (y θ + a • e₀)) : Ell2) j) θ at he
  simp only [back_coord, lp.coeFn_smul, Pi.smul_apply] at he
  unfold physicalDrivenGauge
  refine (he.const_mul (Q E ^ (j + 1))).congr_deriv ?_
  rw [pow_succ]
  ring


/-- The positive gauge rows ignore any contribution in the zeroth slot. -/
theorem physicalDrivenGauge_add_basisVec_zero (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (a : ℝ → ℂ) (j : ℕ) (θ : ℝ) :
    physicalDrivenGauge γ E (fun t => y t + a t • e₀) j θ =
      physicalDrivenGauge γ E y j θ + if j = 0 then s₂ * a θ else 0 := by
  simp only [physicalDrivenGauge, map_add, map_smul, rowD_e₀, gaugeOp_e₀,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, basisVec_coord]
  by_cases h : j = 0 <;> simp [h] <;> ring

/-- The continuous part of the zeroth-row equation and the coefficient of
an additional, possibly rough, zeroth row. -/
def physicalDrivenGaugeZeroContinuousPart (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (θ : ℝ) : ℂ :=
  Q E * deriv γ θ * y θ 1 + (Q E * conj (deriv γ θ)) *
    (gaugeOp γ E θ (rowD (shiftN (y θ))) : ℕ → ℂ) 0

def physicalDrivenGaugeZeroCoeff (γ : ℝ → ℂ) (E : ℝ) (θ : ℝ) : ℂ :=
  (Q E * conj (deriv γ θ)) * (gaugeOp γ E θ (rowD (shiftN e₀)) : ℕ → ℂ) 0

theorem physicalDrivenGaugeZeroContinuousPart_continuousOn {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (E : ℝ) (y : ℝ → Ell2) {s : Set ℝ} (hy : ContinuousOn y s) :
    ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E y) s := by
  have h₀ := (gaugeOp_smooth hγ E).continuous
  have hd := hγ.continuous_deriv_one
  have h₁ :=
    h₀.continuousOn.clm_apply (rowD.continuous.comp_continuousOn (shiftN.continuous.comp_continuousOn hy))
  change ContinuousOn (fun θ => Q E * deriv γ θ * ev 1 (y θ) +
    (Q E * conj (deriv γ θ)) * ev 0 (gaugeOp γ E θ (rowD (shiftN (y θ))))) s
  fun_prop

theorem physicalDrivenGaugeZeroCoeff_continuous {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) :
    Continuous (physicalDrivenGaugeZeroCoeff γ E) := by
  have h₀ := (gaugeOp_smooth hγ E).continuous
  have hd := hγ.continuous_deriv_one
  change Continuous (fun θ => (Q E * conj (deriv γ θ)) * ev 0 (gaugeOp γ E θ (rowD (shiftN e₀))))
  fun_prop

theorem hasDerivAt_physicalDrivenGauge_zero {γ : ℝ → ℂ} {y : ℝ → Ell2} {E θ : ℝ} {a b : ℂ}
    (hγ : DifferentiableAt ℝ γ θ)
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ + a • e₀) + b • e₀) θ) :
    HasDerivAt (physicalDrivenGauge γ E y 0)
      (physicalDrivenGaugeZeroContinuousPart γ E y θ +
        physicalDrivenGaugeZeroCoeff γ E θ * a + s₂ * b) θ := by
  have he := ((ev 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_gaugeVector hγ hy)
  unfold physicalDrivenGauge
  simp only [pow_zero, one_mul]
  refine he.congr_deriv ?_
  change (((Q E * deriv γ θ * y θ 1 + s₂ * b) • e₀ +
    (Q E * conj (deriv γ θ)) • gaugeOp γ E θ (rowD (shiftN (y θ + a • e₀)))) : ℕ → ℂ) 0 = _
  simp only [physicalDrivenGaugeZeroContinuousPart, physicalDrivenGaugeZeroCoeff,
    map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_coord, if_true, mul_one]
  ring

theorem physicalDrivenGauge_eq_zero_of_vector_eq_zero
    (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (j : ℕ) {θ : ℝ} (hy : y θ = 0) :
    physicalDrivenGauge γ E y j θ = 0 := by simp [physicalDrivenGauge, hy]

theorem physicalDrivenGauge_actual_endpoints
     (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ)
    (hO : observationAdj W g = 0) (j : ℕ) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j 0 = 0 ∧
      physicalDrivenGauge γ E (physicalDrivenVector W g) j (2 * Real.pi) = 0 :=
  ⟨physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_zero W g),
    physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_endpoint W g hO)⟩

def physicalDrivenMoment (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (j m : ℕ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) *
    physicalDrivenGauge γ E y j θ * conj (physicalDrivenCentered γ θ) ^ m

section

variable (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ)
include γ E W g

/-- The genuine periodic representative of the actual driven gauge on the
closed parameter interval.  Continuity follows from the proved zero endpoints. -/
def physicalDrivenPeriodicGauge  (j : ℕ) (θ : ℝ) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) j)
      (θ : AddCircle (2 * Real.pi))


theorem physicalDrivenPeriodicGauge_eqOn  (hO : observationAdj W g = 0) (j : ℕ) :
    EqOn (physicalDrivenPeriodicGauge γ E W g j)
      (physicalDrivenGauge γ E (physicalDrivenVector W g) j) (Icc 0 (2 * Real.pi)) := by
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  exact liftIco_zero_eqOn_Icc (h0.trans hL.symm)

end

end PolyaNeumann

end
