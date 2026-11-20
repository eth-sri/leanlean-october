module

public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.VolterraIterateBound

/-! The primitive tower is a single triangular ODE. Conjugating by the
backward shift exponential gives all the positive transport rows at once. -/

@[expose] public section
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set ContinuousLinearMap NormedSpace
open scoped ComplexConjugate
set_option autoImplicit false

local notation "T" => Ell2 →L[ℂ] Ell2
local notation "e₀" => basisVec 0
local notation "e₁" => basisVec 1
local notation "s₂" => (Real.sqrt 2 : ℂ)
local notation "ev" => lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2

@[simp] private theorem coord_add (x y : Ell2) (n : ℕ) : (x + y : Ell2) n = x n + y n :=
  (ev n).map_add x y

@[simp] private theorem coord_sub (x y : Ell2) (n : ℕ) : (x - y : Ell2) n = x n - y n :=
  (ev n).map_sub x y

@[simp] private theorem coord_smul (a : ℂ) (x : Ell2) (n : ℕ) : (a • x : Ell2) n = a * x n :=
  (ev n).map_smul a x

/-- The ordinary forward shift, without the special zeroth weight. -/
def up : T := shiftN - (s₂ - 1) • (ev 0).smulRight e₁

private theorem up_zero (x : Ell2) : up x 0 = 0 := by
  change shiftN x 0 - (s₂ - 1) * (x 0 * e₁ 0) = _
  aesop

private theorem up_succ (x : Ell2) (n : ℕ) : up x (n + 1) = x n := by
  change shiftN x (n + 1) - (s₂ - 1) * (x 0 * e₁ (n + 1)) = _
  cases n <;> simp [shiftWeight, basisVec_coord] <;> ring

private theorem back_up (x : Ell2) : back (up x) = x :=
  lp.ext (funext fun n => by rw [back_coord, up_succ])

private theorem back_e₀ : back e₀ = 0 :=
  lp.ext (funext fun n => by simp [back_coord, basisVec_coord])

/-- One-parameter subgroup of the Banach algebra. -/
def expAlong (B : T) (a : ℂ) : T := exp (a • B)

private theorem expAlong_contDiff (B : T) : ContDiff ℂ 1 (expAlong B) :=
  (show AnalyticOnNhd ℂ (exp : T → T) univ from fun x _ => exp_analytic (𝕂 := ℂ) x).contDiff.comp
    (contDiff_id.smul contDiff_const)

private theorem expAlong_neg (B : T) (a : ℂ) (x : Ell2) :
    expAlong B a (expAlong B (-a) x) = x := by
  have h : expAlong B a * expAlong B (-a) = 1 := by
    letI : NormedAlgebra ℚ T := NormedAlgebra.restrictScalars ℚ ℂ T
    unfold expAlong
    rw [neg_smul, ← exp_add_of_commute (Commute.refl (a • B)).neg_right,
      add_neg_cancel, exp_zero]
  rw [← ContinuousLinearMap.mul_apply, h, ContinuousLinearMap.one_apply]

private theorem hasDerivAt_expAlong_apply {A : ℝ → ℂ} {u : ℝ → Ell2} {t : ℝ}
    {a : ℂ} {v : Ell2} (B : T) (hA : HasDerivAt A a t) (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => expAlong B (A s) (u s))
      (expAlong B (A t) v + a • expAlong B (A t) (B (u t))) t := by
  have hd := ((hasDerivAt_exp_smul_const B (A t)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hA
  have h := ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := Ell2) (F := Ell2)).hasFDerivAt
    (expAlong B (A t), u t)).restrictScalars ℝ
  refine (h.comp_hasDerivAt t (hd.prodMk hu)).congr_deriv ?_
  simp [expAlong, toSpanSingleton_apply, ContinuousLinearMap.mul_apply]

private theorem expAlong_comm (B : T) (a : ℂ) (x : Ell2) :
    B (expAlong B a x) = expAlong B a (B x) := by
  unfold expAlong
  rw [← ContinuousLinearMap.mul_apply, (((Commute.refl B).smul_right a).exp_right).eq,
    ContinuousLinearMap.mul_apply]

section
variable (A a h : ℝ → ℂ)

def towerLoad (t : ℝ) : Ell2 :=
  expAlong up (-A t) (up ((a t * h t) • e₀))

def correction (t : ℝ) : Ell2 :=
  expAlong up (A t) (∫ s in (0 : ℝ)..t, towerLoad A a h s)

def tower (t : ℝ) : Ell2 := h t • e₀ + correction A a h t

variable {A a h} (hA : ∀ t, HasDerivAt A (a t) t) (ha : Continuous a) (hh : Continuous h)
include hA ha hh

private theorem continuous_towerLoad : Continuous (towerLoad A a h) := by
  have hAc := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hc := (expAlong_contDiff up).continuous
  unfold towerLoad
  fun_prop

private theorem hasDerivAt_correction (t : ℝ) :
    HasDerivAt (correction A a h) (a t • up (tower A a h t)) t := by
  have hc := continuous_towerLoad hA ha hh
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter (hc.continuousAt (x := t))
  refine (hasDerivAt_expAlong_apply up (hA t) hd).congr_deriv ?_
  simp  [towerLoad, expAlong_neg, ← expAlong_comm, tower, map_add, map_smul,
    smul_add, smul_smul, correction]

private theorem continuous_tower : Continuous (tower A a h) :=
  (hh.smul continuous_const).add
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_correction hA ha hh t).continuousAt)

private theorem hasDerivAt_back_tower (t : ℝ) :
    HasDerivAt (fun s => back (tower A a h s)) (a t • tower A a h t) t := by
  have h := (back.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_correction hA ha hh t)
  simpa only [tower, map_add, map_smul, back_e₀, smul_zero, zero_add, back_up,
    coe_restrictScalars', Function.comp_def] using h

private theorem correction_zero_coord (t : ℝ) : correction A a h t 0 = 0 := by
  have hd s : HasDerivAt (fun t' => correction A a h t' 0) 0 s := by
    have hd' := ((ev 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_correction hA ha hh s)
    change HasDerivAt (fun t' => correction A a h t' 0)
      ((a s • up (tower A a h s) : Ell2) 0) s at hd'
    simpa only [coord_smul, up_zero, mul_zero] using hd'
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (intervalIntegrable_const (a := (0 : ℝ)) (b := t) (c := (0 : ℂ)))
  simpa [correction] using hi.symm

private theorem tower_coord (n : ℕ) (t : ℝ) : tower A a h t n = volterraPrimitiveIterate a h n t := by
  induction n generalizing t with
  | zero => simp [tower, basisVec_coord, volterraPrimitiveIterate, correction_zero_coord hA ha hh]
  | succ n ih =>
    have hD s : HasDerivAt (fun t' => correction A a h t' (n + 1))
        (a s * volterraPrimitiveIterate a h n s) s := by
      have hd' := ((ev (n + 1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_correction hA ha hh s)
      change HasDerivAt (fun t' => correction A a h t' (n + 1))
        ((a s • up (tower A a h s) : Ell2) (n + 1)) s at hd'
      simpa only [coord_smul, up_succ, ih] using hd'
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hD s)
      ((ha.mul (continuous_volterraPrimitiveIterate ha hh n)).intervalIntegrable 0 t)
    change _ = ∫ s in (0 : ℝ)..t, a s * volterraPrimitiveIterate a h n s
    rw [hi]
    simp [tower, basisVec_coord, correction]
end

local notation "Q" => physicalDrivenQ
local notation "Z" => physicalDrivenCentered

section
variable (γ : ℝ → ℂ) (E : ℝ) (h : ℝ → ℂ)

def primitiveTower : ℝ → Ell2 :=
  tower (fun s => Q E * conj (γ s)) (fun s => Q E * conj (deriv γ s)) h

def vekuaRows (t : ℝ) : Ell2 :=
  expAlong back (Q E * Z γ t) (primitiveTower γ E h t)

/-- The genuine Vekua transport vector, computed by the shift exponential. -/
def vekuaTowerVector (t : ℝ) : Ell2 :=
  (s₂⁻¹ * vekuaRows γ E h t 0) • e₀ + up (back (vekuaRows γ E h t))

/-- The projection to the positive rows. -/
def vekuaPositivePart (x : Ell2) : Ell2 := x - x 0 • e₀

@[simp] theorem vekuaTowerVector_zero_coord (t : ℝ) :
    vekuaTowerVector γ E h t 0 = vekuaRows γ E h t 0 / s₂ := by
  simp [vekuaTowerVector, up_zero, basisVec_coord, div_eq_mul_inv, mul_comm]

@[simp] theorem vekuaTowerVector_succ_coord (t : ℝ) (n : ℕ) :
    vekuaTowerVector γ E h t (n + 1) = vekuaRows γ E h t (n + 1) := by
  simp [vekuaTowerVector, up_succ, back_coord, basisVec_coord]

theorem vekuaTowerVector_origin : vekuaTowerVector γ E h 0 = (h 0 / s₂) • e₀ := by
  have hr : vekuaRows γ E h 0 = h 0 • e₀ := by
    simp [vekuaRows, expAlong, physicalDrivenCentered, primitiveTower, tower, correction]
  simp [vekuaTowerVector, hr, back_e₀, basisVec_coord, div_eq_mul_inv, mul_comm]

variable {γ E h} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h)
include hγ hh

omit hh in
private theorem hasDerivAt_antiparam (t : ℝ) :
    HasDerivAt (fun s => Q E * conj (γ s)) (Q E * conj (deriv γ t)) t :=
  (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hγ.differentiable_one t).hasDerivAt).const_mul _

omit hh in
private theorem continuous_antivelocity : Continuous (fun s => Q E * conj (deriv γ s)) :=
  continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)

private theorem continuous_vekuaRows : Continuous (vekuaRows γ E h) := by
  have hc := (expAlong_contDiff back).continuous
  have ht := continuous_tower (hasDerivAt_antiparam (E := E) hγ) (continuous_antivelocity (E := E) hγ) hh
  have hgc := hγ.continuous
  unfold vekuaRows primitiveTower physicalDrivenCentered
  fun_prop

/-- Only the zeroth input row needs a derivative for the full transport equation. -/
theorem continuous_vekuaTowerVector : Continuous (vekuaTowerVector γ E h) := by
  have hc := continuous_vekuaRows (E := E) hγ hh
  unfold vekuaTowerVector
  change Continuous (fun t => (s₂⁻¹ * ev 0 (vekuaRows γ E h t)) • e₀ + up (back (vekuaRows γ E h t)))
  fun_prop

omit hγ hh in
private theorem positivePart_vekuaRows (t : ℝ) :
    vekuaPositivePart (vekuaTowerVector γ E h t) = up (back (vekuaRows γ E h t)) := by
  rw [vekuaPositivePart, vekuaTowerVector_zero_coord, vekuaTowerVector, div_eq_mul_inv, mul_comm _ s₂⁻¹]
  abel

omit hγ hh in
private theorem rowD_vekuaTowerVector (t : ℝ) : rowD (vekuaTowerVector γ E h t) = vekuaRows γ E h t := by
  apply lp.ext; funext n
  rw [rowD_coord]
  cases n with
  | zero => simp_all [shiftWeight, mul_div_cancel₀]
  | succ n => simp [shiftWeight]

/-- Vanishing of all transport rows implies vanishing of the original input. -/
theorem vekuaTowerVector_eq_zero_imp (t : ℝ) (hz : vekuaTowerVector γ E h t = 0) : h t = 0 := by
  have hr : vekuaRows γ E h t = 0 := by rw [← rowD_vekuaTowerVector, hz, map_zero]
  have hk : primitiveTower γ E h t = 0 := by
    have he := expAlong_neg back (-(Q E * Z γ t)) (primitiveTower γ E h t)
    rw [neg_neg, ← vekuaRows, hr, map_zero] at he
    gcongr
  have h0 := tower_coord (hasDerivAt_antiparam (E := E) hγ)
    (continuous_antivelocity (E := E) hγ) hh 0 t
  change primitiveTower γ E h t 0 = h t at h0
  simp_all

omit hγ hh in
private theorem up_back_eq (x : Ell2) : up (back x) = vekuaPositivePart x := by
  apply lp.ext; funext n
  cases n <;> simp [vekuaPositivePart, up_zero, up_succ, back_coord, basisVec_coord]

omit hγ hh in
private theorem back_transport (γ : ℝ → ℂ) (E t : ℝ) (x : Ell2) :
    back (transportCoeff γ E t x) =
      (Q E * deriv γ t) • back (back (rowD x)) + (Q E * conj (deriv γ t)) • rowD x := by
  have he (y : Ell2) : back y = back (rowD y) := lp.ext (funext fun n => by
    rw [back_coord, back_coord, rowD_coord]; simp [shiftWeight])
  change back (Q E • (deriv γ t • ContinuousLinearMap.adjoint shiftN x +
    conj (deriv γ t) • shiftN x)) = _
  rw [map_smul, map_add, map_smul, map_smul, ← shiftNAdj_eq_adjoint,
    he (shiftNAdj x), rowD_shiftAdj, map_add, map_smul, back_e₀, smul_zero, add_zero,
    he (shiftN x), back_rowD_shift, smul_add, smul_smul, smul_smul]

/-- The positive rows of the gauged primitive tower satisfy the homogeneous transport equation. -/
theorem hasDerivAt_vekuaTower_positive (t : ℝ) :
    HasDerivAt (fun s => vekuaPositivePart (vekuaTowerVector γ E h s))
      (vekuaPositivePart (transportCoeff γ E t (vekuaTowerVector γ E h t))) t := by
  have hB : HasDerivAt (fun s => Q E * Z γ s) (Q E * deriv γ t) t :=
    ((hγ.differentiable_one t).hasDerivAt.sub_const _).const_mul _
  have hX := hasDerivAt_back_tower (hasDerivAt_antiparam (E := E) hγ)
    (continuous_antivelocity (E := E) hγ) hh t
  have hV := hasDerivAt_expAlong_apply back hB hX
  have hfunc : (fun s => expAlong back (Q E * Z γ s) (back (primitiveTower γ E h s))) =
      fun s => back (vekuaRows γ E h s) := funext fun s => (expAlong_comm _ _ _).symm
  change HasDerivAt (fun s => expAlong back (Q E * Z γ s) (back (primitiveTower γ E h s))) _ t at hV
  rw [hfunc] at hV
  have hu := (up.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hV
  simp  [positivePart_vekuaRows]
  refine hu.congr_deriv ?_
  change up (expAlong back (Q E * Z γ t) ((Q E * conj (deriv γ t)) • primitiveTower γ E h t) +
    (Q E * deriv γ t) • expAlong back (Q E * Z γ t) (back (back (primitiveTower γ E h t)))) = _
  rw [map_smul, ← expAlong_comm, ← expAlong_comm, ← vekuaRows, add_comm,
    ← rowD_vekuaTowerVector, ← back_transport, up_back_eq]

/-- The primitive ODE is also the inverse of the gauge on a driven solution. -/
theorem vekuaTowerVector_eq_driven {K : NNReal} (hK : LipschitzWith K γ)
    {W : ℝ → T} (hW : IsTransport γ E W) (g : ℝ → ℂ)
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hz : EqOn h (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) (Icc 0 (2 * Real.pi))) :
    EqOn (vekuaTowerVector γ E h) (physicalDrivenVector W g) (Icc 0 (2 * Real.pi)) := by
  let P := primitiveTower γ E h
  let y := physicalDrivenVector W g
  let G := fun t => gaugeOp γ E t (rowD (y t))
  let a := fun t => Q E * conj (deriv γ t)
  have hA := hasDerivAt_antiparam (E := E) hγ
  have ha := continuous_antivelocity (E := E) hγ
  have hp := continuous_tower hA ha hh
  have hgC : ContinuousOn G (Icc 0 (2 * Real.pi)) := by
    rw [← uIcc_of_le Real.two_pi_pos.le]
    exact (gaugeVector_absolutelyContinuous hγ
      (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg) E).continuousOn
  have hP (t : ℝ) : back (P t) = ∫ s in (0 : ℝ)..t, a s • P s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_back_tower hA ha hh s) ((ha.smul hp).intervalIntegrable 0 t)
    change (∫ s in (0 : ℝ)..t, a s • P s) = back (P t) - back (P 0) at h
    have h0 : back (P 0) = 0 := by simp [P, primitiveTower, tower, correction, back_e₀]
    simp_all
  have hc (n : ℕ) : ∀ t ∈ Icc 0 (2 * Real.pi), P t n = G t n := by
    induction n with
    | zero =>
      intro t ht
      have h : P t 0 = h t := tower_coord hA ha hh 0 t
      exact h.trans (by simpa [physicalDrivenGauge] using hz ht)
    | succ n ih =>
      intro t ht
      rw [← back_coord (P t) n, ← back_coord (G t) n, hP]
      have hgi :=
        physicalDrivenBackGauge_eq_integral hK hγ hW g hg ht
      rw [hgi]
      change ev n (∫ s in (0 : ℝ)..t, a s • P s) = ev n (∫ s in (0 : ℝ)..t, a s • G s)
      have hpI : IntervalIntegrable (fun s => a s • P s) volume 0 t := (ha.smul hp).intervalIntegrable 0 t
      have hgI : IntervalIntegrable (fun s => a s • G s) volume 0 t :=
        (ha.continuousOn.smul (hgC.mono (Icc_subset_Icc_right ht.2))).intervalIntegrable_of_Icc ht.1
      rw [← (ev n).intervalIntegral_comp_comm hpI, ← (ev n).intervalIntegral_comp_comm hgI]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      simp only 
      exact congrArg (a s • ·) (ih s (Icc_subset_Icc_right ht.2 hs))
  intro t ht
  have he := lp.ext (funext fun n => hc n t ht)
  have hG : G t = expAlong back (-(Q E * Z γ t)) (rowD (y t)) := by
    simp [G, gaugeOp, expAlong, mul_comm]
  have hr : vekuaRows γ E h t = rowD (y t) := by
    unfold vekuaRows
    change expAlong back (Q E * Z γ t) (P t) = _
    rw [he, hG, expAlong_neg]
  apply lp.ext; funext n
  have h := congrArg (fun x : Ell2 => x n) ((rowD_vekuaTowerVector t).trans hr)
  simp only [rowD_coord] at h
  exact mul_left_cancel₀ (by cases n <;> simp [shiftWeight]) h

omit hγ hh in
private theorem volterraPrimitiveIterate_scale (q : ℂ) (a h : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    volterraPrimitiveIterate (fun t => q * a t) h n t = q ^ n * volterraPrimitiveIterate a h n t := by
  induction n generalizing t with
  | zero => aesop
  | succ n ih =>
    simp only [volterraPrimitiveIterate, ih]
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ring

/-- Entrywise expansion of the operator exponential. -/
theorem vekuaRows_hasSum (t : ℝ) (n : ℕ) :
    HasSum (fun j : ℕ => Q E ^ n *
      ((Q E ^ 2) ^ j / (j.factorial : ℂ) * Z γ t ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + n) t))
      (vekuaRows γ E h t n) := by
  have hs := exp_back_hasSum (Q E * Z γ t) (primitiveTower γ E h t) n
  change HasSum _ (vekuaRows γ E h t n) at hs
  convert hs using 1
  funext j
  rw [primitiveTower, tower_coord (hasDerivAt_antiparam (E := E) hγ)
    (continuous_antivelocity (E := E) hγ) hh, volterraPrimitiveIterate_scale,
    mul_pow, pow_add, ← pow_mul, mul_comm 2 j, pow_mul]
  ring

end
end PolyaNeumann
end
