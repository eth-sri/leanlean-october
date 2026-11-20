module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.ScalarCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.ScalarSlices
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Profile

/-! # The elementary scalar supersolution on the punctured kinetic plane -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
open Filter MeasureTheory Real Set
open scoped Topology ContDiff MatrixOrder

variable {α : ℝ} (m : Model α)

/-- Reflect both variables at once on the negative position half-plane. -/
def lift (q : XV 1) :=
  if 0 < q.1 0 then chart α m.f (q.1 0) (q.2 0)
  else if q.1 0 < 0 then chart α m.f (-q.1 0) (-q.2 0)
  else |q.2 0| ^ α

private theorem scale_mul {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    scale (r^3*x) = r * scale x := by
  rw [scale, mul_rpow (by positivity) hx.le, ← rpow_natCast r 3, ← rpow_mul hr.le]
  norm_num [scale]

private theorem chart_mul (v : ℝ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    chart α m.f (r^3*x) (r*v) = r^α * chart α m.f x v := by
  rw [chart, chart, scale_mul hr hx, mul_rpow hr.le (scale_pos hx).le,
    mul_div_mul_left _ _ hr.ne', mul_assoc]

private theorem lift_homogeneous (r : ℝ) (hr : 0 < r) (q : XV 1) :
    lift m (dilate r q) = r^α * lift m q := by
  have hn : r^3 * q.1 0 < 0 ↔ q.1 0 < 0 := by simpa using (mul_lt_mul_iff_right₀ (pow_pos hr 3) (b := q.1 0) (c := 0))
  simp only [lift, dilate, Pi.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left (pow_pos hr 3),
    hn]
  split_ifs with h h
  · exact chart_mul m _ hr h
  · rw [← mul_neg, ← mul_neg]; exact chart_mul m _ hr (neg_pos.mpr h)
  · rw [abs_mul, abs_of_pos hr, mul_rpow hr.le (abs_nonneg _)]

private theorem chart_power {x : ℝ} (v : ℝ) (hx : 0 < x) (h : m.width * scale x < |v|) :
    chart α m.f x v = |v| ^ α := by
  have hr := scale_pos hx
  unfold chart
  rw [m.power _ (by rwa [abs_div, abs_of_pos hr, lt_div_iff₀ hr]), abs_div, abs_of_pos hr,
    div_rpow (abs_nonneg _) hr.le, mul_div_cancel₀ _ (rpow_pos_of_pos hr _).ne']

private theorem lift_axis {q : XV 1} (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
    lift m =ᶠ[𝓝 q] fun z => |z.2 0|^α := by
  have hc : Continuous (fun z : XV 1 => m.width * scale |z.1 0|) := continuous_const.mul
    ((continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/3)).comp (by fun_prop))
  have hv' : Continuous (fun z : XV 1 => |z.2 0|) := by fun_prop
  filter_upwards [hc.continuousAt.eventually_lt hv'.continuousAt
    (by simpa [scale,hx,zero_rpow (by norm_num : (1/3:ℝ) ≠ 0)] using abs_pos.mpr hv)] with z hz
  unfold lift
  split_ifs with h h
  · exact chart_power m _ h (by simpa only [abs_of_pos h] using hz)
  · simpa only [abs_neg] using chart_power m (-z.2 0) (neg_pos.mpr h)
      (by simpa only [abs_neg,abs_of_neg h] using hz)
  · rfl

private theorem lift_smooth {q : XV 1} (hq : q ≠ 0) : ContDiffAt ℝ ∞ (lift m) q := by
  have hx : ContDiff ℝ ∞ (fun z : XV 1 => z.1 0) := by fun_prop
  have hv : ContDiff ℝ ∞ (fun z : XV 1 => z.2 0) := by fun_prop
  have hchart {x v : XV 1 → ℝ} (hs : ContDiffAt ℝ ∞ x q) (h : 0 < x q) (ht : ContDiffAt ℝ ∞ v q) :
      ContDiffAt ℝ ∞ (fun z => chart α m.f (x z) (v z)) q := by
    have hscale : ContDiffAt ℝ ∞ (fun z => scale (x z)) q := hs.rpow_const_of_ne h.ne'
    exact (hscale.rpow_const_of_ne (scale_pos h).ne').mul
      (m.smooth.contDiffAt.comp q (ht.div hscale (scale_pos h).ne'))
  rcases lt_trichotomy (q.1 0) 0 with h | h | h
  · apply (hchart hx.contDiffAt.neg (neg_pos.mpr h) hv.contDiffAt.neg).congr_of_eventuallyEq
    filter_upwards [hx.continuous.continuousAt.eventually_lt_const h] with z hz
    simp [lift,hz,hz.not_gt]
  · have hv0 : q.2 0 ≠ 0 := fun e => hq (Prod.ext
      (by ext i; change q.1 i = 0; simpa only [Subsingleton.elim i 0] using h)
      (by ext i; change q.2 i = 0; simpa only [Subsingleton.elim i 0] using e))
    exact ((hv.contDiffAt.abs hv0).rpow_const_of_ne (abs_ne_zero.mpr hv0)).congr_of_eventuallyEq
      (lift_axis m h hv0)
  · apply (hchart hx.contDiffAt h hv.contDiffAt).congr_of_eventuallyEq
    filter_upwards [hx.continuous.continuousAt.eventually_const_lt h] with z hz
    simp [lift,hz]

private def diffusion (q : XV 1) :=
  if 0 < q.1 0 then m.a (q.2 0 / scale (q.1 0)) else m.a (-q.2 0 / scale (-q.1 0))

private theorem scalar_super {q : XV 1} (hx : q.1 0 ≠ 0) :
    diffusion m q * dvv (lift m) q 0 0 ≤ q.2 0 * dx (lift m) q 0 := by
  have hq : q ≠ 0 := fun e => hx (e ▸ rfl)
  have hs := lift_smooth m hq
  rw [dx_eq_scalar_slice _ _ (hs.differentiableAt (by simp)),
    dvv_eq_scalar_slice _ _ (hs.of_le (by simp))]
  have bound (x v : ℝ) (hx : 0 < x) : m.a (v/scale x) * deriv (deriv (chart α m.f x)) v ≤
      v * deriv (fun y => chart α m.f y v) x := by
    rw [chart_transport _ m.smooth hx, chart_deriv2 m.smooth, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (m.super _) (div_nonneg (rpow_pos_of_pos (scale_pos hx) _).le (sq_nonneg _))
  rcases hx.lt_or_gt with h | h
  · have e : (fun x => lift m (scalarPositionSlice q x)) =ᶠ[𝓝 (q.1 0)] fun x => chart α m.f (-x) (-q.2 0) :=
      (gt_mem_nhds h).mono fun x hx => by simp [lift,scalarPositionSlice,hx,hx.not_gt]
    simp only [diffusion, lift, scalarVelocitySlice, h, h.not_gt, ↓reduceIte] at e ⊢
    rw [e.deriv_eq, deriv_comp_neg (fun x => chart α m.f x (-q.2 0))]
    have hh (f : ℝ → ℝ) (a : ℝ) : deriv (deriv (fun z => f (-z))) a = deriv (deriv f) (-a) := by
      have e : deriv (fun z => f (-z)) = -(fun z => deriv f (-z)) := funext (deriv_comp_neg f)
      rw [e, deriv.neg, deriv_comp_neg, neg_neg]
    rw [hh, mul_neg, ← neg_mul]
    exact bound _ _ (neg_pos.mpr h)
  · have e : (fun x => lift m (scalarPositionSlice q x)) =ᶠ[𝓝 (q.1 0)] fun x => chart α m.f x (q.2 0) :=
      (lt_mem_nhds h).mono fun x hx => by simp [lift,scalarPositionSlice,hx]
    rw [e.deriv_eq]
    simpa only [diffusion,lift,scalarVelocitySlice,h,↓reduceIte] using bound _ _ h

/-- The scalar angular supersolution transported to the native kinetic coordinates. -/
theorem Model.profile (m : Model α) : Nonempty (ClassicalProfile 1 α) := by
  let A := fun q => diffusion m q • (1 : PDE.Mat 1)
  have hb (q : XV 1) : m.lam ≤ diffusion m q ∧ diffusion m q ≤ m.Lam := by
    unfold diffusion; split <;> apply m.bounds
  have hm : Measurable (diffusion m) := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) <;>
      apply m.measurable.comp <;> unfold scale <;> fun_prop
  have hI : (0 : PDE.Mat 1) ≤ 1 := Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
  refine ⟨⟨m.lam,m.Lam,A,lift m,m.pos,(m.bounds 0).1.trans (m.bounds 0).2,
    fun i j => hm.mul_const _,fun q => ⟨smul_le_smul_of_nonneg_right (hb q).1 hI,
      smul_le_smul_of_nonneg_right (hb q).2 hI⟩,
    fun q hq => (lift_smooth m hq).contDiffWithinAt, fun q hq => ?_, lift_homogeneous m, ?_⟩⟩
  · unfold lift; split_ifs with h h
    · exact mul_pos (rpow_pos_of_pos (scale_pos h) _) (m.positive _)
    · exact mul_pos (rpow_pos_of_pos (scale_pos (neg_pos.mpr h)) _) (m.positive _)
    · apply rpow_pos_of_pos (abs_pos.mpr _) _
      intro e; apply hq; ext i <;> fin_cases i <;> simp_all <;> linarith
  · have hx : ∀ᵐ q ∂(volume : Measure (XV 1)), q.1 ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : PDE.Vec 1))
    filter_upwards [hx] with q hq
    have hq0 : q.1 0 ≠ 0 := fun e => hq (by ext i; simpa only [Subsingleton.elim i 0, Pi.zero_apply] using e)
    simpa only [statOp,sub_nonneg,PDE.vecDot,matrixContraction,A,Fin.sum_univ_one,
      Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] using scalar_super m hq0

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
