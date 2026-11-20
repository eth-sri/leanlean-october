module

public import PottsDiscontinuity.Bethe.CountingQuadrature
public import PottsDiscontinuity.Bethe.Prop21Tau

/-! The difference of the two counting functions satisfies the continuous offset
    equation up to the quadrature error. Reflection gives a strict contraction. -/

@[expose] public section

open Set MeasureTheory Finset

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

private theorem negpi_le_pi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]

private theorem d2Theta_swap (Δ x y : ℝ) : d2Theta Δ x y = -d1Theta Δ y x := by
  unfold d2Theta d1Theta
  rw [show theta Δ x = (fun t => -theta Δ t x) from funext (fun t => theta_swap Δ t x)]
  exact deriv.fun_neg

private theorem continuous_d2Theta_pair' {Δ : ℝ} (hΔ : Δ < -1) :
    Continuous (fun z : ℝ × ℝ => d2Theta Δ z.1 z.2) := by
  have h : Continuous (fun z : ℝ × ℝ => -d1Theta Δ z.2 z.1) :=
    ((continuous_d1Theta_pair hΔ).comp continuous_swap).neg
  simpa [d2Theta_swap] using h

private theorem d2Theta_pos {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) : 0 < d2Theta Δ x y := by
  have hlam := lamOf_pos hΔ
  rw [← kMap_kInv hlam x, ← kMap_kInv hlam y, d2Theta,
    deriv_theta_right_kMap hlam (cosh_lamOf hΔ)]
  exact div_pos (Xi_pos (by positivity) _) (Xi_pos hlam _)

private theorem integral_d2Theta {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y) = 2 * Real.pi := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y (_ : y ∈ uIcc (-Real.pi) Real.pi) =>
      (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt)
    (((continuous_d2Theta_pair' hΔ).comp (continuous_const.prodMk continuous_id)).intervalIntegrable
      (μ := volume) (-Real.pi) Real.pi)
  change (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y) = theta Δ x Real.pi - theta Δ x (-Real.pi) at h
  rw [h, theta_swap Δ Real.pi x, theta_swap Δ (-Real.pi) x,
    show theta Δ Real.pi x = theta Δ (-Real.pi) x - 2 * Real.pi by
      convert theta_add_two_pi_left Δ (-Real.pi) x using 2 <;> ring]
  ring

private theorem tauCont_neg' (Δ x : ℝ) : tauCont Δ (-x) = -tauCont Δ x := by
  have hU (lam z : ℝ) : tauU lam (-z) = -tauU lam z := by
    simp [tauU, trigSeries, ← tsum_neg]
  simp only [tauCont, kInv_neg, TcontFn, hU, neg_neg]; ring

/-- The scaled difference of counting functions, with the deficit tuple second. -/
noncomputable def countingShift (Δ : ℝ) (N : ℕ) {n k : ℕ} (p : Fin n → ℝ) (q : Fin k → ℝ)
    (x : ℝ) : ℝ :=
  (N : ℝ) * (betheCountingFunction Δ N k q x - betheCountingFunction Δ N n p x)

private noncomputable def countingShiftDeriv (Δ : ℝ) (N : ℕ) {n k : ℕ} (p : Fin n → ℝ) (q : Fin k → ℝ)
    (x : ℝ) : ℝ :=
  (N : ℝ) * (betheCountingDerivative Δ N k q x - betheCountingDerivative Δ N n p x)

private theorem hasDerivAt_countingShift {Δ : ℝ} (hΔ : Δ < -1) (N : ℕ) {n k : ℕ}
    (p : Fin n → ℝ) (q : Fin k → ℝ) (x : ℝ) :
    HasDerivAt (countingShift Δ N p q) (countingShiftDeriv Δ N p q x) x :=
  ((hasDerivAt_betheCountingFunction hΔ N k q x).sub
    (hasDerivAt_betheCountingFunction hΔ N n p x)).const_mul _

private theorem countingShift_neg {Δ : ℝ} {N n k : ℕ} {p : Fin n → ℝ} {q : Fin k → ℝ}
    (hp : p ∈ S_n n) (hq : q ∈ S_n k) (x : ℝ) :
    countingShift Δ N p q (-x) = -countingShift Δ N p q x := by
  simp only [countingShift, betheCountingFunction_neg hp, betheCountingFunction_neg hq]
  ring

private theorem countingShift_pi {Δ : ℝ} {N n k r : ℕ} {p : Fin n → ℝ} {q : Fin k → ℝ}
    (hp : p ∈ S_n n) (hq : q ∈ S_n k) (hN : 0 < N) (hcount : n = k + r) :
    countingShift Δ N p q Real.pi = (r : ℝ) / 2 := by
  have hc : (n : ℝ) = (k : ℝ) + r := by exact_mod_cast hcount
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simp only [countingShift, betheCountingFunction_pi hp hN, betheCountingFunction_pi hq hN, hc]
  field_simp; ring

section Residual

variable {Δ : ℝ} (hΔ : Δ < -1) {N n k r : ℕ} (hN : 0 < N) (hcount : n = k + r)
  {p : Fin n → ℝ} {q : Fin k → ℝ} (hp : p ∈ S_n n) (hq : q ∈ S_n k)

include hΔ hN hcount hp hq in
/-- After integration by parts the endpoint masses contribute half the deficit. -/
private theorem countingShift_residual {g G : ℝ → ℝ} {ep eq : ℝ}
    (hg : ∀ x ∈ J, HasDerivAt g (G x) x) (hc : ContinuousOn G J)
    (hP : |(∑ j, g (p j)) - (N : ℝ) * ∫ y in (-Real.pi)..Real.pi,
      g y * betheCountingDerivative Δ N n p y| ≤ ep)
    (hQ : |(∑ j, g (q j)) - (N : ℝ) * (∫ y in (-Real.pi)..Real.pi,
      g y * betheCountingDerivative Δ N k q y) + (r : ℝ) * (g (-Real.pi) + g Real.pi)| ≤ eq) :
    |(∑ j, g (q j)) - (∑ j, g (p j)) + (r : ℝ) * (g (-Real.pi) + g Real.pi) / 2 +
      (∫ y in (-Real.pi)..Real.pi, G y * countingShift Δ N p q y)| ≤ ep + eq := by
  have hcg : ContinuousOn g J := fun y hy => (hg y hy).continuousAt.continuousWithinAt
  have hDp := continuous_betheCountingDerivative hΔ N n p
  have hDq := continuous_betheCountingDerivative hΔ N k q
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => hg y (uIcc_of_le negpi_le_pi ▸ hy))
    (fun y _ => hasDerivAt_countingShift hΔ N p q y)
    (hc.intervalIntegrable_of_Icc negpi_le_pi)
    (((hDq.sub hDp).const_mul (N : ℝ)).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
  change (∫ y in (-Real.pi)..Real.pi, g y * countingShiftDeriv Δ N p q y) = _ at h
  have he (y : ℝ) : g y * countingShiftDeriv Δ N p q y = (N : ℝ) *
      (g y * betheCountingDerivative Δ N k q y - g y * betheCountingDerivative Δ N n p y) := by
    unfold countingShiftDeriv; ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (f := fun y => g y * betheCountingDerivative Δ N k q y)
    (g := fun y => g y * betheCountingDerivative Δ N n p y)
    ((hcg.mul hDq.continuousOn).intervalIntegrable_of_Icc negpi_le_pi)
    ((hcg.mul hDp.continuousOn).intervalIntegrable_of_Icc negpi_le_pi),
    countingShift_neg hp hq, countingShift_pi hp hq hN hcount] at h
  rcases abs_le.mp hP with ⟨_, _⟩
  rcases abs_le.mp hQ with ⟨_, _⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Residual

/-- A positive kernel with row mass `2π` is strictly contractive on odd functions
    after a constant is subtracted. -/
private theorem odd_kernel_estimate {Δ δ e : ℝ} (hΔ : Δ < -1) (hδ : 0 < δ)
    (hlow : ∀ x ∈ J, ∀ y ∈ J, δ ≤ d2Theta Δ x y)
    {u : ℝ → ℝ} (hc : Continuous u) (hodd : ∀ x, u (-x) = -u x)
    (hres : ∀ x ∈ J, |2 * Real.pi * u x + (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * u y)| ≤ e) :
    ∀ x ∈ J, |u x| ≤ e / (2 * Real.pi * δ) := by
  have hint0 : (∫ x in (-Real.pi)..Real.pi, u x) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi) u
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨_, ⟨le_rfl, negpi_le_pi⟩⟩ hc.abs.continuousOn
  have hmax' : ∀ y ∈ J, |u y| ≤ |u x| := fun y hy => hmax hy
  let K (y : ℝ) := d2Theta Δ x y - δ
  have hK : Continuous K :=
    ((continuous_d2Theta_pair' hΔ).comp (continuous_const.prodMk continuous_id)).sub continuous_const
  have hmass : (∫ y in (-Real.pi)..Real.pi, K y) = 2 * Real.pi - δ * (2 * Real.pi) := by
    simp only [K]
    rw [intervalIntegral.integral_sub ((hK.add continuous_const : Continuous (fun y => K y + δ)).congr
      (fun y => sub_add_cancel (d2Theta Δ x y) δ) |>.intervalIntegrable _ _) intervalIntegrable_const,
      integral_d2Theta hΔ, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hI : (∫ y in (-Real.pi)..Real.pi, u y * K y) = ∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * u y := by
    have hc2 := (continuous_d2Theta_pair' hΔ).comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => x))
    simp only [K, mul_comm (u _), sub_mul]
    rw [intervalIntegral.integral_sub (f := fun y => d2Theta Δ x y * u y)
      ((hc2.mul hc).intervalIntegrable _ _) ((hc.const_mul δ).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hint0, mul_zero, sub_zero]
  have hbound := abs_weighted_intervalIntegral_le negpi_le_pi hc.continuousOn hK.continuousOn
    (fun y hy => sub_nonneg.mpr (hlow x hx y hy)) hmax'
  rw [hI, hmass] at hbound
  have hdiff := abs_sub ((2 * Real.pi * u x) + (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * u y))
    (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * u y)
  rw [add_sub_cancel_right, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hdiff
  exact fun y hy => (hmax' y hy).trans ((le_div_iff₀ (by positivity)).mpr
    (by linarith only [hdiff, hres x hx, hbound]))

private noncomputable def quadConstant (m A L M : ℝ) (r : ℕ) : ℝ :=
  (L + A / m * M) / m ^ 2 + 2 * A * ((r : ℝ) + 1 / 2) * (r + 1) / m

/-- The shifted counting functions converge at rate `1/N` on the physical interval. -/
theorem countingShift_estimates {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {N n k : ℕ} {p : Fin n → ℝ} {q : Fin k → ℝ},
      0 < k → N = 2 * n → n = k + r →
      p ∈ S_n n → q ∈ S_n k →
      DiscreteBetheEquation Δ N n p → DiscreteBetheEquation Δ N k q →
      (∀ x ∈ J, m ≤ betheCountingDerivative Δ N n p x ∧ m ≤ betheCountingDerivative Δ N k q x) →
      (∀ x ∈ J, ∀ y ∈ J,
        |betheCountingDerivative Δ N n p x - betheCountingDerivative Δ N n p y| ≤ M * |x - y| ∧
        |betheCountingDerivative Δ N k q x - betheCountingDerivative Δ N k q y| ≤ M * |x - y|) →
      ∀ x ∈ J, |countingShift Δ N p q x + (r : ℝ) * tauCont Δ x| ≤ C / N := by
  obtain ⟨A, hA, hA'⟩ := exists_uniform_d1Theta_bounds hΔ
  rcases hA' Δ le_rfl with ⟨hAb, hAl⟩
  let K : Set (ℝ × ℝ) := J ×ˢ J
  obtain ⟨z, _, hz⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K).exists_isMinOn
    ⟨(-Real.pi, -Real.pi), ⟨⟨le_rfl, negpi_le_pi⟩, ⟨le_rfl, negpi_le_pi⟩⟩⟩
    (continuous_d2Theta_pair' hΔ).continuousOn
  let δ := d2Theta Δ z.1 z.2
  have hδ : 0 < δ := d2Theta_pos hΔ ..
  let C := (quadConstant m A A M 0 + quadConstant m A A M r) / (2 * Real.pi * δ)
  refine ⟨C, by dsimp [C, quadConstant]; positivity,
    fun {N n k p q} hk hN hcount hp hq hpBE hqBE hpos hLip => ?_⟩
  have hNpos : 0 < N := by omega
  let H := countingShift Δ N p q
  have hcH := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_countingShift hΔ N p q x).continuousAt
  have hsum (y : ℝ) : 2 * Real.pi * H y = (∑ j, theta Δ y (q j)) - (∑ j, theta Δ y (p j)) := by
    unfold H countingShift betheCountingFunction
    field_simp
    ring
  have hconv : ∀ x ∈ J, |H x + (r : ℝ) * tauCont Δ x| ≤ C / N := by
    let u (y : ℝ) := H y + (r : ℝ) * tauCont Δ y
    have hres (y : ℝ) (hy : y ∈ J) :
        |2 * Real.pi * u y + (∫ t in (-Real.pi)..Real.pi, d2Theta Δ y t * u t)| ≤
          (quadConstant m A A M 0 + quadConstant m A A M r) / N := by
      let g := theta Δ y
      let G := d2Theta Δ y
      have hcθ : Continuous G := (continuous_d2Theta_pair' hΔ).comp (continuous_const.prodMk continuous_id)
      have hg (t : ℝ) (_ : t ∈ J) : HasDerivAt g (G t) t :=
        (analyticAt_theta_right hΔ y t).differentiableAt.hasDerivAt
      have hG (t : ℝ) (ht : t ∈ J) : |G t| ≤ A := by
        simpa [G, d2Theta_swap] using (hAb t ht y hy).1
      have hGl (t : ℝ) (ht : t ∈ J) (u : ℝ) (hu : u ∈ J) : |G t - G u| ≤ A * |t - u| + 0 := by
        simp only [G, d2Theta_swap, neg_sub_neg, abs_sub_comm (d1Theta Δ u y), add_zero]
        simpa using hAl t ht y hy u hu y hy
      have hpQ := bethe_counting_quadrature hΔ hp (by omega) (r := 0) (by omega) hpBE
        hm hA.le hA.le hM le_rfl (fun x hx => (hpos x hx).1) (fun x hx t ht => (hLip x hx t ht).1) hg hG hGl
      have hqQ := bethe_counting_quadrature hΔ hq hk (r := r) (by omega) hqBE
        hm hA.le hA.le hM le_rfl (fun x hx => (hpos x hx).2) (fun x hx t ht => (hLip x hx t ht).2) hg hG hGl
      simp only [zero_div, add_zero, Nat.cast_zero, zero_mul] at hpQ hqQ
      have h := countingShift_residual hΔ hNpos hcount hp hq hg hcθ.continuousOn hpQ hqQ
      change |(∑ j, theta Δ y (q j)) - (∑ j, theta Δ y (p j)) + _ + _| ≤ _ at h
      rw [← hsum] at h
      replace h := h.trans_eq (show _ = (quadConstant m A A M 0 + quadConstant m A A M r) / (N : ℝ) by
        unfold quadConstant; ring)
      have hτ := tauCont_isCOESolution hΔ y hy
      unfold cOEop at hτ
      have hsplit : (∫ t in (-Real.pi)..Real.pi, d2Theta Δ y t * (H t + (r : ℝ) * tauCont Δ t)) =
          (∫ t in (-Real.pi)..Real.pi, d2Theta Δ y t * H t) +
          (r : ℝ) * ∫ t in (-Real.pi)..Real.pi, d2Theta Δ y t * tauCont Δ t := by
        simp only [mul_add, mul_left_comm (d2Theta Δ y _)]
        rw [intervalIntegral.integral_add (f := fun t => d2Theta Δ y t * H t)
          (g := fun t => (r : ℝ) * (d2Theta Δ y t * tauCont Δ t)) ((hcθ.mul hcH).intervalIntegrable _ _)
          (((hcθ.mul (continuous_tauCont hΔ)).const_mul (r : ℝ)).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
      dsimp only [u]
      rw [hsplit]
      rcases abs_le.mp h with ⟨hl, hu⟩
      exact abs_le.mpr ⟨by nlinarith only [hl, congrArg ((r : ℝ) * ·) hτ], by
        nlinarith only [hu, congrArg ((r : ℝ) * ·) hτ]⟩
    intro x hx
    have h := odd_kernel_estimate hΔ hδ (fun x hx y hy => hz (show (x, y) ∈ K from ⟨hx, hy⟩))
      (hcH.add ((continuous_tauCont hΔ).const_mul (r : ℝ)))
      (fun y => by change u (-y) = -u y; dsimp [u, H]; rw [countingShift_neg hp hq, tauCont_neg']; ring)
      hres x hx
    exact h.trans_eq (by ring)
  exact hconv

/-- The offset is Lipschitz at zero. Subtract its equation at zero, and use the
joint Lipschitz bound of the scattering kernel. -/
theorem exists_tauCont_abs_le_mul {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ J, |tauCont Δ x| ≤ L * |x| := by
  obtain ⟨A, hA, hA'⟩ := exists_uniform_d1Theta_bounds hΔ
  obtain ⟨hAb, hAl⟩ := hA' Δ le_rfl
  have hc := continuous_tauCont hΔ
  obtain ⟨T, hT⟩ := (isCompact_Icc : IsCompact J).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨A / (2 * Real.pi) + A * |T|, by positivity, fun x hx => ?_⟩
  have h0 : (0 : ℝ) ∈ J := ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  have hz : tauCont Δ 0 = 0 := by have h := tauCont_neg' Δ 0; rw [neg_zero] at h; linarith
  have ht y (hy : y ∈ J) : |theta Δ x y - theta Δ 0 y| ≤ A * |x| := by
    simpa using abs_sub_le_of_hasDerivAt
          (fun t _ => (analyticAt_theta_left hΔ t y).differentiableAt.hasDerivAt)
          (fun t ht => (hAb t ht y hy).1) hx h0
  let K (a : ℝ) := fun y => d2Theta Δ a y * tauCont Δ y
  have hK (a : ℝ) : IntervalIntegrable (K a) volume (-Real.pi) Real.pi :=
    (((continuous_d2Theta_pair' hΔ).comp (continuous_const.prodMk continuous_id)).mul hc).intervalIntegrable _ _
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi)
    (C := A * |x| * |T|) (f := fun y => K x y - K 0 y) (fun y hy => by
      have hy' : y ∈ J := uIcc_of_le negpi_le_pi ▸ Ioc_subset_Icc_self hy
      have hk : |d2Theta Δ x y - d2Theta Δ 0 y| ≤ A * |x| := by
        rw [d2Theta_swap, d2Theta_swap, neg_sub_neg, abs_sub_comm]
        simpa using hAl y hy' x hx y hy' 0 h0
      have hty : |tauCont Δ y| ≤ |T| := (Real.norm_eq_abs _ ▸ hT y hy').trans (le_abs_self _)
      rw [Real.norm_eq_abs, show K x y - K 0 y = (d2Theta Δ x y - d2Theta Δ 0 y) * tauCont Δ y by simp [K, sub_mul], abs_mul]
      exact mul_le_mul hk hty (abs_nonneg _) (by positivity))
  rw [Real.norm_eq_abs, intervalIntegral.integral_sub (hK x) (hK 0), sub_neg_eq_add,
    ← two_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)] at hI
  have hτ := tauCont_isCOESolution hΔ x hx
  have hτ0 := tauCont_isCOESolution hΔ 0 h0
  simp only [cOEop, hz, mul_zero] at hτ hτ0
  have h₁ := abs_le.mp (ht (-Real.pi) ⟨le_rfl, negpi_le_pi⟩)
  have h₂ := abs_le.mp (ht Real.pi ⟨negpi_le_pi, le_rfl⟩)
  have h₃ := abs_le.mp hI
  apply (le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 * Real.pi))
  rw [← abs_of_pos (by positivity : 0 < 2 * Real.pi), ← abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hR : (2 * Real.pi) * ((A / (2 * Real.pi) + A * |T|) * |x|) =
      A * |x| + A * |x| * |T| * (2 * Real.pi) := by field_simp
  rw [hR]
  exact abs_le.mpr ⟨by linarith only [hτ, hτ0, h₁.1, h₂.1, h₃.2],
    by linarith only [hτ, hτ0, h₁.2, h₂.2, h₃.1]⟩

end PottsDiscontinuity.Bethe
