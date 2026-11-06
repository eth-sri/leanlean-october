module

public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# Proposition 4.2

The proof of Proposition 4.2 of the paper: a perturbation `g` of a map `f ∈ S^ω(I)` with
`f([0,1]) ⊆ (0,1)` that is small in `𝒞¹` on `[0,1]`, agrees with `f` to first order on a finite
set `𝒴 ∪ 𝒵` and to second order on `𝒵`, and changes `f''/f'` by at least `δ` at the points of
`𝒴`, at a cost of `C δ` in the second derivative.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace MultiplicativeBump

theorem Differentiable.deriv' {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) :=
  fun _ => (hf.differentiableOn.deriv isOpen_univ).differentiableAt Filter.univ_mem

/-- A margin `m > 0` with `m ≤ f ≤ 1 - m` and `m ≤ |f'| ≤ 1 - m` on `I`. -/
theorem exists_margin {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ m > 0, ∀ x ∈ I,
      m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m := by
  have hmem : MapsTo ((↑) : ℝ → ℂ) I (nbhd (2 * ε)) := fun _ => ofReal_mem_nbhd (by positivity)
  have hf0 := Complex.continuous_re.comp_continuousOn
    (hf.differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem)
  have hf1 := ((hf.differentiableOn.deriv (isOpen_nbhd _)).continuousOn.comp
    Complex.continuous_ofReal.continuousOn hmem).norm
  let h (x : ℝ) := min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖))
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩
    ((hf0.inf (continuousOn_const.sub hf0)).inf (hf1.inf (continuousOn_const.sub hf1)))
  have hcl := subset_closure (ofReal_mem_nbhd hε hx₀)
  refine ⟨h x₀, lt_min (lt_min (hI x₀ hx₀).1 (by linarith [(hI x₀ hx₀).2]))
    (lt_min (norm_pos_iff.2 (hf.deriv_ne_zero x₀ hcl)) (by linarith [hf.norm_deriv_lt_one x₀ hcl])),
    fun x hx => ?_⟩
  have h1 : h x₀ ≤ h x := isMinOn_iff.1 hmin x hx
  simp only [h, le_min_iff] at h1
  exact ⟨h1.1.1, by linarith [h1.1.2], h1.2.1, by linarith [h1.2.2]⟩

/-- The product `P_W(z) = ∏_{w ∈ W} (z - w)³`. -/
noncomputable def P (W : Finset ℝ) (z : ℂ) : ℂ := ∏ w ∈ W, (z - w) ^ 3

theorem differentiable_P (W : Finset ℝ) : Differentiable ℂ (P W) := fun _ =>
  DifferentiableAt.fun_finsetProd fun w _ => (differentiableAt_id.sub_const (w : ℂ)).fun_pow 3

theorem P_ne_zero {W : Finset ℝ} {y : ℝ} (hy : y ∉ W) : P W y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hw => pow_ne_zero _ (sub_ne_zero.2 fun h =>
    hy (Complex.ofReal_injective h ▸ hw))

theorem hasDerivAt_sq_mul (c : ℂ) {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (z : ℂ) :
    HasDerivAt (fun z => (z - c) ^ 2 * Q z) (2 * (z - c) * Q z + (z - c) ^ 2 * deriv Q z) z := by
  have h1 : HasDerivAt (fun z => (z - c) ^ 2) (2 * (z - c)) z := by
    simpa using ((hasDerivAt_id' z).sub_const c).fun_pow 2
  exact (h1.fun_mul (hQ z).hasDerivAt).congr_deriv (by ring)

theorem deriv_sq_mul_self (c : ℂ) {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) :
    deriv (fun z => (z - c) ^ 2 * Q z) c = 0 ∧
      deriv (deriv (fun z => (z - c) ^ 2 * Q z)) c = 2 * Q c := by
  have hd : deriv (fun z => (z - c) ^ 2 * Q z) =
      fun z => 2 * (z - c) * Q z + (z - c) ^ 2 * deriv Q z :=
    funext fun z => (hasDerivAt_sq_mul c hQ z).deriv
  refine ⟨by simp [hd], ?_⟩
  rw [hd]
  have h1 := (((hasDerivAt_id' c).sub_const c).const_mul 2).fun_mul (hQ c).hasDerivAt
  have h2 := hasDerivAt_sq_mul c (Differentiable.deriv' hQ) c
  simpa using (h1.fun_add h2).deriv

/-- The localized Gaussian factor `E_{k,η}(z) = (z - k)² e^{-(z - k)²/η}` and its derivatives. -/
noncomputable def E (k η : ℝ) (z : ℂ) : ℂ :=
  (z - k) ^ 2 * Complex.exp (-(z - k) ^ 2 / η)

noncomputable def E1 (k η : ℝ) (z : ℂ) : ℂ :=
  (2 * (z - k) - 2 * (z - k) ^ 3 / η) * Complex.exp (-(z - k) ^ 2 / η)

noncomputable def E2 (k η : ℝ) (z : ℂ) : ℂ :=
  (2 - 10 * (z - k) ^ 2 / η + 4 * (z - k) ^ 4 / η ^ 2) * Complex.exp (-(z - k) ^ 2 / η)

theorem hasDerivAt_gaussian (k η : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-(z - k) ^ 2 / η))
      (-2 * (z - k) / η * Complex.exp (-(z - k) ^ 2 / η)) z := by
  refine (((((hasDerivAt_id' z).sub_const (k : ℂ)).fun_pow 2).neg.div_const (η : ℂ)).cexp).congr_deriv ?_
  norm_num; ring

theorem hasDerivAt_E (k η : ℝ) (z : ℂ) : HasDerivAt (E k η) (E1 k η z) z := by
  have h1 : HasDerivAt (fun z : ℂ => (z - k) ^ 2) (2 * (z - k)) z := by
    simpa using ((hasDerivAt_id' z).sub_const (k : ℂ)).fun_pow 2
  exact (h1.fun_mul (hasDerivAt_gaussian k η z)).congr_deriv (by unfold E1; ring)

theorem hasDerivAt_E1 (k η : ℝ) (z : ℂ) : HasDerivAt (E1 k η) (E2 k η z) z := by
  have h1 : HasDerivAt (fun z : ℂ => (z - k) ^ 3) (3 * (z - k) ^ 2) z := by
    simpa using ((hasDerivAt_id' z).sub_const (k : ℂ)).fun_pow 3
  have h2 := (((hasDerivAt_id' z).sub_const (k : ℂ)).const_mul 2).fun_sub
    ((h1.const_mul 2).div_const (η : ℂ))
  exact (h2.fun_mul (hasDerivAt_gaussian k η z)).congr_deriv (by unfold E2; ring)

theorem differentiable_E (k η : ℝ) : Differentiable ℂ (E k η) :=
  fun z => (hasDerivAt_E k η z).differentiableAt

/-- The bump term `B_{W,k,η}(z) = P_W(z) E_{k,η}(z)`. -/
noncomputable def B (W : Finset ℝ) (k η : ℝ) (z : ℂ) : ℂ := P W z * E k η z

theorem differentiable_B (W : Finset ℝ) (k η : ℝ) : Differentiable ℂ (B W k η) :=
  (differentiable_P W).mul (differentiable_E k η)

theorem deriv_B (W : Finset ℝ) (k η : ℝ) (z : ℂ) :
    deriv (B W k η) z = deriv (P W) z * E k η z + P W z * E1 k η z ∧
      deriv (deriv (B W k η)) z =
        deriv (deriv (P W)) z * E k η z + 2 * deriv (P W) z * E1 k η z + P W z * E2 k η z := by
  have hP := differentiable_P W
  have heq : deriv (B W k η) = fun w => deriv (P W) w * E k η w + P W w * E1 k η w :=
    funext fun w => ((hP w).hasDerivAt.fun_mul (hasDerivAt_E k η w)).deriv
  refine ⟨congrFun heq z, ?_⟩
  rw [heq]
  have hd2 := ((Differentiable.deriv' hP z).hasDerivAt.fun_mul (hasDerivAt_E k η z)).fun_add
    ((hP z).hasDerivAt.fun_mul (hasDerivAt_E1 k η z))
  rw [hd2.deriv]; ring

theorem B_at_self (W : Finset ℝ) (k η : ℝ) :
    B W k η k = 0 ∧ deriv (B W k η) k = 0 ∧ deriv (deriv (B W k η)) k = 2 * P W k := by
  simp [(deriv_B W k η k).1, (deriv_B W k η k).2, B, E, E1, E2, mul_comm]

theorem B_of_mem {W : Finset ℝ} (k η : ℝ) {w : ℝ} (hw : w ∈ W) :
    B W k η w = 0 ∧ deriv (B W k η) w = 0 ∧ deriv (deriv (B W k η)) w = 0 := by
  have heq : B W k η = fun z => (z - w) ^ 2 * ((z - w) * P (W.erase w) z * E k η z) :=
    funext fun z => by rw [B, P, ← Finset.mul_prod_erase W _ hw, P]; ring
  have hQ : Differentiable ℂ (fun z => (z - w) * P (W.erase w) z * E k η z) :=
    ((differentiable_id.sub_const (w : ℂ)).mul (differentiable_P _)).mul (differentiable_E k η)
  obtain ⟨h1, h2⟩ := deriv_sq_mul_self (w : ℂ) hQ
  rw [heq]
  exact ⟨by simp, h1, by simpa using h2⟩

/-! ## Elementary Gaussian bounds -/

theorem norm_E_le {x k ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ‖E k (ρ ^ 4) x‖ ≤ ρ ^ 2 ∧ ‖E1 k (ρ ^ 4) x‖ ≤ 5 * ρ ^ 2 ∧ ‖E2 k (ρ ^ 4) x‖ ≤ 20 ∧
      (ρ ≤ |x - k| → ‖E2 k (ρ ^ 4) x‖ ≤ 108 * ρ ^ 2) := by
  set s := (x - k) / ρ ^ 2
  set t := s ^ 2
  have ht : 0 ≤ t := sq_nonneg s
  have hxk : x - k = ρ ^ 2 * s := by dsimp [s]; field_simp
  have hsub : (x : ℂ) - k = ((ρ ^ 2 * s : ℝ) : ℂ) := by rw [← Complex.ofReal_sub, hxk]
  have hexp : Complex.exp (-((x : ℂ) - k) ^ 2 / (ρ ^ 4 : ℝ)) = ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, hsub]; congr 1; simp only [t]; norm_cast; field_simp
  have hE : E k (ρ ^ 4) x = ((ρ ^ 4 * (t * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [E, hexp, hsub]; simp only [t]; norm_cast; ring
  have hE1 : E1 k (ρ ^ 4) x = ((ρ ^ 2 * ((2 * s - 2 * s ^ 3) * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [E1, hexp, hsub]; simp only [t]; norm_cast; field_simp
  have hE2 : ‖E2 k (ρ ^ 4) x‖ = |2 - 10 * t + 4 * t ^ 2| * Real.exp (-t) := by
    have hE2' : E2 k (ρ ^ 4) x = (((2 - 10 * t + 4 * t ^ 2) * Real.exp (-t) : ℝ) : ℂ) := by
      rw [E2, hexp, hsub]; simp only [t]; norm_cast; field_simp
    rw [hE2', Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  set P := (1 + t / 2 + t ^ 2 / 8) ^ 2
  have hP : P * Real.exp (-t) ≤ 1 := by
    have h1 : 1 + t / 2 + (t / 2) ^ 2 / 2 ≤ Real.exp (t / 2) := by
      linarith [Real.quadratic_le_exp_of_nonneg (show 0 ≤ t / 2 by positivity)]
    have h2 : P ≤ Real.exp t := by
      refine (show P = (1 + t / 2 + (t / 2) ^ 2 / 2) ^ 2 by dsimp [P]; ring ▸
        pow_le_pow_left₀ (by positivity) h1 2).trans_eq ?_
      rw [← Real.exp_nat_mul]; ring_nf
    exact (mul_le_mul_of_nonneg_right h2 he0).trans_eq
      (by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
  have hle {X C : ℝ} (hC : 0 ≤ C) (hX : X ≤ C * P) : X * Real.exp (-t) ≤ C :=
    (mul_le_mul_of_nonneg_right hX he0).trans
      ((mul_assoc C P _).symm ▸ mul_le_of_le_one_right hC hP)
  have hs1 : |2 * s - 2 * s ^ 3| ≤ 5 * P :=
    abs_le.2 ⟨by dsimp [P, t]; nlinarith [sq_nonneg (s + 1), sq_nonneg (s * (s - 1))],
      by dsimp [P, t]; nlinarith [sq_nonneg (s - 1), sq_nonneg (s * (s + 1))]⟩
  have hs2 : |2 - 10 * t + 4 * t ^ 2| ≤ 2 + 10 * t + 4 * t ^ 2 :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  refine ⟨?_, ?_, ?_, fun hfar => ?_⟩
  · rw [hE, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (by positivity)
      (hle zero_le_one (by dsimp [P]; nlinarith))).trans
      (pow_le_pow_of_le_one hρ.le hρ1 (by omega))
  · rw [hE1, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hρ 2),
      abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [hle (by norm_num) hs1, pow_pos hρ 2]
  · rw [hE2]
    exact hle (by norm_num) (hs2.trans (by dsimp [P]; nlinarith))
  · rw [hE2]
    have hρt : 1 ≤ ρ ^ 2 * t := by
      rw [show ρ ^ 2 * t = (x - k) ^ 2 / ρ ^ 2 by simp only [t, hxk]; field_simp,
        one_le_div (pow_pos hρ 2)]
      simpa [sq_abs] using pow_le_pow_left₀ hρ.le hfar 2
    have h2 := hle (by norm_num : (0 : ℝ) ≤ 108)
      ((mul_le_mul_of_nonneg_left hs2 ht).trans (by dsimp [P]; nlinarith [sq_nonneg t]))
    nlinarith [mul_le_mul_of_nonneg_right hρt (mul_nonneg (abs_nonneg (2 - 10 * t + 4 * t ^ 2)) he0),
      pow_pos hρ 2]

theorem exists_B_bound (W : Finset ℝ) (k : ℝ) :
    ∃ M ≥ 0, ∀ {x ρ : ℝ}, x ∈ I → 0 < ρ → ρ ≤ 1 →
      ‖B W k (ρ ^ 4) x‖ ≤ M * ρ ^ 2 ∧
        ‖deriv (B W k (ρ ^ 4)) x‖ ≤ M * ρ ^ 2 ∧
        ‖deriv (deriv (B W k (ρ ^ 4))) x‖ ≤ 20 * ‖P W x‖ + M * ρ ^ 2 ∧
        (ρ ≤ |x - k| → ‖deriv (deriv (B W k (ρ ^ 4))) x‖ ≤ M * ρ ^ 2) := by
  have hP := differentiable_P W
  have hc0 := hP.continuous
  have hc1 := (Differentiable.deriv' hP).continuous
  have hc2 := (Differentiable.deriv' (Differentiable.deriv' hP)).continuous
  obtain ⟨M₀, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := I) (f := fun x : ℝ => ‖P W x‖ + ‖deriv (P W) x‖ + ‖deriv (deriv (P W)) x‖) (by fun_prop)
  set M := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨119 * M, by positivity, fun {x ρ} hx hρ hρ1 => ?_⟩
  have h := (le_abs_self _).trans ((hM x hx).trans (le_max_left M₀ 0))
  have hP0 : ‖P W x‖ ≤ M :=
    by linarith [norm_nonneg (deriv (P W) x), norm_nonneg (deriv (deriv (P W)) x)]
  have hP1 : ‖deriv (P W) x‖ ≤ M :=
    by linarith [norm_nonneg (P W x), norm_nonneg (deriv (deriv (P W)) x)]
  have hP2 : ‖deriv (deriv (P W)) x‖ ≤ M :=
    by linarith [norm_nonneg (P W x), norm_nonneg (deriv (P W) x)]
  obtain ⟨hE0, hE1, hE2, hE2_far⟩ := norm_E_le (x := x) (k := k) hρ hρ1
  obtain ⟨hd1, hd2⟩ := deriv_B W k (ρ ^ 4) x
  have m0 := mul_le_mul hP0 hE0 (norm_nonneg _) hM0
  have m1 := mul_le_mul hP1 hE0 (norm_nonneg _) hM0
  have m2 := mul_le_mul hP0 hE1 (norm_nonneg _) hM0
  have m3 := mul_le_mul hP2 hE0 (norm_nonneg _) hM0
  have m4 := mul_le_mul hP1 hE1 (norm_nonneg _) hM0
  have h1 := hd1 ▸ norm_add_le (deriv (P W) x * E k (ρ ^ 4) x) (P W x * E1 k (ρ ^ 4) x)
  have h3 := hd2 ▸ norm_add₃_le (a := deriv (deriv (P W)) x * E k (ρ ^ 4) x)
    (b := 2 * deriv (P W) x * E1 k (ρ ^ 4) x) (c := P W x * E2 k (ρ ^ 4) x)
  rw [norm_mul, norm_mul] at h1
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_two] at h3
  exact ⟨by rw [B, norm_mul]; nlinarith, by nlinarith,
    by nlinarith [mul_le_mul_of_nonneg_left hE2 (norm_nonneg (P W x)), mul_nonneg hM0 (sq_nonneg ρ)],
    fun hfar => by nlinarith [mul_le_mul hP0 (hE2_far hfar) (norm_nonneg _) hM0]⟩

/-- Near a point `y` with `F(y) ≠ 0`, `|F| ≤ 2 |F(y)|` for a continuous `F`. -/
theorem eventually_near {F : ℂ → ℂ} (hF : Continuous F) {y : ℝ} (hy : F y ≠ 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ x : ℝ, |x - y| < ρ → ‖F x‖ ≤ 2 * ‖F y‖ := by
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.1 hF.continuousAt (‖F y‖) (norm_pos_iff.2 hy)
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ x hx
  have h1 := h (by rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx.trans hρ.2)
  rw [dist_eq_norm] at h1
  linarith [norm_sub_norm_le (F x) (F y)]

/-- Small radii separate the points of a finite set: `2ρ < |y - y'|` for `y ≠ y'`. -/
theorem eventually_sep (Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'| := by
  refine (eventually_all_finset Y).2 fun k _ => (eventually_all_finset Y).2 fun k' _ => ?_
  by_cases hkk : k = k'
  · exact Eventually.of_forall fun _ h => absurd hkk h
  · filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.2 (sub_ne_zero.2 hkk)))] with ρ hρ _
    linarith [hρ.2]

end MultiplicativeBump

open MultiplicativeBump in
/-- Proposition 4.2: additive localized perturbation `g = f + ∑_{k ∈ Y} a_k P_{W_k} E_{k,ρ⁴}`. -/
theorem proposition_4_2 {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) {Y Z : Finset ℝ}
    (hY : ∀ y ∈ Y, y ∈ I) (hZ : ∀ z ∈ Z, z ∈ I) (hYZ : Disjoint Y Z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℂ → ℂ, (∃ ε' > 0, InClass ε' g) ∧
      (∀ y ∈ Y ∪ Z, g y = f y ∧ deriv g y = deriv f y) ∧
      (∀ z ∈ Z, deriv (deriv g) z = deriv (deriv f) z) ∧
      (∀ y ∈ Y, δ ≤ ‖deriv (deriv g) y / deriv g y - deriv (deriv f) y / deriv f y‖) ∧
      (∀ x ∈ I, ‖g x - f x‖ < δ) ∧ (∀ x ∈ I, ‖deriv g x - deriv f x‖ < δ) ∧
      (∀ x ∈ I, ‖deriv (deriv g) x - deriv (deriv f) x‖ < 21 * δ) := by
  classical
  obtain ⟨m, hm, hmar⟩ := exists_margin hε hf hI
  have hU : IsOpen (nbhd (2 * ε)) := isOpen_nbhd _
  have hmem : ∀ x ∈ I, (x : ℂ) ∈ nbhd (2 * ε) := fun x hx => ofReal_mem_nbhd (by positivity) hx
  let W : ℝ → Finset ℝ := fun k => Y.erase k ∪ Z
  have hkW : ∀ k ∈ Y, k ∉ W k := fun k hk h =>
    (Finset.mem_union.1 h).elim (Finset.notMem_erase k Y) (Finset.disjoint_left.1 hYZ hk)
  have hPN0 : ∀ k ∈ Y, P (W k) k ≠ 0 := fun k hk => P_ne_zero (hkW k hk)
  let a : ℝ → ℝ := fun k => δ * ‖deriv f k‖ / (2 * ‖P (W k) k‖)
  have ha0 : ∀ k ∈ Y, 0 ≤ a k := fun k _ => by positivity
  have haN : ∀ k ∈ Y, a k * (2 * ‖P (W k) k‖) = δ * ‖deriv f k‖ := fun k hk => by
    have := norm_pos_iff.2 (hPN0 k hk)
    dsimp [a]; field_simp
  choose M hM0 hM using fun k => exists_B_bound (W k) k
  let S := ∑ k ∈ Y, a k * M k
  set s := min δ (m / 2)
  have hs : 0 < s := lt_min hδ (half_pos hm)
  have hρ_small : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ≤ 1 ∧ S * ρ ^ 2 < s := by
    have hc : ContinuousAt (fun ρ : ℝ => S * ρ ^ 2) 0 := by fun_prop
    filter_upwards [Ioo_mem_nhdsGT one_pos,
      nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by simpa using hs)))] with ρ hρ1 hρ2
      using ⟨hρ1.2.le, hρ2⟩
  obtain ⟨ρ, ⟨⟨⟨hnear, hsep⟩, hρ1, hSρ⟩, hρ0 : 0 < ρ⟩⟩ :=
    ((((eventually_all_finset Y).2 fun k hk =>
      eventually_near (differentiable_P (W k)).continuous (hPN0 k hk)).and
      (eventually_sep Y)).and hρ_small |>.and self_mem_nhdsWithin).exists
  let H : ℂ → ℂ := fun z => ∑ k ∈ Y, (a k : ℂ) * B (W k) k (ρ ^ 4) z
  let g : ℂ → ℂ := fun z => f z + H z
  have hH_diff : Differentiable ℂ H := fun z =>
    DifferentiableAt.fun_sum fun k _ => (differentiable_B (W k) k (ρ ^ 4) z).const_mul _
  have hderiv_H (z : ℂ) : deriv H z = ∑ k ∈ Y, (a k : ℂ) * deriv (B (W k) k (ρ ^ 4)) z ∧
      deriv (deriv H) z = ∑ k ∈ Y, (a k : ℂ) * deriv (deriv (B (W k) k (ρ ^ 4))) z := by
    have heq : deriv H = fun w => ∑ k ∈ Y, (a k : ℂ) * deriv (B (W k) k (ρ ^ 4)) w :=
      funext fun w => (HasDerivAt.fun_sum fun k _ =>
        (differentiable_B (W k) k (ρ ^ 4) w).hasDerivAt.const_mul _).deriv
    refine ⟨congrFun heq z, ?_⟩
    rw [heq]
    exact (HasDerivAt.fun_sum fun k _ =>
      ((Differentiable.deriv' (differentiable_B (W k) k (ρ ^ 4))) z).hasDerivAt.const_mul _).deriv
  have hderiv_g {x : ℝ} (hx : x ∈ I) : deriv g x = deriv f x + deriv H x ∧
      deriv (deriv g) x = deriv (deriv f) x + deriv (deriv H) x := by
    have hd1 {w : ℂ} (hw : w ∈ nbhd (2 * ε)) : deriv g w = deriv f w + deriv H w :=
      deriv_add (hf.differentiableOn.differentiableAt (hU.mem_nhds hw)) (hH_diff w)
    have hzx := hU.mem_nhds (hmem x hx)
    refine ⟨hd1 (hmem x hx), ?_⟩
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem hzx fun _ => hd1)]
    exact deriv_add ((hf.differentiableOn.deriv hU).differentiableAt hzx)
      (Differentiable.deriv' hH_diff x)
  have hB_yz {k w : ℝ} (hk : k ∈ Y) (hw : w ∈ Y ∪ Z) :
      B (W k) k (ρ ^ 4) w = 0 ∧ deriv (B (W k) k (ρ ^ 4)) w = 0 ∧
        deriv (deriv (B (W k) k (ρ ^ 4))) w = if w = k then 2 * P (W k) k else 0 := by
    by_cases hwk : w = k
    · subst hwk; simpa using B_at_self (W w) w (ρ ^ 4)
    · simpa [hwk] using B_of_mem k (ρ ^ 4) (Finset.mem_union.2 ((Finset.mem_union.1 hw).imp_left
        fun h => Finset.mem_erase.2 ⟨hwk, h⟩))
  have hH01 {w : ℝ} (hw : w ∈ Y ∪ Z) : H w = 0 ∧ deriv H w = 0 :=
    ⟨Finset.sum_eq_zero fun k hk => by simp [(hB_yz hk hw).1],
      by rw [(hderiv_H w).1]; exact Finset.sum_eq_zero fun k hk => by simp [(hB_yz hk hw).2.1]⟩
  have hest : ∀ x ∈ I, ‖H x‖ ≤ S * ρ ^ 2 ∧ ‖deriv H x‖ ≤ S * ρ ^ 2 ∧
      ‖deriv (deriv H) x‖ ≤ 20 * δ + S * ρ ^ 2 := by
    intro x hx
    have hterm : ∀ k ∈ Y,
        ‖(a k : ℂ) * B (W k) k (ρ ^ 4) x‖ ≤ a k * M k * ρ ^ 2 ∧
        ‖(a k : ℂ) * deriv (B (W k) k (ρ ^ 4)) x‖ ≤ a k * M k * ρ ^ 2 ∧
        ‖(a k : ℂ) * deriv (deriv (B (W k) k (ρ ^ 4))) x‖ ≤
          (if |x - k| < ρ then 20 * δ else 0) + a k * M k * ρ ^ 2 := by
      intro k hk
      obtain ⟨b0, b1, b2, bfar⟩ := hM k hx hρ0 hρ1
      have hak := ha0 k hk
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hak]
      refine ⟨by nlinarith [mul_le_mul_of_nonneg_left b0 hak],
        by nlinarith [mul_le_mul_of_nonneg_left b1 hak], ?_⟩
      split_ifs with hxk
      · have hPk : a k * ‖P (W k) x‖ ≤ δ :=
          ((mul_le_mul_of_nonneg_left (hnear k hk x hxk) hak).trans_eq (haN k hk)).trans
            (mul_le_of_le_one_right hδ.le (by linarith [(hmar k (hY k hk)).2.2.2]))
        nlinarith [mul_le_mul_of_nonneg_left b2 hak,
          mul_nonneg hak (mul_nonneg (hM0 k) (sq_nonneg ρ))]
      · nlinarith [mul_le_mul_of_nonneg_left (bfar (not_lt.1 hxk)) hak]
    have hcard : (Y.filter fun k => |x - k| < ρ).card ≤ 1 :=
      Finset.card_le_one.2 fun k hk k' hk' => by
        obtain ⟨hkY, hxk⟩ := Finset.mem_filter.1 hk
        obtain ⟨hk'Y, hxk'⟩ := Finset.mem_filter.1 hk'
        by_contra hne
        linarith [hsep k hkY k' hk'Y hne, abs_sub_comm k x ▸ abs_sub_le k x k']
    have hsum_ite : ∑ k ∈ Y, (if |x - k| < ρ then 20 * δ else 0) ≤ 20 * δ := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hcard)
    have hsum_S : ∑ k ∈ Y, a k * M k * ρ ^ 2 = S * ρ ^ 2 := (Finset.sum_mul _ _ _).symm
    refine ⟨(norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => (hterm k hk).1).trans hsum_S.le),
      ?_, ?_⟩
    · rw [(hderiv_H x).1]
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => (hterm k hk).2.1).trans hsum_S.le)
    · rw [(hderiv_H x).2]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => (hterm k hk).2.2).trans ?_)
      rw [Finset.sum_add_distrib, hsum_S]; linarith
  have hSδ : S * ρ ^ 2 < δ := hSρ.trans_le (min_le_left _ _)
  have hSm : S * ρ ^ 2 < m / 2 := hSρ.trans_le (min_le_right _ _)
  refine ⟨g, ?_, fun w hw => ?_, fun w hw => ?_, fun y hy => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · refine exists_inClass hU (by rintro _ ⟨x, hx, rfl⟩; exact hmem x hx)
      (hf.differentiableOn.add hH_diff.differentiableOn) (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
    · show (f x + H x).im = 0
      rw [Complex.add_im, hf.im_eq_zero x hx, zero_add, Complex.im_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [B, show P (W k) x = ((∏ w ∈ W k, (x - w) ^ 3 : ℝ) : ℂ) by simp [P],
        show E k (ρ ^ 4) x = (((x - k) ^ 2 * Real.exp (-(x - k) ^ 2 / ρ ^ 4) : ℝ) : ℂ) by
          simp [E, Complex.ofReal_exp],
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_im]
    · obtain ⟨h1, h2, -, -⟩ := hmar x hx
      have h3 := abs_le.1 ((Complex.abs_re_le_norm (H x)).trans ((hest x hx).1.trans hSm.le))
      show (f x + H x).re ∈ I
      rw [Complex.add_re]; constructor <;> linarith
    · obtain ⟨-, -, h1, -⟩ := hmar x hx
      have h2 := ((hest x hx).2.1).trans_lt hSm
      rw [(hderiv_g hx).1]
      intro h0
      rw [eq_neg_of_add_eq_zero_right h0, norm_neg] at h2; linarith
    · rw [(hderiv_g hx).1]
      linarith [(hmar x hx).2.2.2, ((hest x hx).2.1).trans_lt hSm,
        norm_add_le (deriv f x) (deriv H x)]
  · rw [(hderiv_g ((Finset.mem_union.1 hw).elim (hY w) (hZ w))).1, (hH01 hw).2, add_zero]
    exact ⟨by simp [g, (hH01 hw).1], rfl⟩
  · rw [(hderiv_g (hZ w hw)).2, (hderiv_H w).2,
      Finset.sum_eq_zero fun k hk => ?_, add_zero]
    simp [(hB_yz hk (Finset.mem_union_right _ hw)).2.2,
      show w ≠ k from fun h => Finset.disjoint_left.1 hYZ (h ▸ hk) hw]
  · have hyI := hY y hy
    have hne : deriv f y ≠ 0 := norm_pos_iff.1 (hm.trans_le (hmar y hyI).2.2.1)
    have hH2 : deriv (deriv H) y = (a y : ℂ) * (2 * P (W y) y) := by
      rw [(hderiv_H y).2, Finset.sum_eq_single y]
      · simp [(hB_yz hy (Finset.mem_union_left _ hy)).2.2]
      · exact fun k hk hyk => by simp [(hB_yz hk (Finset.mem_union_left _ hy)).2.2, hyk.symm]
      · exact (absurd hy ·)
    rw [(hderiv_g hyI).2, (hderiv_g hyI).1,
      (hH01 (Finset.mem_union_left _ hy)).2, hH2, add_zero, add_div, add_sub_cancel_left,
      norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha0 y hy),
      Complex.norm_two, le_div_iff₀ (norm_pos_iff.2 hne), haN y hy]
  · simpa [g] using (hest x hx).1.trans_lt hSδ
  · rw [(hderiv_g hx).1, add_sub_cancel_left]
    exact (hest x hx).2.1.trans_lt hSδ
  · rw [(hderiv_g hx).2, add_sub_cancel_left]
    linarith [(hest x hx).2.2, hSδ]

end AnalyticESC
