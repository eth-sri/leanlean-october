module

public import NearlyMinimax.LiftL2
public import NearlyMinimax.LocalizationL2
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

𝚵
𝚻
noncomputable section
namespace NearlyMinimax.FieldLiftCovariance


variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {M : Measure W}

𝗇 𝔴 𝗓
𝗇 𝔦 fun _ : Fin k => 𝔴
abbrev KernelMap (p k : ℕ) :=
  ContinuousMultilinearMap ℝ 𝔦 ℝ

𝗃 𝕬 ἀ $ e i
𝗇 𝔱 ∏ i, 𝕬 X ω (σ i)
𝗇 𝕴 LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2
𝗇 𝔇 (𝕴).toLp fun ω => 𝔱
𝗇 𝔉 fun i => Pi.single (σ i) 1
𝗇 𝔊 ∀ j a, MemLp (fun ω => X j ω a) 2 μ
𝗇 𝔏 Fin n → Ω → 𝔴
𝗇 𝔖 Fin k ↪ Fin n
𝗇 𝔚 ∀ j, Measurable $ X j
𝗇 𝔠 iIndepFun X μ
𝗇 𝔢 KernelMap p k
𝗇 𝔧 Fin k → Fin p
/-- The actual raw kernel is a continuous linear function of its
multilinear coefficient map, with values in the observation L² space.
The finite coordinate expansion proves this even for unbounded features. -/
def rawKernelOperator (e : 𝔖)
    (X : 𝔏) (hind : 𝔠)
    (hmeas : 𝔚)
    (hL2 : 𝔊) : 𝔢 →L[ℝ] Lp ℝ 2 μ :=
  ∑ σ : 𝔧,
    (ContinuousMultilinearMap.apply ℝ 𝔦 ℝ
      𝔉).smulRight
      𝔇

𝗇 𝔅 fun i => 𝕬 X ω
𝗇 𝔨 𝔱
𝗇 𝔩 LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2
𝗇 𝔫 rawKernelOperator e X hind hmeas hL2
𝗇 𝔯 (𝔩).toLp fun ω => H 𝔅
𝗇 𝕭 H 𝔉 • 𝔇
/-- This operator is precisely the real raw kernel, modulo almost-everywhere equality. -/
theorem raw_kernel_operator_eq_toLp (e : 𝔖)
    X (hind : 𝔠)
    hmeas
    hL2 (H : 𝔢) :
    𝔫 H =
      𝔯 := by
  classical
  have heq : 𝔫 H =
      ∑ σ : 𝔧, 𝕭 := by
    simp [rawKernelOperator]
  rw [heq]
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
     fun σ => 𝕭
  have hterms : ∀ᵐ ω ∂μ, ∀ σ : 𝔧,
      𝕭 ω =
        H 𝔉 * 𝔨 := by
    apply Filter.eventually_all.mpr
    intro σ
    filter_upwards [Lp.coeFn_smul (H 𝔉)
      𝔇,
      (𝕴).coeFn_toLp] with ω hs hp
    simp_all
  filter_upwards [hsum, hterms,
    (𝔩).coeFn_toLp]
    with ω hs ht hH
  change 𝔯 ω = H 𝔅 at hH
  rw [hs, hH]
  calc
    _ = ∑ σ : 𝔧,
        H 𝔉 * 𝔨 :=
      Finset.sum_congr rfl fun σ _ => ht σ
    _ = H 𝔅 :=
      (LiftL2.multilinear_coordinate_expansion H.toMultilinearMap _).symm

/-- The genuine raw-kernel energy equals the operator's squared Hilbert norm. -/
theorem raw_kernel_operator_norm_sq (e : 𝔖)
    X (hind : 𝔠)
    hmeas
    hL2 (H : 𝔢) :
    ‖𝔫 H‖ ^ 2 =
      ∫ ω, H 𝔅 ^ 2 ∂μ := by
  rw [raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_norm_sq_eq_integral_sq _

𝗇 𝔎 ∫ w, ν w • H w ∂M
𝗇 𝔗 Integrable (fun w => ν w • H w) M
𝗇 𝔣 W → ℝ
𝗇 𝕲 W → 𝔢
/-- Bochner integration commutes with the actual raw-kernel operator. -/
theorem raw_kernel_integral_commute (e : 𝔖)
    X (hind : 𝔠)
    hmeas
    hL2
    (ν : 𝔣) (H : 𝕲)
    (hH : 𝔗) :
    𝔫 𝔎 =
      ∫ w, ν w • 𝔫 (H w) ∂M := by
  rw [← (𝔫).integral_comp_comm hH]
  simp

/-- Raw support separation becomes genuine L² orthogonality, before centering. -/
theorem raw_kernel_operator_inner_zero (e : 𝔖)
    X (hind : 𝔠)
    hmeas
    hL2 (H G : 𝔢)
    (hdisjoint : ∀ᵐ ω ∂μ,
      H 𝔅 * G 𝔅 = 0) :
    ⟪𝔫 H,
      𝔫 G⟫ = 0 := by
  rw [raw_kernel_operator_eq_toLp, raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_inner_eq_zero_of_disjoint _ _ hdisjoint

𝗇 𝔞 ν w * LiftL2.kernelStatistic (H w) X ω
𝗇 𝔡 (k.factorial * (n.descFactorial k : ℝ))⁻¹
𝗇 𝔪 fun _ => 𝔴
𝗇 𝔭 ν w * H w 𝔅
𝗇 𝕮 (ContinuousMultilinearMap.apply ℝ 𝔪 ℝ 𝔅).integrable_comp hH
𝗇 𝕯 fun w => 𝔞
𝗇 𝕰 Integrable (fun w => 𝔭) M
/-- A weighted factorial-lift term is integrable in its coefficient field. -/
theorem weighted_kernel_statistic_integrable
    (X : 𝔏) (ν : 𝔣) (H : 𝕲)
    (hH : 𝔗) ω :
    Integrable 𝕯 M := by
  classical
  let d := 𝔡
  have hi (e : 𝔖) : 𝕰 := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      𝕮
  convert integrable_finsetSum Finset.univ fun e _ => (hi e).const_mul d using 1
  funext w
  simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  dsimp
  ring

𝗃 𝕺 ∫ w, ἀ ∂M
/-- Actual spatial integration commutes with finite factorial averaging. -/
theorem kernel_statistic_integral_commute
    (X : 𝔏) (ν : 𝔣) (H : 𝕲)
    (hH : 𝔗) ω :
    𝕺 𝔞 =
      LiftL2.kernelStatistic 𝔎 X ω := by
  classical
  let d := 𝔡
  have hi (e : 𝔖) : 𝕰 := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      𝕮
  have heval v :
      𝔎 v = ∫ w, ν w * H w v ∂M := by
    rw [ContinuousMultilinearMap.integral_apply hH]
    rfl
  have halg : 𝕯 =
       fun w => d * ∑ e : 𝔖, 𝔭 := by
    funext w
    simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    dsimp
    ring
  rw [halg, integral_const_mul, integral_finsetSum _ fun e _ => hi e ]
  change d * ∑ e : 𝔖, 𝕺 𝔭 =
    d * ∑ e : 𝔖, 𝔎 𝔅
  simp_rw [heval]

𝗇 𝔍 𝗙₁
𝗇 𝕵 H w r
𝗇 𝔐 ∀ r, Integrable (fun w => ν w • 𝕵) M
𝗇 𝔒 ∫ w, ν w • 𝕵 ∂M
𝗇 𝔙 fun w => 𝕵
𝗇 𝔤 (r : Fin R) → KernelMap p 𝔍
𝗇 𝔮 LiftL2.centeredKernelExpansion 0 fun r => 𝔒
𝗇 𝔲 LiftL2.centeredKernelExpansion 0 $ H w
𝗃 𝔷 ∫ w, ν w * 𝔲 ἀ ω ∂M
𝗇 𝕳 W → 𝔤
𝗃 𝕶 fun r _ => ἀ X ν 𝔙 (hH r) ω
/-- Spatial integration commutes with the entire centered Taylor lift. -/
theorem centered_expansion_integral_commute
    (X : 𝔏) (ν : 𝔣)
    (H : 𝕳)
    (hH : 𝔐) ω :
    𝔷 X =
      𝔮 X ω := by
  simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  rw [integral_finsetSum _ 𝕶 weighted_kernel_statistic_integrable]
  exact Finset.sum_congr rfl 𝕶 kernel_statistic_integral_commute

𝗇 𝔔 fun i => v $ σ i
𝗃 𝕸 Equiv.Perm $ Fin ἀ
/-- Symmetry of the genuine multilinear fields is preserved by integration. -/
theorem integrated_kernel_symmetric
    (ν : 𝔣) (H : 𝕲)
    (hH : 𝔗)
    (hsym : ∀ w (σ : 𝕸 k) v,
      H w 𝔔 = H w v)
    (σ : 𝕸 k) v :
    𝔎 𝔔 = 𝔎 v := by
  rw [ContinuousMultilinearMap.integral_apply hH,
    ContinuousMultilinearMap.integral_apply hH]
  simp_all

𝗇 𝔳 fun j ω => X j ω - m
𝗇 𝔄 fun ω => 𝔷 𝔳
𝗇 𝔑 ∀ j a, ∫ ω, X j ω a ∂μ = m a
𝗇 𝔓 ∀ i j, IdentDistrib (X i) (X j) μ μ
𝗇 𝔘 𝔳
𝗇 𝕱 LiftL2.centerObservations_l2 X m hind hmeas hid hL2 hmean
/-- Actual coefficient integration yields a square-integrable centered
random variable; centering and integrability are proved from the input L²
observations, rather than required as covariance hypotheses. -/
theorem integrated_centered_lift_moment_facts
    (H : 𝕳)
    (ν : 𝔣) (hH : 𝔐)
    (X : 𝔏) m
    (hind : 𝔠) (hmeas : 𝔚)
    (hid : 𝔓)
    (hL2 : 𝔊)
    (hmean : 𝔑) :
    MemLp 𝔄 2 μ ∧
       ∫ ω, 𝔷 𝔘 ∂μ = 0 := by
  have heq : 𝔄 =
      𝔮
        𝔘 := by
    funext ω
    exact centered_expansion_integral_commute _ ν H hH ω
  rw [heq]
  obtain ⟨hi, hm, _, hlp, hzero⟩ := 𝕱
  exact ⟨LiftL2.centeredKernelExpansion_memLp_two _ _ _ hi hm hlp,
    LiftL2.centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero⟩

𝗇 𝔵 (Nat.succ_le_of_lt r.isLt).trans hR
𝗇 𝔈 fun i => X (Fin.castLEEmb 𝔵 i) ω
𝗇 𝔛 Λ ≤ 𝙒 - R + 1
𝗇 𝔟 Fin.castLEEmb 𝔵
𝗇 𝔜 ( (𝔍).factorial * Λ ^ 𝔍)⁻¹
𝗃 𝕹 fun i a => 𝕬 ἀ a
𝗃 𝕻 fun i => 𝕬 ἀ
/-- The factorial variance series and the centering contraction apply to an
arbitrary symmetric Taylor coefficient collection, including one obtained by
spatial integration. The right side consists of actual uncentered kernels. -/
theorem centered_expansion_variance_le_raw_power
    (H : 𝔤)
    (hsym : ∀ r (σ : 𝕸 𝔍) v,
      H r 𝔔 = H r v)
    (X : 𝔏) m (hR : R ≤ n)
    (hind : 𝔠) (hmeas : 𝔚)
    (hid : 𝔓)
    (hL2 : 𝔊)
    (hmean : 𝔑)
    Λ (hΛ : 𝖠₂) (hΛn : 𝔛) :
    variance (LiftL2.centeredKernelExpansion 0 H 𝔘) μ ≤
      ∑ r : Fin R, 𝔜 *
        ∫ ω, H r 𝔈 ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := 𝕱
  rw [LiftL2.centeredKernelExpansion_variance 0 H hsym _ hR hi hm hid' hlp hzero]
  apply Finset.sum_le_sum
  intro r _
  let e := 𝔟
  have hc := LiftL2.independent_centering_square_le_l2 μ (H r)
    𝕻 X 𝕻 hmeas (hind.precomp e.injective)
    (fun i j => 𝕬 hid $ e j ) 𝕹 hL2 m
    𝕹 hmean
  have hb := LiftL2.descFactorial_lower_bound hR (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((𝔍).factorial : ℝ) := 𝖠₃
  have hpow : 0 < Λ ^ 𝔍 := pow_pos hΛ _
  have hd := (inv_le_inv₀ (mul_pos hfac $ hpow.trans_le hb ) $ mul_pos hfac hpow ).2
    $ mul_le_mul_of_nonneg_left hb hfac.le
  exact (mul_le_mul_of_nonneg_left hc 𝖠₃ ).trans
    $ mul_le_mul_of_nonneg_right hd $ integral_nonneg 𝖸

𝗇 𝔬 𝕵
𝗇 𝔰 ∀ w r (σ : 𝕸 𝔍) v, 𝔬 𝔔 = 𝔬 v
𝗃 𝕷 ∑ r : Fin R, 𝔜 * ∫ ω, ἀ 𝔈 ^ 2 ∂μ
/-- U6's first spatial inequality: the variance of the actual integral of
centered factorial lifts is bounded by the integral-free raw kernel series.
The proof commutes actual integration with the finite lift, proves symmetry
after integration, and then contracts the centered kernel in L². -/
theorem integrated_centered_lift_variance_le_raw
    (H : 𝕳)
    (ν : 𝔣) (hH : 𝔐)
    (hsym : 𝔰)
    (X : 𝔏) m (hR : R ≤ n)
    (hind : 𝔠) (hmeas : 𝔚)
    (hid : 𝔓)
    (hL2 : 𝔊)
    (hmean : 𝔑)
    Λ (hΛ : 𝖠₂) (hΛn : 𝔛) :
    variance 𝔄 μ ≤
      𝕷 𝔒 := by
  have heq : 𝔄 =
      𝔮
        𝔘 := by
    funext ω
    exact centered_expansion_integral_commute _ ν H hH ω
  rw [heq]
  exact centered_expansion_variance_le_raw_power _
    (fun r => integrated_kernel_symmetric ν 𝔙 (hH r)
       fun w => hsym w r ) X m hR hind hmeas hid hL2 hmean Λ hΛ hΛn

𝗇 𝔥 ‖∫ w, ν w • K r w ∂M‖ ^ 2
𝗃 𝔶 ἀ (e r) X hind hmeas hL2
/-- U6's second spatial inequality for actual raw kernels. Distinct spatial
blocks are checked before centering; their L² orthogonality is proved from
disjoint raw support. This gains the block mass, without bounding responses. -/
theorem integrated_centered_lift_variance_localized [IsFiniteMeasure M]
    (H : 𝕳)
    (ν : 𝔣) (hν : MemLp ν 2 M)
    (hH : 𝔐)
    (hHmeas : ∀ r, AEStronglyMeasurable 𝔙 M)
    (hsym : 𝔰)
    (X : 𝔏) (m : 𝔴) (hR : R ≤ n)
    (hind : 𝔠) (hmeas : 𝔚)
    (hid : 𝔓)
    (hL2 : 𝔊)
    (hmean : 𝔑)
    (Λ : ℝ) (hΛ : 𝖠₂) (hΛn : 𝔛)
    (b : W → Fin q) (hb : Measurable b)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M,
      ‖rawKernelOperator 𝔟
        X hind hmeas hL2 𝔬‖ ≤ C r)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ ω ∂μ,
      𝔬 𝔈 *
      H v r 𝔈 = 0)
    L (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    variance 𝔄 μ ≤
      L * ∫ w, ν w ^ 2 * 𝕷 𝔬 ∂M := by
  let e (r : Fin R) := 𝔟
  let K r w := 𝔶 rawKernelOperator 𝔬
  let δ (r : Fin R) := 𝔜
  have hKmeas r :=
    (𝔶 rawKernelOperator).continuous.comp_aestronglyMeasurable $ hHmeas r
  have horth r w v h :=
    𝔶 raw_kernel_operator_inner_zero 𝔬 (H v r) $ hdisjoint r w v h
  have hl := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hKmeas
    C hC hbound horth δ fun r => by positivity L hL
  have hfirst := integrated_centered_lift_variance_le_raw H ν hH hsym X m hR
    hind hmeas hid hL2 hmean Λ hΛ hΛn
  have heq r :
       ∫ ω, 𝔒 (fun i => X (e r i) ω) ^ 2 ∂μ =
        𝔥 := by
    rw [← 𝔶 raw_kernel_operator_norm_sq,
      𝔶 raw_kernel_integral_commute ν 𝔙 $ hH r ]
  have hfirst' : variance 𝔄 μ ≤
      ∑ r : Fin R, δ r * 𝔥 := by
    apply hfirst.trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    tauto
  apply hfirst'.trans
  convert hl using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    apply congrArg fun t => ν w ^ 2 * t
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t => δ r * t)
      (𝔶 raw_kernel_operator_norm_sq 𝔬).symm
