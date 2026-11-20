module

public import RequestProject.WeakConstancy
public import RequestProject.Finite

/-!
# Mollifier estimates for `H¹` functions

For `u ∈ L²(Ω)` with weak gradient `g`, extended by zero to `U : ℂ → ℂ`, and a probability
density `ρ` supported in `{‖z‖ ≤ R}`, the mollification `ρ ⋆ U` is close to `U` in `L²` on
every open set `W` from which all segments `t - s z` (`t ∈ W`, `z ∈ supp ρ`, `0 ≤ s ≤ 1`)
stay inside `Ω`:
`‖1_W (U - ρ ⋆ U)‖_{L²} ≤ R (‖g₀‖ + ‖g₁‖)`.

The proof is by duality: the pairing of `U - ρ ⋆ U` with a test function is computed with the
fundamental theorem of calculus along segments and the definition of the weak gradient, and an
`L²` function whose pairings with test functions supported in `W` are bounded by `C ‖φ‖` has
norm at most `C`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set
open scoped Manifold ComplexConjugate

noncomputable section

namespace PolyaNeumann

/-- The `L²(ℂ)` norm of a function, as a real number. -/
def l2norm (f : ℂ → ℂ) : ℝ := (eLpNorm f 2 volume).toReal

lemma memLp_extZero {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (u : L2 Ω) :
    MemLp (extZero Ω u) 2 volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)

/-- Cauchy–Schwarz for `∫_Ω g ψ`. -/
lemma norm_setIntegral_mul_le {Ω : Set ℂ} (g : L2 Ω) {ψ : ℂ → ℂ} (hψ : MemLp ψ 2 volume) :
    ‖∫ w in Ω, g w * ψ w‖ ≤ ‖g‖ * l2norm ψ := by
  rw [← lpIntegralPair_apply (hψ.restrict Ω)]
  refine (norm_lpIntegralPair_apply_le (hψ.restrict Ω) g).trans ?_
  gcongr
  exact ENNReal.toReal_mono hψ.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- The weak gradient identity, in an arbitrary direction `v`. -/
lemma integral_extZero_mul_fderiv {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {ψ : ℂ → ℂ} (hψ : TestFunction Ω ψ) (v : ℂ) :
    ∫ t, extZero Ω u t * fderiv ℝ ψ t v =
      -((v.re : ℂ) * (∫ w in Ω, g 0 w * ψ w) + (v.im : ℂ) * ∫ w in Ω, g 1 w * ψ w) := by
  set A : Fin 2 → ℂ → ℂ := fun i t => extZero Ω u t * fderiv ℝ ψ t (coordDir i)
  have hv : (fun t => extZero Ω u t * fderiv ℝ ψ t v) =
      fun t => (v.re : ℂ) * A 0 t + (v.im : ℂ) * A 1 t := by
    ext t
    have : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul]
    simp only [A, coordDir]
    simp; ring
  have hU : LocallyIntegrable (extZero Ω u) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hint : ∀ i, Integrable (A i) := by
    intro i
    have hs :=
      (hψ.2.1.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) rfl
    exact hU.integrable_smul_right_of_hasCompactSupport
      ((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const) hs
  have hI : ∀ i, ∫ t, A i t = -∫ w in Ω, g i w * ψ w := by
    intro i
    rw [← hg ψ hψ i]
    rw [← integral_indicator hΩ.measurableSet]
    congr 1; ext t
    by_cases ht : t ∈ Ω <;> simp [A, extZero, ht]
  rw [hv, integral_add ((hint 0).const_mul _) ((hint 1).const_mul _), integral_const_mul,
    integral_const_mul, hI, hI]
  ring

lemma testFunction_translate {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (a : ℂ) (ha : ∀ t ∈ tsupport φ, t - a ∈ Ω) :
    TestFunction Ω (fun t => φ (t + a)) := ⟨ContDiff.comp hφ (ContDiff.add contDiff_id contDiff_const), ⟨HasCompactSupport.comp_homeomorph hφs (Homeomorph.addRight a), fun ⦃t⦄ ht => have this := have h := tsupport_comp_subset_preimage φ (Continuous.add continuous_id continuous_const); h ht; Eq.mp (congrArg (Membership.mem Ω) (add_sub_cancel_right t a)) (ha (t + a) this)⟩⟩

lemma l2norm_translate {φ : ℂ → ℂ} (hφ : AEStronglyMeasurable φ volume) (a : ℂ) :
    l2norm (fun t => φ (t + a)) = l2norm φ := by
  unfold l2norm
  congr 1
  exact eLpNorm_comp_measurePreserving hφ (measurePreserving_add_right volume a)

/-- **Pairing with a translation difference.** If every segment from `tsupport φ` in the
direction `-z` of length `‖z‖` stays in `Ω`, then
`|∫ U(t) (φ(t+z) - φ(t)) dt| ≤ ‖z‖ (‖g₀‖ + ‖g₁‖) ‖φ‖₂`. -/
theorem pairing_translate_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (z : ℂ)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ tsupport φ, t - s • z ∈ Ω) :
    ‖∫ t, extZero Ω u t * (φ (t + z) - φ t)‖ ≤ ‖z‖ * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
  set D : ℂ → ℝ → ℂ := fun t s => fderiv ℝ φ (t + s • z) z with hD
  have hDc : Continuous (fun p : ℂ × ℝ => D p.1 p.2) :=
    ((hφ.continuous_fderiv (by simp)).comp (continuous_fst.add
      (continuous_snd.smul continuous_const))).clm_apply continuous_const
  -- fundamental theorem of calculus along the segment
  have hftc : ∀ t, φ (t + z) - φ t = ∫ s in (0 : ℝ)..1, D t s := by
    intro t
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => φ (t + s • z)) (D t s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => t + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add t
      exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hDc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    simp
  -- the inner integrals, by the weak gradient identity
  set B := ‖z‖ * (‖g 0‖ + ‖g 1‖) * l2norm φ
  have hinner : ∀ s ∈ Icc (0 : ℝ) 1, ‖∫ t, extZero Ω u t * D t s‖ ≤ B := by
    intro s hs
    have hψ := testFunction_translate hφ hφs (s • z) (hseg s hs)
    have hfd : ∀ t, fderiv ℝ (fun t => φ (t + s • z)) t = fderiv ℝ φ (t + s • z) := by
      intro t
      exact fderiv_comp_add_right _
    have := integral_extZero_mul_fderiv hΩ hg hψ z
    simp only [hfd] at this
    rw [this, norm_neg]
    have hmem : MemLp (fun t => φ (t + s • z)) 2 volume :=
      (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1)
    have hn : l2norm (fun t => φ (t + s • z)) = l2norm φ :=
      l2norm_translate hφ.continuous.aestronglyMeasurable _
    have h0 := norm_setIntegral_mul_le (g 0) hmem
    have h1 := norm_setIntegral_mul_le (g 1) hmem
    rw [hn] at h0 h1
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    have hl : 0 ≤ l2norm φ := ENNReal.toReal_nonneg
    calc _ ≤ ‖(z.re : ℂ) * ∫ w in Ω, g 0 w * φ (w + s • z)‖ +
          ‖(z.im : ℂ) * ∫ w in Ω, g 1 w * φ (w + s • z)‖ := norm_add_le _ _
      _ ≤ |z.re| * (‖g 0‖ * l2norm φ) + |z.im| * (‖g 1‖ * l2norm φ) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
          gcongr
      _ ≤ ‖z‖ * (‖g 0‖ * l2norm φ) + ‖z‖ * (‖g 1‖ * l2norm φ) := by gcongr
      _ = _ := by ring
  -- Fubini
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hU :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  set L : Set ℂ := (fun p : ℂ × ℝ => p.1 - p.2 • z) '' (tsupport φ ×ˢ Icc 0 1)
  have hL : IsCompact L := (hφs.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨M, hM⟩ := (hφs.fderiv ℝ).exists_bound_of_continuous (hφ.continuous_fderiv (by simp))
  have hDb : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖D t s‖ ≤ M * ‖z‖ * ‖L.indicator (fun _ => (1 : ℝ)) t‖ := by
    intro t s hs
    by_cases ht : t ∈ L
    · simp  [ht, norm_one, mul_one]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; tauto)
    · have : t + s • z ∉ tsupport (fderiv ℝ φ) := by
        intro h
        exact ht ⟨(t + s • z, s), ⟨tsupport_fderiv_subset ℝ h, hs⟩, by simp⟩
      simp only [D]
      rw [image_eq_zero_of_notMem_tsupport this]; simp_all
  have hint : Integrable (fun p : ℂ × ℝ => extZero Ω u p.1 * D p.1 p.2) (volume.prod ν) := by
    have hLU : Integrable (fun t => M * ‖z‖ * ‖L.indicator (extZero Ω u) t‖) :=
      (((integrable_indicator_iff hL.measurableSet).mpr
        (hU.integrableOn_isCompact hL)).norm.const_mul _)
    refine (hLU.comp_fst ν).mono' ?_ ?_
    · exact ((hU.aestronglyMeasurable.comp_fst (ν := ν)).mul hDc.aestronglyMeasurable)
    · have hae : ∀ᵐ p ∂((volume : Measure ℂ).prod ν), p.2 ∈ Ioc (0 : ℝ) 1 := by
        rw [ae_iff]
        have : {p : ℂ × ℝ | p.2 ∉ Ioc (0 : ℝ) 1} = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext; simp
        rw [this, Measure.prod_prod]
        simp [ν]
      filter_upwards [hae] with p hp
      have := hDb p.1 p.2 (Ioc_subset_Icc_self hp)
      by_cases ht : p.1 ∈ L
      · simp only [ht, indicator_of_mem, norm_mul] at this ⊢
        simp   at this
        calc ‖extZero Ω u p.1‖ * ‖D p.1 p.2‖ ≤ ‖extZero Ω u p.1‖ * (M * ‖z‖) := by gcongr
          _ = _ := by ring
      · simp only [ht, not_false_eq_true, indicator_of_notMem, norm_zero, mul_zero] at this ⊢
        simp_all
  have hswap : ∫ t, extZero Ω u t * (φ (t + z) - φ t) =
      ∫ s in Ioc (0 : ℝ) 1, ∫ t, extZero Ω u t * D t s := by
    simp_rw [hftc, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    exact integral_integral_swap hint
  rw [hswap]
  calc ‖∫ s in Ioc (0 : ℝ) 1, ∫ t, extZero Ω u t * D t s‖ ≤
        B * (volume (Ioc (0 : ℝ) 1)).toReal :=
        norm_setIntegral_le_of_norm_le_const (by simp)
          fun s hs => hinner s (Ioc_subset_Icc_self hs)
    _ = B := by simp

/-- **Pairing with a mollification difference.** -/
theorem pairing_mollify_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1) {R : ℝ} (hR : ∀ z ∈ tsupport ρ, ‖z‖ ≤ R)
    (hseg : ∀ z ∈ tsupport ρ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ tsupport φ, t - s • z ∈ Ω) :
    ‖∫ t, (extZero Ω u t - mollify ρ (extZero Ω u) t) * φ t‖ ≤
      R * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
  set U := extZero Ω u
  have hU : LocallyIntegrable U volume := locallyIntegrable_indicator_L2 hΩ.measurableSet u
  set C := (‖g 0‖ + ‖g 1‖) * l2norm φ
  have hC : 0 ≤ C := by unfold C l2norm; positivity
  have hmc : Continuous (mollify ρ U) :=
    hρs.continuous_convolution_left _ hρc hU
  have hUφ : Integrable (fun t => U t * φ t) :=
    hU.integrable_smul_right_of_hasCompactSupport hφ.continuous hφs
  have hmφ : Integrable (fun t => mollify ρ U t * φ t) :=
    (hmc.mul hφ.continuous).integrable_of_hasCompactSupport (hφs.mul_left)
  have hUφz : ∀ z, Integrable (fun t => U t * φ (t + z)) := fun z =>
    hU.integrable_smul_right_of_hasCompactSupport (hφ.continuous.comp ((continuous_id.add continuous_const : Continuous fun x => x + z)))
      (hφs.comp_homeomorph (Homeomorph.addRight z))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  -- Fubini
  set L' : Set ℂ := (fun p : ℂ × ℂ => p.1 - p.2) '' (tsupport φ ×ˢ tsupport ρ)
  have hL' : IsCompact L' := (hφs.prod hρs).image (by fun_prop)
  set F : ℂ → ℂ → ℂ := fun x z => ρ z • U (x - z) * φ x with hF
  have hFeq : ∀ x z, F x z = ρ z • L'.indicator U (x - z) * φ x := by
    intro x z
    by_cases hz : z ∈ tsupport ρ
    · by_cases hx : x ∈ tsupport φ
      · have : x - z ∈ L' := ⟨(x, z), ⟨hx, hz⟩, rfl⟩
        simp [F, this]
      · simp [F, image_eq_zero_of_notMem_tsupport hx]
    · simp [F, image_eq_zero_of_notMem_tsupport hz]
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h1 := Integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure ℂ)) (ν := volume) hρi
      ((integrable_indicator_iff hL'.measurableSet).mpr (hU.integrableOn_isCompact hL'))
    obtain ⟨Mφ, hMφ⟩ := hφs.exists_bound_of_continuous hφ.continuous
    have h2 := h1.mul_bdd (c := Mφ) (g := fun p : ℂ × ℂ => φ p.1)
      (hφ.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hMφ p.1)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, hFeq]
  have hG : ∀ z, ∫ x, F x z = ρ z • ∫ t, U t * φ (t + z) := by
    intro z
    simp only [hF]
    simp_rw [smul_mul_assoc]
    rw [integral_smul]
    congr 1
    have := integral_sub_right_eq_self (μ := volume) (fun x => U x * φ (x + z)) z
    simpa using this
  have hGi : Integrable (fun z => ρ z • ∫ t, U t * φ (t + z)) := by
    have := hFint.integral_prod_right
    simp_all
  have hm : ∫ x, mollify ρ U x * φ x = ∫ z, ρ z • ∫ t, U t * φ (t + z) := by
    have h1 : ∀ x, mollify ρ U x * φ x = ∫ z, F x z := by
      intro x
      simp  [mollify, convolution_def, hF]
      rw [integral_mul_const]
    simp_rw [h1]
    rw [integral_integral_swap hFint]
    simp_all
  have hu : ∫ t, U t * φ t = ∫ z, ρ z • ∫ t, U t * φ t := by
    rw [integral_smul_const, hρ1, one_smul]
  have hdiff : ∫ t, (U t - mollify ρ U t) * φ t =
      -∫ z, ρ z • ∫ t, U t * (φ (t + z) - φ t) := by
    simp_rw [sub_mul]
    rw [integral_sub hUφ hmφ, hm, hu, ← integral_sub (hρi.smul_const _) hGi, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [mul_sub]
    rw [integral_sub (hUφz z) hUφ, smul_sub, ← smul_sub]
    simp only [smul_sub, neg_sub]
  rw [hdiff, norm_neg]
  calc ‖∫ z, ρ z • ∫ t, U t * (φ (t + z) - φ t)‖ ≤ ∫ z, ρ z * (R * C) := by
        refine norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall fun z => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hρ0 z)]
        by_cases hz : z ∈ tsupport ρ
        · gcongr
          tauto
          refine (pairing_translate_le hΩ hg hφ hφs z
            (fun s hs t ht => hseg z hz s hs t ht)).trans ?_
          rw [mul_assoc]
          gcongr
          tauto
        · simp [image_eq_zero_of_notMem_tsupport hz]
    _ = R * (‖g 0‖ + ‖g 1‖) * l2norm φ := by
        rw [integral_mul_const, hρ1, one_mul, mul_assoc]

lemma l2norm_nonneg (f : ℂ → ℂ) : 0 ≤ l2norm f := ENNReal.toReal_nonneg



/-- Duality against compactly supported smooth tests on an open set. -/
theorem l2norm_le_of_pairing {W : Set ℂ} (hW : IsOpen W) {F : ℂ → ℂ}
    (hF : MemLp F 2 volume) (hFW : ∀ x ∉ W, F x = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ‖∫ x, F x * φ x‖ ≤ C * l2norm φ) : l2norm F ≤ C := by
  let f : L2 W := (hF.restrict W).toLp F
  have hn : ‖f‖ = l2norm F := by
    have he : W.indicator F = F := funext fun x => by by_cases hx : x ∈ W <;> simp [hx, hFW]
    rw [Lp.norm_toLp, l2norm, ← eLpNorm_indicator_eq_eLpNorm_restrict hW.measurableSet, he]
  have hle : ∀ v : L2 W, ‖inner ℂ f v‖ ≤ C * ‖v‖ := by
    have hc : IsClosed {v : L2 W | ‖inner ℂ f v‖ ≤ C * ‖v‖} :=
      isClosed_le (innerSL ℂ f).continuous.norm (continuous_const.mul continuous_norm)
    intro v
    apply closure_minimal _ hc (dense_l2_tests hW v)
    rintro _ ⟨φ, hφ, rfl⟩
    change ‖inner ℂ f _‖ ≤ _
    rw [norm_inner_symm, inner_toLp_test hφ, lpIntegralPair_apply, Lp.norm_toLp]
    have hi : ∫ x in W, f x * conj (φ x) = ∫ x, F x * conj (φ x) := by
      calc
        _ = ∫ x in W, F x * conj (φ x) :=
          integral_congr_ae ((hF.restrict W).coeFn_toLp.mono fun x hx => by rw [hx])
        _ = _ := by
          rw [← integral_indicator hW.measurableSet]
          congr 1; ext x
          by_cases hx : x ∈ W <;> simp [hx, hFW]
    have hφW : W.indicator φ = φ := funext fun x => by
      by_cases hx : x ∈ W
      · simp [hx]
      · simp [hx, image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))]
    rw [hi, ← eLpNorm_indicator_eq_eLpNorm_restrict hW.measurableSet, hφW]
    simpa only [l2norm, show (fun x => conj (φ x)) = star φ from rfl, eLpNorm_star] using
      h _ hφ.conj.1 hφ.conj.2.1 hφ.conj.2.2
  have hff := hle f
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, hn] at hff
  rcases eq_or_lt_of_le (l2norm_nonneg F) with he | hp
  · linarith
  exact le_of_mul_le_mul_right hff hp

lemma memLp_indicator_of_continuous {W : Set ℂ} (hW : MeasurableSet W)
    (hWb : Bornology.IsBounded W) {f : ℂ → ℂ} (hf : Continuous f) :
    MemLp (W.indicator f) 2 volume := by
  obtain ⟨M, hM⟩ := hWb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  rw [memLp_indicator_iff_restrict hW]
  haveI : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr hWb.measure_lt_top.ne
  refine MemLp.of_bound hf.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  exact hM x (subset_closure hx)

/-- **Mollifier estimate.** If all segments `t - s z` (`t ∈ W`, `z ∈ supp ρ`, `s ∈ [0,1]`) stay
in `Ω`, then `‖1_W (U - ρ ⋆ U)‖₂ ≤ R (‖g₀‖ + ‖g₁‖)`. -/
theorem l2norm_indicator_sub_mollify_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω}
    {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g) {W : Set ℂ} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ z ∈ tsupport ρ, ‖z‖ ≤ R)
    (hseg : ∀ t ∈ W, ∀ z ∈ tsupport ρ, ∀ s ∈ Icc (0 : ℝ) 1, t - s • z ∈ Ω) :
    MemLp (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) 2 volume ∧
    l2norm (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) ≤
      R * (‖g 0‖ + ‖g 1‖) := by
  have hU :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet u
  have hmc : Continuous (mollify ρ (extZero Ω u)) :=
    hρs.continuous_convolution_left _ hρc hU
  have hmem : MemLp (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) 2 volume := by
    rw [show (fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) =
      extZero Ω u - mollify ρ (extZero Ω u) from rfl, indicator_sub']
    exact ((memLp_extZero hΩ.measurableSet u).indicator hW.measurableSet).sub
      (memLp_indicator_of_continuous hW.measurableSet hWb hmc)
  refine ⟨hmem, l2norm_le_of_pairing hW hmem (fun x hx => by simp_all) (by positivity) ?_⟩
  intro φ hφ hφs hφW
  have heq : ∫ x, (W.indicator fun x => extZero Ω u x - mollify ρ (extZero Ω u) x) x * φ x =
      ∫ x, (extZero Ω u x - mollify ρ (extZero Ω u) x) * φ x := by
    congr 1; ext x
    by_cases hx : x ∈ W
    simp_all
    · have := fun h => hx (hφW h)
      simp [image_eq_zero_of_notMem_tsupport this]
  rw [heq]
  exact pairing_mollify_le hΩ hg hφ hφs hρc hρs hρ0 hρ1 hR
    (fun z hz s hs t ht => hseg t (hφW ht) z hz s hs)

end PolyaNeumann

end
