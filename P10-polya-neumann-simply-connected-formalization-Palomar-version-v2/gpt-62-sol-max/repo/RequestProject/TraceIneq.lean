module

public import RequestProject.HerglotzGreen
public import RequestProject.HerglotzPoincare
public import RequestProject.ReconChordArc

/-! The trace estimate follows from Green's formula tested with a boundary
multiplier assembled from the local increasing directions of the graphs. -/

@[expose] public section
open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- A linear coordinate with positive tangential derivative near each point of
    the boundary. Its scale is chosen so that the derivative is at least one. -/
private lemma exists_boundary_direction (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    {p : ℂ} (hp : p ∈ frontier Ω) : ∃ r > 0, ∃ c : ℂ,
      ∀ t, γ t ∈ ball p r → DifferentiableAt ℝ γ t → 1 ≤ (c * deriv γ t).re := by
  obtain ⟨s, _, rfl⟩ := hγ.image ▸ hp
  obtain ⟨ε, hε, hεπ, c, _, k, hk, h⟩ := local_boundary_coordinate hL hγ s
  obtain ⟨K, hK⟩ := hγ.lipschitz
  let U := Ioo (s - ε) (s + ε)
  let V := Icc (s - π) (s + π) \ U
  have hs : s ∈ U := ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩
  have hV : IsCompact V := isCompact_Icc.diff isOpen_Ioo
  have hnot : γ s ∈ (γ '' V)ᶜ := by
    rintro ⟨t, ⟨ht, htu⟩, he⟩
    have hdiff : |t - s| < 2 * π := abs_lt.mpr (by constructor <;> linarith [ht.1, ht.2, Real.pi_pos])
    exact htu (hγ.eq_of_eq hdiff he ▸ hs)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (hV.image hK.continuous).isClosed.isOpen_compl _ hnot
  refine ⟨r, hr, (k : ℂ)⁻¹ * c, fun t ht hdt => ?_⟩
  let t' := toIcoMod Real.two_pi_pos (s - π) t
  have ht' : t' ∈ Ico (s - π) (s + π) := by
    simpa only [show s - π + 2 * π = s + π by ring] using
      toIcoMod_mem_Ico Real.two_pi_pos (s - π) t
  have heq : γ t' = γ t := by dsimp [t']; rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have htu : t' ∈ U := by
    by_contra hn
    exact hball ht ⟨t', ⟨Ico_subset_Icc_self ht', hn⟩, heq⟩
  let d := t - t'
  have hper x : γ (x + d) = γ x := by
    dsimp [d, t']; rw [toIcoMod, sub_sub_cancel]
    exact (hγ.periodic.zsmul _) _
  have hdt' : HasDerivAt γ (deriv γ t) t' := by
    have he : t' + d = t := by dsimp [d]; ring
    have hda : HasDerivAt γ (deriv γ t) (t' + d) := he ▸ hdt.hasDerivAt
    have hd : HasDerivAt (fun x : ℝ => x + d) 1 t' := (hasDerivAt_id t').add_const d
    simpa only [Function.comp_def, hper, one_smul] using hda.scomp t' hd
  let f (x : ℝ) := (c * γ x).re - k * x
  have hmono : MonotoneOn f U := fun x hx y hy hxy => by
    have hh := h x hx y hy hxy
    simp only [mul_sub, Complex.sub_re] at hh
    dsimp [f]; linarith
  have hdf : HasDerivAt f ((c * deriv γ t).re - k) t' := by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t' (hdt'.const_mul c)
    simpa only [f, Pi.sub_def, Function.comp_def, id_eq, mul_one, Complex.reCLM_apply] using
      hd.sub ((hasDerivAt_id t').const_mul k)
  have hdb := hmono.derivWithin_nonneg (x := t')
  rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htu), hdf.deriv] at hdb
  rw [mul_assoc, ← Complex.ofReal_inv, Complex.re_ofReal_mul, inv_mul_eq_div, le_div_iff₀ hk, one_mul]
  linarith

set_option maxHeartbeats 440000 in
/-- Patching the local directions using nonnegative bumps. -/
private lemma exists_boundary_multiplier (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) : ∃ (Y : ℂ → ℂ) (L : NNReal) (M : ℝ),
      LipschitzWith L Y ∧ (∀ z, ‖Y z‖ ≤ M) ∧
      ∀ t, DifferentiableAt ℝ γ t → 1 ≤ (Y (γ t) * deriv γ t).re := by
  classical
  choose r hr c hc using fun p : frontier Ω => exists_boundary_direction hL hγ p.property
  let U (p : frontier Ω) := ball (p : ℂ) (r p / 2)
  have hcompact :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨S, hS⟩ := hcompact.elim_finite_subcover U (fun _ => isOpen_ball) (fun p hp =>
    mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (half_pos (hr ⟨p, hp⟩))⟩)
  let B (p : frontier Ω) : ContDiffBump (p : ℂ) := ⟨r p / 2, r p, by linarith [hr p], by linarith [hr p]⟩
  let F (p : frontier Ω) (z : ℂ) := (B p z : ℂ) * c p
  let Y := ∑ p ∈ S, F p
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := by
    have hF p : ContDiff ℝ (⊤ : ℕ∞) (F p) :=
      (Complex.ofRealCLM.contDiff.comp (B p).contDiff).mul contDiff_const
    have he : Y = fun z => ∑ p ∈ S, F p z := funext fun _ => Finset.sum_apply _ _ _
    rw [he]
    exact ContDiff.sum fun p _ => hF p
  have hYc : HasCompactSupport Y :=
    HasCompactSupport.finset_sum fun p _ => show HasCompactSupport
      ((Complex.ofReal ∘ B p) * fun _ => c p) from
        ((B p).hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  obtain ⟨L, hL'⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hYc hY (by simp)
  obtain ⟨M, hM⟩ := hYc.exists_bound_of_continuous hY.continuous
  refine ⟨Y, L, M, hL', hM, fun t ht => ?_⟩
  have hd p : B p (γ t) ≤ (F p (γ t) * deriv γ t).re := by
    unfold F
    rw [mul_assoc, Complex.re_ofReal_mul]
    by_cases hmem : γ t ∈ ball (p : ℂ) (r p)
    · exact le_mul_of_one_le_right (B p).nonneg (hc p t hmem ht)
    · rw [(B p).zero_of_le_dist (le_of_not_gt hmem), zero_mul]
  obtain ⟨p, hp, hpt⟩ : ∃ p ∈ S, γ t ∈ U p := by simpa using hS (hγ.mem_frontier t)
  have h1 := (B p).one_of_mem_closedBall (ball_subset_closedBall hpt)
  calc
    1 = B p (γ t) := h1.symm
    _ ≤ ∑ i ∈ S, B i (γ t) := Finset.single_le_sum (fun i _ => (B i).nonneg) hp
    _ ≤ ∑ i ∈ S, (F i (γ t) * deriv γ t).re := Finset.sum_le_sum (fun i _ => hd i)
    _ = _ := by simp [Y, Finset.sum_mul, Complex.re_sum]

lemma dbar_mul_of_differentiableAt {F G : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    dbar (fun x => F x * G x) z = F z * dbar G z + G z * dbar F z := by
  unfold dbar
  rw [(hF.hasFDerivAt.fun_mul hG.hasFDerivAt).fderiv]
  grind [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma norm_dbar_le_half (F : ℂ → ℂ) (z : ℂ) :
    ‖dbar F z‖ ≤ (‖fderiv ℝ F z 1‖ + ‖fderiv ℝ F z Complex.I‖) / 2 := by
  unfold dbar
  rw [norm_div, Complex.norm_ofNat]
  gcongr
  refine (norm_add_le _ _).trans ?_
  simp

lemma fderiv_conj_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ (fun x => conj (f x)) z w = conj (fderiv ℝ f z w) := by
  have := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := f z)).comp z hf.hasFDerivAt
  rw [show (fun x => conj (f x)) = (Complex.conjCLE.toContinuousLinearMap ∘ f) from rfl,
    this.fderiv]
  rfl

lemma norm_dbar_normSq_mul_le {f Y : ℂ → ℂ} {z : ℂ} {LY : NNReal} {M : ℝ}
    (hf : DifferentiableAt ℝ f z) (hY : DifferentiableAt ℝ Y z) (hYL : LipschitzWith LY Y)
    (hYM : ‖Y z‖ ≤ M) :
    ‖dbar (fun x => (f x * conj (f x)) * Y x) z‖ ≤
      ‖f z‖ ^ 2 * LY + M * (‖f z‖ ^ 2 / 2 + gradSq f z) := by
  have hcf : DifferentiableAt ℝ (fun x => conj (f x)) z :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z hf
  have hN : DifferentiableAt ℝ (fun x => f x * conj (f x)) z := hf.mul hcf
  rw [dbar_mul_of_differentiableAt hN hY, dbar_mul_of_differentiableAt hf hcf]
  set a := ‖fderiv ℝ f z 1‖
  set b := ‖fderiv ℝ f z Complex.I‖
  have h1 : ‖dbar f z‖ ≤ (a + b) / 2 := norm_dbar_le_half f z
  have h2 : ‖dbar (fun x => conj (f x)) z‖ ≤ (a + b) / 2 := by
    refine (norm_dbar_le_half _ z).trans ?_
    rw [fderiv_conj_apply hf, fderiv_conj_apply hf, Complex.norm_conj, Complex.norm_conj]
  have h3 := norm_dbar_le hYL z
  have hM0 := (norm_nonneg _).trans hYM
  have hgs : gradSq f z = a ^ 2 + b ^ 2 := rfl
  have hfz : ‖f z * conj (f z)‖ = ‖f z‖ ^ 2 := by rw [norm_mul, Complex.norm_conj]; ring
  calc ‖f z * conj (f z) * dbar Y z + Y z * (f z * dbar (fun x => conj (f x)) z +
        conj (f z) * dbar f z)‖
      ≤ ‖f z‖ ^ 2 * LY + M * (‖f z‖ * (a + b)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hfz]; gcongr
        · rw [norm_mul]
          refine mul_le_mul hYM ?_ (norm_nonneg _) hM0
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg (f z)]
    _ ≤ _ := by
        gcongr
        rw [hgs]
        nlinarith [sq_nonneg (‖f z‖ - (a + b)), sq_nonneg (a - b)]

/-- **Trace inequality** on a bounded Lipschitz domain: for bounded Lipschitz `f`,
`∫₀^{2π} |f(γ θ)|² dθ ≤ C (∫_Ω |f|² + ∫_Ω |∇f|²)`. -/
theorem trace_sq_le (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ) (Kf : NNReal), LipschitzWith Kf f → ∀ B : ℝ,
      (∀ z, ‖f z‖ ≤ B) →
      ∫ θ in (0:ℝ)..(2 * π), ‖f (γ θ)‖ ^ 2 ≤
        C * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq f z) := by
  have hΩfin := hb.measure_lt_top (μ := volume)
  obtain ⟨Y, LX, M, hYL, hYM, hdir⟩ := exists_boundary_multiplier hb hL hγ
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hM0 := (norm_nonneg _).trans (hYM 0)
  refine ⟨2 * (LX + M), by positivity, fun f Kf hf B hB => ?_⟩
  have hB0 := (norm_nonneg _).trans (hB 0)
  have hcf : LipschitzWith Kf (fun z => conj (f z)) :=
    (Complex.isometry_conj.lipschitz.comp hf).weaken (by simp)
  have hcfB : ∀ z, ‖conj (f z)‖ ≤ B := fun z => by simp_all
  obtain ⟨KN, hKN⟩ := lipschitzWith_mul_of_bounded hf hcf hB hcfB
  have hNB : ∀ z, ‖f z * conj (f z)‖ ≤ B * B := fun z => by
    rw [norm_mul]; exact mul_le_mul (hB z) (hcfB z) (norm_nonneg _) hB0
  obtain ⟨KΦ, hKΦ⟩ := lipschitzWith_mul_of_bounded hKN hYL hNB hYM
  have hΦB : ∀ z, ‖f z * conj (f z) * Y z‖ ≤ B * B * M := fun z => by
    rw [norm_mul]; exact mul_le_mul (hNB z) (hYM z) (norm_nonneg _) (by positivity)
  have hG := integral_boundary_eq_dbar_of_bounded hb hL hγ hKΦ hΦB
  have hint := intervalIntegrable_comp_mul_deriv hKγ hKΦ.continuous
  have hbd : (∫ θ in (0:ℝ)..(2 * π), ‖f (γ θ)‖ ^ 2) ≤
      (∫ θ in (0:ℝ)..(2 * π), (f (γ θ) * conj (f (γ θ)) * Y (γ θ)) * deriv γ θ).re := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
    apply intervalIntegral.integral_mono_ae_restrict (by positivity)
      (((hf.continuous.comp hKγ.continuous).norm.pow 2).intervalIntegrable 0 (2 * π))
      ⟨Complex.reCLM.integrable_comp hint.1, Complex.reCLM.integrable_comp hint.2⟩
    filter_upwards [ae_restrict_of_ae (hKγ.ae_differentiableAt (μ := volume))] with θ hθ
    simp only [Complex.reCLM_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
    exact le_mul_of_one_le_right (sq_nonneg _) (hdir θ hθ)
  rw [hG] at hbd
  have hdint : IntegrableOn (fun z => dbar (fun x => f x * conj (f x) * Y x) z) Ω := by
    refine Measure.integrableOn_of_bounded (M := KΦ) hΩfin.ne
      (measurable_dbar _).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    exact norm_dbar_le hKΦ z
  -- integrability of the interior majorant
  have hfsq : IntegrableOn (fun z => ‖f z‖ ^ 2) Ω :=
    Measure.integrableOn_of_bounded (M := B ^ 2) hΩfin.ne
      (hf.continuous.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB z) 2)
  have hgsq : IntegrableOn (gradSq f) Ω := by
    refine Measure.integrableOn_of_bounded (M := 2 * Kf ^ 2) hΩfin.ne ?_
      (Eventually.of_forall fun z => ?_)
    · unfold gradSq
      fun_prop
    · have hD := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := z)
      have h1 : ‖fderiv ℝ f z 1‖ ≤ Kf := by
        simpa using (fderiv ℝ f z).le_of_opNorm_le hD 1
      have h2 : ‖fderiv ℝ f z Complex.I‖ ≤ Kf := by
        simpa using (fderiv ℝ f z).le_of_opNorm_le hD Complex.I
      unfold gradSq
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (fderiv ℝ f z 1), norm_nonneg (fderiv ℝ f z Complex.I)]
  have hmaj : ∫ z in Ω, ‖dbar (fun x => f x * conj (f x) * Y x) z‖ ≤
      (LX + M) * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq f z) := by
    have hI1 : IntegrableOn (fun z => ‖f z‖ ^ 2 * LX) Ω := hfsq.mul_const _
    have hI3 := hfsq.div_const 2
    have hI2 : IntegrableOn (fun z => M * (‖f z‖ ^ 2 / 2 + gradSq f z)) Ω :=
      (hI3.add hgsq).const_mul M
    have hle : ∫ z in Ω, ‖dbar (fun x => f x * conj (f x) * Y x) z‖ ≤
        ∫ z in Ω, (‖f z‖ ^ 2 * LX + M * (‖f z‖ ^ 2 / 2 + gradSq f z)) := by
      refine integral_mono_ae hdint.norm ?_ ?_
      · exact hI1.add hI2
      · filter_upwards [ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume)),
          ae_restrict_of_ae (hYL.ae_differentiableAt (μ := volume))] with z h1 h2
        exact norm_dbar_normSq_mul_le h1 h2 hYL (hYM z)
    refine hle.trans ?_
    rw [integral_add hI1 hI2, integral_const_mul, integral_add hI3 hgsq, integral_mul_const,
      integral_div]
    have hf0 : 0 ≤ ∫ z in Ω, ‖f z‖ ^ 2 := integral_nonneg fun z => by positivity
    have hg0 : 0 ≤ ∫ z in Ω, gradSq f z := integral_nonneg fun z => by unfold gradSq; positivity
    nlinarith [LX.coe_nonneg]
  calc
    _ ≤ ‖2 * Complex.I * ∫ z in Ω, dbar (fun x => f x * conj (f x) * Y x) z‖ :=
      hbd.trans (Complex.re_le_norm _)
    _ ≤ 2 * ((LX + M) * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq f z)) := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      gcongr
      exact (norm_integral_le_integral_norm _).trans hmaj
    _ = _ := by ring

end PolyaNeumann
end
