module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Two opposite-phase paths

Step 1 of the proof of the contraction at unit frequency (Proposition 3.9 and the
tube inclusion (3.17)).  With the tent profile `𝖿 = tent L₀` we set
`γ₁ ≡ v₀` and `γ₂(r) = v₀ + α 𝖿(clamp (r - σ)) ξ`, where `clamp` is the constant extension
outside `[σ, σ + L₀]`.  The drift gap
`Δ(α) = ∫₀^{L₀} ξ · (b(v₀ + α 𝖿(t) ξ) - b(v₀)) dt` is continuous, vanishes at `α = 0`, and
satisfies `Δ(1/2) ≥ (m + 2π)/2 > π` by the unit-direction coercivity of `b`; the intermediate
value theorem gives `α ∈ (0, 1/2)` with `Δ(α) = π`.

This file also introduces the literal source notions `HasCurveSpeedOn` (Euclidean speed bound
at differentiable interior times) and `phaseCenter`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/- A finite set of breakpoints cuts every compact interval into finitely many consecutive
pieces with no breakpoint in the interior of a piece. -/
theorem isContinuousPiecewiseC1_of_breakpoints {n : ℕ} (γ : ℝ → PDE.Vec n)
    (hγ : Continuous γ) (S : Finset ℝ)
    (hS : ∀ x y, x < y → (∀ s ∈ S, ¬ (x < s ∧ s < y)) → ContDiffOn ℝ 1 γ (Icc x y)) :
    IsContinuousPiecewiseC1 γ := by
  refine ⟨hγ, fun a b hab => ?_⟩
  obtain ⟨N, t, ht, h0, hl, hno⟩ : ∃ (N : ℕ) (t : Fin (N + 2) → ℝ), StrictMono t ∧ t 0 = a ∧ t (Fin.last (N + 1)) = b ∧
      ∀ i : Fin (N + 1), ∀ s ∈ S, ¬ (t i.castSucc < s ∧ s < t i.succ) := by
      classical
      set T : Finset ℝ := insert a (insert b (S.filter fun s => a < s ∧ s < b)) with hT
      have hmemT : ∀ x, x ∈ T ↔ x = a ∨ x = b ∨ (x ∈ S ∧ a < x ∧ x < b) := by
        intro x; simp [hT, Finset.mem_filter]
      have hcard : 2 ≤ T.card := by
        have : ({a, b} : Finset ℝ) ⊆ T := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (hmemT _).2 (Or.inl rfl)
          · exact (hmemT _).2 (Or.inr (Or.inl rfl))
        calc 2 = ({a, b} : Finset ℝ).card := by
              rw [Finset.card_pair hab.ne]
          _ ≤ T.card := Finset.card_le_card this
      obtain ⟨N, hN⟩ : ∃ N, T.card = N + 2 := ⟨T.card - 2, by omega⟩
      let t : Fin (N + 2) ↪o ℝ := T.orderEmbOfFin hN
      have hmem : ∀ i, t i ∈ T := fun i => Finset.orderEmbOfFin_mem T hN i
      have hbd : ∀ i, a ≤ t i ∧ t i ≤ b := by
        intro i
        rcases (hmemT _).1 (hmem i) with h | h | ⟨_, h1, h2⟩
        · rw [h]; exact ⟨le_rfl, hab.le⟩
        · rw [h]; exact ⟨hab.le, le_rfl⟩
        · exact ⟨h1.le, h2.le⟩
      have hsurj : ∀ x ∈ T, ∃ j, t j = x := by
        intro x hx
        have : x ∈ Set.range t := by
          rw [Finset.range_orderEmbOfFin T hN]; exact hx
        exact this
      refine ⟨N, t, t.strictMono, ?_, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := hsurj a ((hmemT _).2 (Or.inl rfl))
        apply le_antisymm
        · rw [← hj]; exact t.monotone (Fin.zero_le _)
        · exact (hbd 0).1
      · obtain ⟨j, hj⟩ := hsurj b ((hmemT _).2 (Or.inr (Or.inl rfl)))
        apply le_antisymm
        · exact (hbd _).2
        · rw [← hj]; exact t.monotone (Fin.le_last _)
      · intro i s hs ⟨h1, h2⟩
        have hsT : s ∈ T := (hmemT _).2 (Or.inr (Or.inr
          ⟨hs, lt_of_le_of_lt (hbd _).1 h1, lt_of_lt_of_le h2 (hbd _).2⟩))
        obtain ⟨j, hj⟩ := hsurj s hsT
        rw [← hj] at h1 h2
        have h1' := t.lt_iff_lt.1 h1
        have h2' := t.lt_iff_lt.1 h2
        rw [Fin.lt_def] at h1' h2'
        simp at h1' h2'
        omega


    /- Continuity and affine/`C¹` behaviour between consecutive breakpoints give a continuous
    piecewise `C¹` curve in the sense of `IsContinuousPiecewiseC1`. -/
  refine ⟨N, t, ht, h0, hl, fun i => hS _ _ (ht (Fin.castSucc_lt_succ)) (hno i)⟩

/- The Euclidean dot product with `ξ` as a continuous linear functional. -/
noncomputable def dotCLM {d } (ξ : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, ξ i • ContinuousLinearMap.proj i

@[simp]
theorem dotCLM_apply {d } (ξ w : PDE.Vec d) : dotCLM ξ w = PDE.vecDot ξ w := by
  classical
  unfold dotCLM PDE.vecDot
  simp

/- The line `r ↦ v₀ + h(r) ξ` with `h` `α`-Lipschitz has Euclidean speed at most `α`
wherever it is differentiable. -/
theorem speed_line_le {d } (ξ v0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (h : ℝ → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (hlip : ∀ r r', |h r - h r'| ≤ α * |r - r'|) (r : ℝ)
    (hdiff : DifferentiableAt ℝ (fun r => v0 + h r • ξ) r) :
    PDE.vecEuclideanNorm (deriv (fun r => v0 + h r • ξ) r) ≤ α := by
  have hhfun : h = fun r => dotCLM ξ (v0 + h r • ξ - v0) := by
    funext r
    simp only [add_sub_cancel_left, map_smul, dotCLM_apply, smul_eq_mul]
    have : PDE.vecDot ξ ξ = 1 := hξ
    rw [this, mul_one]
  have hhd : DifferentiableAt ℝ h r := by
    rw [hhfun]
    exact (dotCLM ξ).differentiableAt.comp r (hdiff.sub_const v0)
  have hL : LipschitzWith α.toNNReal h := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hα]
    exact hlip x y
  have hbd : ‖deriv h r‖ ≤ α := by
    have := norm_deriv_le_of_lipschitz (f := h) (x₀ := r) hL
    simpa [Real.coe_toNNReal _ hα] using this
  rw [((HasDerivAt.smul_const hhd.hasDerivAt ξ).const_add v0).deriv, PDE.vecEuclideanNorm_smul]
  have h1 : PDE.vecEuclideanNorm ξ = 1 := by
    unfold PDE.vecEuclideanNorm; rw [hξ, Real.sqrt_one]
  rw [h1, mul_one]
  simpa using hbd


/-! ## The clamped tent -/

/- The tent profile extended by `0` outside `[0, L₀]`, the source's constant extension. -/
noncomputable def tentPulse (L0 t : ℝ) : ℝ := tent L0 (max 0 (min L0 t))

theorem tent_zero {L0 : ℝ} (h : 0 ≤ L0) : tent L0 0 = 0 := by
  simp [tent, h]

theorem tent_self {L0 : ℝ} (h : 0 ≤ L0) : tent L0 L0 = 0 := by
  simp [tent, h]

theorem continuous_tent (L0 : ℝ) : Continuous (tent L0) := by
  unfold tent; fun_prop

theorem continuous_tentPulse (L0 : ℝ) : Continuous (tentPulse L0) := by
  unfold tentPulse
  exact (continuous_tent L0).comp (by fun_prop)

theorem tent_nonneg {L0 t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ L0) : 0 ≤ tent L0 t := by
  unfold tent
  exact le_min h0 (le_min zero_le_one (by linarith))

theorem tentPulse_nonneg {L0 : ℝ} (h : 0 ≤ L0) (t : ℝ) : 0 ≤ tentPulse L0 t :=
  tent_nonneg (le_max_left _ _) (max_le h (min_le_left _ _))

theorem tentPulse_le_one (L0 t : ℝ) : tentPulse L0 t ≤ 1 := by
    exact (
  (min_le_right _ _).trans (min_le_left _ _)
  )

theorem abs_tent_sub_tent_le (L0 x y : ℝ) : |tent L0 x - tent L0 y| ≤ |x - y| := by
  unfold tent
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le le_rfl ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) ?_)
  rw [show L0 - x - (L0 - y) = -(x - y) by ring, abs_neg]

theorem abs_tentPulse_sub_le (L0 x y : ℝ) : |tentPulse L0 x - tentPulse L0 y| ≤ |x - y| := by
  unfold tentPulse
  refine (abs_tent_sub_tent_le _ _ _).trans ?_
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

/- Between consecutive breakpoints the clamped tent is affine. -/
theorem continuous_vecDot_right {d } (ξ : PDE.Vec d) : Continuous (PDE.vecDot ξ) := by
  have : PDE.vecDot ξ = dotCLM ξ := by funext w; simp
  rw [this]; exact (dotCLM ξ).continuous

theorem vecDot_smul_right {d } (ξ w : PDE.Vec d) (c : ℝ) :
    PDE.vecDot ξ (c • w) = c * PDE.vecDot ξ w := by
  rw [← dotCLM_apply, map_smul, dotCLM_apply, smul_eq_mul]

/-! ## The integral of the tent and the drift gap -/

noncomputable def driftGap {d } (ξ v0 : PDE.Vec d) (b : PDE.Vec d → PDE.Vec d)
    (L0 α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L0,
    (PDE.vecDot ξ (b (v0 + (α * tent L0 t) • ξ)) - PDE.vecDot ξ (b v0))

theorem continuous_driftGap {d : ℕ} (ξ v0 : PDE.Vec d) {b : PDE.Vec d → PDE.Vec d}
    (hb : Continuous b) (L0 : ℝ) : Continuous (driftGap ξ v0 b L0) := by
  unfold driftGap
  have hc := continuous_tent L0
  have hp : Continuous fun p : ℝ × ℝ => v0 + (p.1 * tent L0 p.2) • ξ := by
    have h2 : Continuous fun p : ℝ × ℝ => tent L0 p.2 := hc.comp continuous_snd
    fun_prop
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (α t : ℝ) =>
      PDE.vecDot ξ (b (v0 + (α * tent L0 t) • ξ)) - PDE.vecDot ξ (b v0)) ?_ 0 L0
  exact ((continuous_vecDot_right ξ).comp (hb.comp hp)).sub continuous_const

/- The pointwise coercivity increment: `ξ · (b(v₀ + a f ξ) - b(v₀)) ≥ m a f` for `a, f ≥ 0`. -/
theorem drift_increment_ge {d m b}
    (hb : IsSmoothDrift b) (hco : HasUnitDirectionDriftCoercivity m b)
    (ξ v0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) {f α } (hf : 0 ≤ f) (hα : 0 ≤ α) :
    m * α * f ≤ PDE.vecDot ξ (b (v0 + (α * f) • ξ)) - PDE.vecDot ξ (b v0) := by
  have hbd := hb.differentiable (by simp)
  have h1 : PDE.vecEuclideanNorm ξ = 1 := by
    unfold PDE.vecEuclideanNorm; rw [hξ, Real.sqrt_one]
  let k : ℝ → ℝ := fun a => PDE.vecDot ξ (b (v0 + (a * f) • ξ)) - m * a * f
  have hk : ∀ a, HasDerivAt k
      (PDE.vecDot ξ ((fderiv ℝ b (v0 + (a * f) • ξ)) ((1 * f) • ξ)) - m * 1 * f) a := by
    intro a
    have hu :=
      (HasDerivAt.smul_const ((hasDerivAt_id a).mul_const f) ξ).const_add v0
    have hb' := (hbd (v0 + (a * f) • ξ)).hasFDerivAt.comp_hasDerivAt a hu
    have hd := (dotCLM ξ).hasFDerivAt.comp_hasDerivAt a hb'
    have hlin :=
      ((hasDerivAt_id a).const_mul m).mul_const f
    have hs := HasDerivAt.sub hd hlin
    convert hs using 1
    · funext a; simp [k]
    · simp only [dotCLM_apply]
  have hmono : Monotone k := by
    refine monotone_of_deriv_nonneg (fun a => (hk a).differentiableAt) fun a => ?_
    rw [(hk a).deriv]
    have := hco (v0 + (a * f) • ξ) ξ h1
    rw [map_smul]
    simp only [one_mul, mul_one, vecDot_smul_right]
    nlinarith
  have := hmono hα
  simp only [k, zero_mul, zero_smul, add_zero, mul_zero] at this
  linarith


theorem driftGap_ge {d m b}
    (hb : IsSmoothDrift b) (hco : HasUnitDirectionDriftCoercivity m b)
    (ξ v0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) {L0 : ℝ} (hL0 : 2 ≤ L0) {α : ℝ}
    (hα : 0 ≤ α) : m * α * (L0 - 1) ≤ driftGap ξ v0 b L0 α := by
  have hcont : Continuous fun t : ℝ =>
      PDE.vecDot ξ (b (v0 + (α * tent L0 t) • ξ)) - PDE.vecDot ξ (b v0) := by
    have hb := hb.continuous
    have hc := continuous_tent L0
    have hp : Continuous fun t : ℝ => v0 + (α * tent L0 t) • ξ := by fun_prop
    exact ((continuous_vecDot_right ξ).comp (hb.comp hp)).sub continuous_const
  have hlow : Continuous fun t : ℝ => m * α * tent L0 t := by
    have := continuous_tent L0; fun_prop
  have hmono := intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ L0)
    (hlow.intervalIntegrable (μ := MeasureTheory.volume) 0 L0)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 L0)
    (fun t ht => drift_increment_ge hb hco ξ v0 hξ (tent_nonneg ht.1 ht.2) hα)
  have _h_inl_32 : ∫ t in (0 : ℝ)..L0, tent L0 t = L0 - 1 := by
    have hc := continuous_tent L0
    have hi : ∀ a b, IntervalIntegrable (tent L0) MeasureTheory.volume a b :=
      fun a b => hc.intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 L0),
      ← intervalIntegral.integral_add_adjacent_intervals (hi 1 (L0 - 1)) (hi (L0 - 1) L0)]
    have e1 : ∫ t in (0 : ℝ)..1, tent L0 t = ∫ t in (0 : ℝ)..1, t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      simp only [tent, min_def]; split_ifs <;> linarith [ht.1, ht.2]
    have e2 : ∫ t in (1 : ℝ)..(L0 - 1), tent L0 t = ∫ t in (1 : ℝ)..(L0 - 1), (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [tent, min_def]; split_ifs <;> linarith [ht.1, ht.2]
    have e3 : ∫ t in (L0 - 1)..L0, tent L0 t = ∫ t in (L0 - 1)..L0, (L0 - t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [tent, min_def]; split_ifs <;> linarith [ht.1, ht.2]
    have e4 : ∫ t in (L0 - 1)..L0, (L0 - t) = ∫ t in (0 : ℝ)..1, t := by
      have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) (a := L0 - 1) (b := L0) L0
      simpa using this
    rw [e1, e2, e3, e4]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_const_mul, _h_inl_32] at hmono
  exact hmono

/- The source intermediate value step: `Δ(α) = π` for some `α ∈ (0, 1/2)`. -/
theorem euclideanBall_subset_of_close {d : ℕ} {m Lb : ℝ} (hLb : 0 < Lb) (hm : 0 < m)
    {D : Set (PDE.Vec d)} {v0 c : PDE.Vec d}
    (hfit : PDE.euclideanBall v0 (blockOuter Lb) ⊆ D)
    (hc : PDE.vecEuclideanNorm (c - v0) ≤ 1 / 2) :
    PDE.euclideanBall c (blockEta m Lb) ⊆ D := by
  intro x hx
  have hη := blockEta_pos hm hLb
  have hη4 : blockEta m Lb ≤ 1 / 4 := blockEta_le_quarter
  have hρ := blockRho_pos hLb
  have hout : 0 < blockOuter Lb := by unfold blockOuter; positivity
  apply hfit
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hout]
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hη] at hx
  have hsplit : x - v0 = (x - c) + (c - v0) := by abel
  have h1 := PDE.vecEuclideanNorm_add_le (x - c) (c - v0)
  rw [← hsplit] at h1
  have : 1 ≤ blockOuter Lb := by unfold blockOuter; linarith
  linarith


theorem exists_opposite_paths {d } (m Lb σ : ℝ) (hm : 0 < m) (hmLb : m ≤ Lb)
    (D b)
    (hb : IsSmoothDrift b) (hbounds : HasTransportBounds m Lb b)
    (ξ v0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hfit : PDE.euclideanBall v0 (blockOuter Lb) ⊆ D) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧
      let γ1 : ℝ → PDE.Vec d := fun _ => v0
      let γ2 : ℝ → PDE.Vec d := fun r =>
        v0 + (α * tent (blockL0 m) (max 0 (min (blockL0 m) (r - σ)))) • ξ
      IsContinuousPiecewiseC1 γ1 ∧ IsContinuousPiecewiseC1 γ2 ∧
      γ1 σ = v0 ∧ γ2 σ = v0 ∧
      γ1 (σ + blockL0 m) = v0 ∧ γ2 (σ + blockL0 m) = v0 ∧
      HasCurveSpeedOn (1 / 2) γ1 σ (σ + blockL0 m) ∧
      HasCurveSpeedOn (1 / 2) γ2 σ (σ + blockL0 m) ∧
      (∀ r : ℝ,
        PDE.euclideanBall (γ1 r) (blockEta m Lb) ⊆ D ∧
        PDE.euclideanBall (γ2 r) (blockEta m Lb) ⊆ D) ∧
      phaseCenter ξ b γ2 σ (σ + blockL0 m) -
        phaseCenter ξ b γ1 σ (σ + blockL0 m) = Real.pi := by
  have hLb := hm.trans_le hmLb
  have hL0 := two_le_blockL0 hm
  obtain ⟨α, hα0, hα1, hΔ⟩ : ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧ driftGap ξ v0 b (blockL0 m) α = Real.pi := by
    have hco := hbounds.2
    have hL0 := two_le_blockL0 hm
    have hge := driftGap_ge hb hco ξ v0 hξ hL0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hval : m * (1 / 2) * (blockL0 m - 1) = (m + 2 * Real.pi) / 2 := by
      unfold blockL0; field_simp; ring
    rw [hval] at hge
    have hpi := Real.pi_pos
    have hcont := (continuous_driftGap ξ v0 hb.continuous (blockL0 m)).continuousOn
      (s := Set.Icc (0 : ℝ) (1 / 2))
    have hmem : Real.pi ∈ Set.Ioo (driftGap ξ v0 b (blockL0 m) 0)
        (driftGap ξ v0 b (blockL0 m) (1 / 2)) := by
      have _h_inl_32 (ξ v0 : PDE.Vec d) (b : PDE.Vec d → PDE.Vec d) (L0 : ℝ) : driftGap ξ v0 b L0 0 = 0 := by
        simp [driftGap]
      rw [_h_inl_32]; constructor <;> linarith
    obtain ⟨α, hα, hαeq⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont hmem
    exact ⟨α, hα.1, hα.2, hαeq⟩
  refine ⟨α, hα0, hα1, ?_⟩
  intro γ1 γ2
  set L0 := blockL0 m with hL0def
  have hξ1 : PDE.vecEuclideanNorm ξ = 1 := by
    unfold PDE.vecEuclideanNorm; rw [hξ, Real.sqrt_one]
  have hγ2 : γ2 = fun r => v0 + (α * tentPulse L0 (r - σ)) • ξ := rfl
  have hγ2c : Continuous γ2 := by
    have h2 : Continuous fun r : ℝ => tentPulse L0 (r - σ) :=
      (continuous_tentPulse L0).comp (by fun_prop)
    rw [hγ2]; fun_prop
  -- piecewise C¹
  have hpc1 : IsContinuousPiecewiseC1 γ1 :=
    isContinuousPiecewiseC1_of_breakpoints γ1 continuous_const ∅ fun x y _ _ =>
      (contDiffOn_const (c := v0))
  have hpc2 : IsContinuousPiecewiseC1 γ2 := by
    refine isContinuousPiecewiseC1_of_breakpoints γ2 hγ2c {σ, σ + 1, σ + L0 - 1, σ + L0}
      fun x y hxy hno => ?_
    have n0 := hno σ (by simp)
    have n1 := hno (σ + 1) (by simp)
    have n2 := hno (σ + L0 - 1) (by simp)
    have n3 := hno (σ + L0) (by simp)
    obtain ⟨c, e, hce⟩ : ∃ c e : ℝ, ∀ r ∈ Icc x y, tentPulse L0 (r - σ) = c + e * r := by
      by_cases ha : x < σ
      · have hy : y ≤ σ := by by_contra hc; exact n0 ⟨ha, not_le.1 hc⟩
        refine ⟨0, 0, fun r hr => ?_⟩
        have := hr.2
        simp only [tentPulse, tent, min_def, max_def]
        split_ifs <;> linarith
      by_cases hb : x < σ + 1
      · have hy : y ≤ σ + 1 := by by_contra hc; exact n1 ⟨hb, not_le.1 hc⟩
        refine ⟨-σ, 1, fun r hr => ?_⟩
        have := hr.2
        have := hr.1
        simp only [tentPulse, tent, min_def, max_def]
        split_ifs <;> linarith
      by_cases hc : x < σ + L0 - 1
      · have hy : y ≤ σ + L0 - 1 := by by_contra hc'; exact n2 ⟨hc, not_le.1 hc'⟩
        refine ⟨1, 0, fun r hr => ?_⟩
        have := hr.2
        have := hr.1
        simp only [tentPulse, tent, min_def, max_def]
        split_ifs <;> linarith
      by_cases hd : x < σ + L0
      · have hy : y ≤ σ + L0 := by by_contra hc'; exact n3 ⟨hd, not_le.1 hc'⟩
        refine ⟨σ + L0, -1, fun r hr => ?_⟩
        have := hr.2
        have := hr.1
        simp only [tentPulse, tent, min_def, max_def]
        split_ifs <;> linarith
      · refine ⟨0, 0, fun r hr => ?_⟩
        have := hr.1
        simp only [tentPulse, tent, min_def, max_def]
        split_ifs <;> linarith
    have hsm : ContDiff ℝ 1 fun r : ℝ => v0 + (α * (c + e * r)) • ξ := by fun_prop
    refine hsm.contDiffOn.congr fun r hr => ?_
    rw [hγ2]
    simp only [hce r hr]
  have hp0 : tent L0 (max 0 (min L0 (σ - σ))) = 0 := by
    rw [sub_self, min_eq_right (by linarith), max_self]; exact tent_zero (by linarith)
  have hp1 : tent L0 (max 0 (min L0 (σ + L0 - σ))) = 0 := by
    rw [add_sub_cancel_left, min_self, max_eq_right (by linarith)]; exact tent_self (by linarith)
  have hlip : ∀ r r' : ℝ, |α * tentPulse L0 (r - σ) - α * tentPulse L0 (r' - σ)| ≤
      α * |r - r'| := by
    intro r r'
    rw [← mul_sub, abs_mul, abs_of_pos hα0]
    refine mul_le_mul_of_nonneg_left ?_ hα0.le
    refine (abs_tentPulse_sub_le L0 _ _).trans ?_
    rw [sub_sub_sub_cancel_right]
  have hnorm0 : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 := by
    unfold PDE.vecEuclideanNorm PDE.vecNormSq PDE.vecDot; simp
  have hdev : ∀ r, PDE.vecEuclideanNorm (γ2 r - v0) ≤ α := by
    intro r
    have : γ2 r - v0 = (α * tentPulse L0 (r - σ)) • ξ := by
      show v0 + (α * tentPulse L0 (r - σ)) • ξ - v0 = _
      exact add_sub_cancel_left _ _
    rw [this, PDE.vecEuclideanNorm_smul, hξ1, mul_one, abs_of_nonneg (mul_nonneg hα0.le
      (tentPulse_nonneg (by linarith) _))]
    calc α * tentPulse L0 (r - σ) ≤ α * 1 :=
          mul_le_mul_of_nonneg_left (tentPulse_le_one _ _) hα0.le
      _ = α := mul_one α
  refine ⟨hpc1, hpc2, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show v0 + (α * tent L0 (max 0 (min L0 (σ - σ)))) • ξ = v0
    rw [hp0]; simp
  · show v0 + (α * tent L0 (max 0 (min L0 (σ + L0 - σ)))) • ξ = v0
    rw [hp1]; simp
  · intro r _ hd
    have : deriv γ1 r = 0 := deriv_const r v0
    show PDE.vecEuclideanNorm (deriv (fun _ => v0) r) ≤ 1 / 2
    rw [deriv_const, hnorm0]; norm_num
  · intro r _ hd
    have : PDE.vecEuclideanNorm (deriv γ2 r) ≤ α :=
      speed_line_le ξ v0 hξ (fun r => α * tentPulse L0 (r - σ)) α hα0.le hlip r hd
    linarith
  · intro r
    refine ⟨?_, ?_⟩
    · refine euclideanBall_subset_of_close hLb hm hfit ?_
      show PDE.vecEuclideanNorm (v0 - v0) ≤ 1 / 2
      rw [sub_self, hnorm0]; norm_num
    · exact euclideanBall_subset_of_close hLb hm hfit ((hdev r).trans hα1.le)
  · have _h_inl_41 : phaseCenter ξ b (fun r => v0 + (α * tent L0 (max 0 (min L0 (r - σ)))) • ξ) σ (σ + L0) -
      phaseCenter ξ b (fun _ => v0) σ (σ + L0) = driftGap ξ v0 b L0 α := by
      have hb := hb.continuous
      have hc := continuous_tentPulse L0
      have hA : Continuous fun r : ℝ =>
          PDE.vecDot ξ (b (v0 + (α * tent L0 (max 0 (min L0 (r - σ)))) • ξ)) := by
        have h2 : Continuous fun r : ℝ => tentPulse L0 (r - σ) := hc.comp (by fun_prop)
        have hp : Continuous fun r : ℝ => v0 + (α * tentPulse L0 (r - σ)) • ξ := by fun_prop
        exact (continuous_vecDot_right ξ).comp (hb.comp hp)
      unfold phaseCenter
      rw [← intervalIntegral.integral_sub (hA.intervalIntegrable (μ := MeasureTheory.volume) _ _)
        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)]
      unfold driftGap
      have := intervalIntegral.integral_comp_add_left
        (fun r : ℝ => PDE.vecDot ξ (b (v0 + (α * tent L0 (max 0 (min L0 (r - σ)))) • ξ))
          - PDE.vecDot ξ (b v0)) (a := 0) (b := L0) σ
      rw [add_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      have : tentPulse L0 t = tent L0 t := by
        have h0 := ht.1
        have h1 := ht.2
        unfold tentPulse
        rw [min_eq_right h1, max_eq_right h0]
      simp only [tentPulse] at this
      simp only [add_sub_cancel_left, this]
    rw [_h_inl_41]
    exact hΔ

end HypoellipticAleksandrov.KineticAleksandrov.Decay
