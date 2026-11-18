module

public import RequestProject.TraceIneq
public import RequestProject.SmallEnergyForm
public import RequestProject.PeriodicForm
public import Mathlib.Analysis.Complex.Isometry

/-!
# Small-energy Schur positivity and admissible Herglotz data

For small `E = k² > 0` on a bounded Lipschitz domain `Ω` containing a disc `B(z₁, r)`:
* `herglotz_imSchur_nonneg`: the Schur complement `C(v_a)` is nonnegative on Herglotz densities
  with zero mean over `Ω` and vanishing negative modes at `z₁`;
* `exists_admissible_herglotzVec`: every `w ∈ ℓ²` can be shifted along `e₀` to `y_a(z₀)` for an
  admissible density `a`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology InnerProductSpace Interval

noncomputable section

namespace PolyaNeumann

local instance factTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

section Basic

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

private lemma intervalIntegrable_conj' {f : ℝ → ℂ} {b c : ℝ}
    (hf : IntervalIntegrable f volume b c) :
    IntervalIntegrable (fun t => conj (f t)) volume b c :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

private lemma integrableOn_herglotzCoeff (hb : Bornology.IsBounded Ω)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    IntegrableOn (herglotzCoeff k a m) Ω :=
  Measure.integrableOn_of_bounded hb.measure_lt_top.ne
    (continuous_herglotzCoeff ha k m).aestronglyMeasurable
    (Eventually.of_forall (norm_herglotzCoeff_le k m))

private lemma integrable_herglotzCoeff_sq (hb : Bornology.IsBounded Ω)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) (m : ℤ) :
    Integrable (fun z => ‖herglotzCoeff k a m z‖ ^ 2) (volume.restrict Ω) :=
  integrable_norm_sq_of_bounded hb.measure_lt_top (continuous_herglotzCoeff ha k m)
    (norm_herglotzCoeff_le k m)

private theorem integral_ball_herglotzCoeff (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) (z₁ : ℂ) (r : ℝ) :
    ∫ z in ball z₁ r, herglotzCoeff k a m z =
      (∫ u in ball (0 : ℂ) r, planeWave k u 0) * herglotzCoeff k a m z₁ := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hpw : ∀ φ : ℝ, ∫ z in ball z₁ r, planeWave k z φ =
      planeWave k z₁ φ * ∫ u in ball (0 : ℂ) r, planeWave k u 0 := fun φ => by
    have htr : (fun u => z₁ + u) ⁻¹' ball z₁ r = ball (0 : ℂ) r := by ext u; simp [dist_eq_norm]
    rw [← (measurePreserving_add_left volume z₁).setIntegral_preimage_emb
      (measurableEmbedding_addLeft z₁) (fun z => planeWave k z φ) (ball z₁ r), htr]
    simp_rw [planeWave_add]
    rw [integral_const_mul]
    congr 1
    set c : Circle := Circle.exp (-φ)
    have hrot : ∀ u, rotation c u = u * Complex.exp (-(φ * Complex.I)) := fun u => by
      rw [rotation_apply, Circle.coe_exp]; push_cast; ring_nf
    have hpre : (rotation c) ⁻¹' ball (0 : ℂ) r = ball (0 : ℂ) r := by
      ext u; simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
    have hm := (LinearIsometryEquiv.measurePreserving (rotation c)).setIntegral_preimage_emb
      (rotation c).toHomeomorph.measurableEmbedding (fun v => planeWave k v 0) (ball (0 : ℂ) r)
    rw [hpre] at hm
    exact (setIntegral_congr_fun measurableSet_ball fun u _ => by simp [planeWave, hrot]).trans hm
  set e : ℝ → ℂ := fun φ => Complex.exp (-((m : ℂ) * φ * Complex.I)) with he
  have hai : Integrable a (volume.restrict (Ioc 0 (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp ha
  haveI : IsFiniteMeasure (volume.restrict (ball z₁ r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  set F : ℂ → ℝ → ℂ := fun z φ => e φ * (a φ * planeWave k z φ) with hF
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hai.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc1 : Continuous fun p : ℂ × ℝ => e p.2 := by rw [he]; fun_prop
      have hc2 : Continuous fun p : ℂ × ℝ => planeWave k p.1 p.2 := by unfold planeWave; fun_prop
      exact hc1.aestronglyMeasurable.mul
        (hai.aestronglyMeasurable.comp_snd.mul hc2.aestronglyMeasurable)
    · simp [Function.uncurry, hF, he, Complex.norm_exp, norm_planeWave]
  unfold herglotzCoeff
  simp_rw [intervalIntegral.integral_of_le h2π]
  rw [integral_const_mul, integral_integral_swap hFi]
  have hin : ∀ φ, ∫ z in ball z₁ r, F z φ =
      (e φ * (a φ * planeWave k z₁ φ)) * ∫ u in ball (0 : ℂ) r, planeWave k u 0 := fun φ => by
    simp only [hF]; rw [integral_const_mul, integral_const_mul, hpw]; ring
  simp_rw [hin, integral_mul_const]
  simp only [he]; ring

private lemma hasSum_sq_herglotzCoeff (ha : IsDirDensity a) (k : ℝ) (z : ℂ) :
    HasSum (fun m : ℤ => ‖herglotzCoeff k a m z‖ ^ 2)
      ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ ^ 2) := by
  have hb : MemLp (planeWave k z) ⊤ (volume.restrict (Ioc 0 (2 * π))) :=
    memLp_top_of_bound (continuous_planeWave k z).aestronglyMeasurable 1
      (Eventually.of_forall fun φ => (norm_planeWave k z φ).le)
  have hm : MemLp (fun φ => a φ * planeWave k z φ) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    (ha.mul' (r := 2) hb).congr_norm (ha.aestronglyMeasurable.mul hb.aestronglyMeasurable)
      (Eventually.of_forall fun _ => by simp [mul_comm])
  simp_rw [herglotzCoeff_eq_fourierCoeffOn]
  convert hasSum_sq_fourierCoeffOn Real.two_pi_pos hm using 1
  rw [smul_eq_mul, sub_zero]
  congr 1
  exact intervalIntegral.integral_congr fun _ _ => by simp [norm_planeWave]

private theorem herglotz_modes_small (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a, IsDirDensity a → ∀ k : ℝ, k ^ 2 ≤ δ →
      (∀ j : ℕ, 1 ≤ j → herglotzCoeff k a (-(j : ℤ)) z₁ = 0) →
      ∫ z in Ω, herglotzCoeff k a 0 z = 0 →
        ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 ≤
            C * k ^ 2 * ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2 ∧
          (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) + ∫ z in Ω, ‖herglotzCoeff k a (-2) z‖ ^ 2 ≤
            C * k ^ 4 * ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2 := by
  obtain ⟨CB, hCB, hPB⟩ := poincare_herglotzCoeff_ball hb hL hr hball
  obtain ⟨cP, hcP, hP⟩ := poincare_herglotzCoeff hb hL
  set c := CB / 2
  have hc : 0 < c := by positivity
  refine ⟨cP + 2 * c * cP, min 1 (min (1 / (4 * c)) (1 / (2 * c * cP))), by positivity,
    by positivity, fun a ha k hk hz hmean => ?_⟩
  have hai := ha.intervalIntegrable
  let N : ℕ → ℝ := fun j => ∫ z in Ω, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2
  set A1 := ∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2
  have hA10 : 0 ≤ A1 := integral_nonneg fun _ => by positivity
  have hN0 : ∀ j, 0 ≤ N j := fun _ => integral_nonneg fun _ => by positivity
  have hkδ1 : k ^ 2 ≤ 1 := hk.trans (min_le_left _ _)
  have hkδ2 : k ^ 2 ≤ 1 / (4 * c) := hk.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkδ3 : k ^ 2 ≤ 1 / (2 * c * cP) := hk.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hck : c * k ^ 2 ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * c)] at hkδ2; linarith
  have hchain : ∀ j : ℕ, N (j + 1) ≤ c * k ^ 2 * (N j + N (j + 2)) := fun j => by
    have h0 : ∫ z in ball z₁ r, herglotzCoeff k a (-((j + 1 : ℕ) : ℤ)) z = 0 := by
      rw [integral_ball_herglotzCoeff hai, hz (j + 1) (by omega), mul_zero]
    have key := hPB a hai k _ h0
    have e1 : -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) := by push_cast; ring
    have e2 : -((j + 1 : ℕ) : ℤ) - 1 = -((j + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, integral_add (integrable_herglotzCoeff_sq hb hai k _)
      (integrable_herglotzCoeff_sq hb hai k _)] at key
    exact key.trans_eq (by simp [N, c]; ring)
  set T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, N (i + 1) with hT
  have hTbound : ∀ n, T n ≤ 2 * (c * k ^ 2) * (N 0 + N (n + 1)) := fun n => by
    have hsum : T n ≤ c * k ^ 2 * ((∑ i ∈ Finset.range n, N i) +
        ∑ i ∈ Finset.range n, N (i + 2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hchain i
    have h1 : ∑ i ∈ Finset.range n, N i ≤ N 0 + T n := by
      linarith [Finset.sum_range_succ' N n, Finset.sum_range_succ N n, hN0 n]
    have h3 : ∑ i ∈ Finset.range n, N (i + 2) ≤ T n + N (n + 1) := by
      linarith [Finset.sum_range_succ' (fun i => N (i + 1)) n,
        Finset.sum_range_succ (fun i => N (i + 1)) n, hN0 1]
    have hTn : 0 ≤ T n := Finset.sum_nonneg fun _ _ => hN0 _
    have hck0 : 0 ≤ c * k ^ 2 := by positivity
    nlinarith
  have hsumN : Summable N := by
    set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ ^ 2
    haveI : IsFiniteMeasure (volume.restrict Ω) :=
      isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
    refine summable_of_sum_range_le (c := A * (volume Ω).toReal) hN0 fun n => ?_
    simp only [N, ← integral_finset_sum _ fun j _ => integrable_herglotzCoeff_sq hb hai k _]
    calc ∫ z in Ω, ∑ j ∈ Finset.range n, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2
        ≤ ∫ _ in Ω, A := integral_mono (integrable_finset_sum _ fun j _ =>
            integrable_herglotzCoeff_sq hb hai k _) (integrable_const _) fun z => by
          rw [show ∑ j ∈ Finset.range n, ‖herglotzCoeff k a (-(j : ℤ)) z‖ ^ 2 =
            ∑ m ∈ (Finset.range n).map ⟨fun j : ℕ => -(j : ℤ), fun i j h => by simpa using h⟩,
              ‖herglotzCoeff k a m z‖ ^ 2 by rw [Finset.sum_map]; rfl]
          exact sum_le_hasSum _ (fun _ _ => by positivity) (hasSum_sq_herglotzCoeff ha k z)
      _ = A * (volume Ω).toReal := by
          rw [integral_const, smul_eq_mul, Measure.real_def,
            Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm]
  have h12 : N 1 + N 2 ≤ 2 * (c * k ^ 2) * N 0 := by
    have hlim : Tendsto (fun n => 2 * (c * k ^ 2) * (N 0 + N (n + 1))) atTop
        (nhds (2 * (c * k ^ 2) * (N 0 + 0))) :=
      ((hsumN.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)).const_add _).const_mul _
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨2, fun n hn => ?_⟩)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hle : N 1 + N 2 ≤ T (m + 2) := by
      simp only [hT, Finset.sum_range_succ', zero_add]
      linarith [Finset.sum_nonneg (s := Finset.range m) fun i _ => hN0 (i + 1 + 1 + 1)]
    exact hle.trans (hTbound (m + 2))
  have hF0 := hP a hai k 0 hmean
  rw [integral_add (integrable_herglotzCoeff_sq hb hai k _)
    (integrable_herglotzCoeff_sq hb hai k _)] at hF0
  simp only [zero_add, zero_sub] at hF0
  change N 0 ≤ cP * (k ^ 2 / 2 * (A1 + N 1)) at hF0
  have hcc : cP * c * k ^ 4 ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c * cP)] at hkδ3
    nlinarith [sq_nonneg k, mul_pos hc hcP]
  have hN0b : N 0 ≤ cP * k ^ 2 * A1 := by
    have : N 0 ≤ cP * (k ^ 2 / 2) * A1 + cP * c * k ^ 4 * N 0 :=
      calc N 0 ≤ cP * (k ^ 2 / 2 * (A1 + N 1)) := hF0
        _ ≤ cP * (k ^ 2 / 2 * (A1 + 2 * (c * k ^ 2) * N 0)) := by gcongr; linarith [hN0 2]
        _ = _ := by ring
    nlinarith [hN0 0]
  refine ⟨?_, ?_⟩
  · change N 0 ≤ _
    exact hN0b.trans (by nlinarith [show 0 ≤ 2 * c * cP * k ^ 2 * A1 by positivity])
  · change N 1 + N 2 ≤ _
    calc N 1 + N 2 ≤ 2 * (c * k ^ 2) * N 0 := h12
      _ ≤ 2 * (c * k ^ 2) * (cP * k ^ 2 * A1) := by gcongr
      _ ≤ (cP + 2 * c * cP) * k ^ 4 * A1 := by
          nlinarith [show 0 ≤ cP * k ^ 4 * A1 by positivity]

private lemma integral_conj_deriv_mul_herglotzCoeff_neg_one (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      -(k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨K, hK⟩ := lipschitzWith_herglotzCoeff ha k (-1)
  have hK' : LipschitzWith (1 * K) (fun z => conj (herglotzCoeff k a (-1) z)) :=
    Complex.isometry_conj.lipschitz.comp hK
  have hB' : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ := fun z => by
    rw [Complex.norm_conj]; exact norm_herglotzCoeff_le k (-1) z
  have hg := integral_boundary_eq_dbar_of_bounded hb hL hγ hK' hB'
  have hd : ∀ z, dbar (fun x => conj (herglotzCoeff k a (-1) x)) z =
      conj (-(Complex.I * k / 2) * herglotzCoeff k a 0 z) := fun z => by
    obtain ⟨h1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
    have hcF : HasFDerivAt (fun x => conj (herglotzCoeff k a (-1) x))
        (Complex.conjCLE.toContinuousLinearMap.comp _) z :=
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z h1
    have hdbar := dbar_eq_of_hasFDerivAt
      (α := conj (-(Complex.I * k / 2) * herglotzCoeff k a (-1 - 1) z))
      (β := conj (-(Complex.I * k / 2) * herglotzCoeff k a (-1 + 1) z)) hcF fun w => by
        simp only [ContinuousLinearMap.comp_apply, h1L, ContinuousLinearEquiv.coe_coe,
          Complex.conjCLE_apply, map_add, map_mul, Complex.conj_conj]; ring
    rw [hdbar]; norm_num
  simp_rw [hd] at hg
  have e : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) =
      conj (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a (-1) (γ θ)) * deriv γ θ) := by
    rw [← intervalIntegral_conj]
    exact intervalIntegral.integral_congr fun _ _ => by simp [mul_comm]
  rw [e, hg, integral_conj, map_mul, Complex.conj_conj, integral_const_mul]
  simp only [map_mul, map_ofNat, Complex.conj_I]
  ring_nf; rw [Complex.I_sq]; ring

private theorem integral_herglotzConormal (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal k a γ θ =
      -((k : ℂ) ^ 2) * ∫ z in Ω, herglotzCoeff k a 0 z := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hi1 : IntervalIntegrable (fun θ => conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ))
      volume 0 (2 * π) := by
    refine (intervalIntegrable_conj' (intervalIntegrable_comp_mul_deriv hKγ
      (Complex.continuous_conj.comp (continuous_herglotzCoeff ha k (-1))))).congr fun _ _ => ?_
    simp [mul_comm]
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ (continuous_herglotzCoeff ha k 1)
  have h1 : ∫ θ in (0 : ℝ)..(2 * π), herglotzCoeff k a 1 (γ θ) * deriv γ θ =
      (k : ℂ) * ∫ z in Ω, herglotzCoeff k a 0 z := by
    obtain ⟨K, hK⟩ := lipschitzWith_herglotzCoeff ha k 1
    rw [integral_boundary_eq_dbar_of_bounded hb hL hγ hK (norm_herglotzCoeff_le k 1)]
    have hd : ∀ z, dbar (herglotzCoeff k a 1) z =
        -(Complex.I * k / 2) * herglotzCoeff k a 0 z := fun z => by
      obtain ⟨hf, hfL⟩ := herglotzCoeff_hasFDerivAt' ha k 1 z
      rw [dbar_eq_of_hasFDerivAt hf hfL]; norm_num
    simp_rw [hd]; rw [integral_const_mul]; ring_nf; rw [Complex.I_sq]; ring
  have hpt : ∀ θ, herglotzConormal k a γ θ = (k / 2 : ℂ) *
      (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) -
        herglotzCoeff k a 1 (γ θ) * deriv γ θ) := fun θ => by
    rw [herglotzConormal_eq ha]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
    integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha, h1]
  ring

private def herglotzQd (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ)

private def herglotzQ (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..θ, herglotzQd k a γ t

private lemma herglotzQd_bounded (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) {K : NNReal}
    (hK : LipschitzWith K γ) :
    AEStronglyMeasurable (herglotzQd k a γ) volume ∧
      ∀ θ, ‖herglotzQd k a γ θ‖ ≤ K * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖) :=
  ⟨(Complex.continuous_conj.comp_aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable).mul
      ((continuous_herglotzCoeff ha k (-1)).comp hK.continuous).aestronglyMeasurable,
    fun θ => by
      rw [herglotzQd, norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_deriv_le_of_lipschitz hK) (norm_herglotzCoeff_le k _ _)
        (norm_nonneg _) K.2⟩

private lemma herglotzConormal_ae_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∀ᵐ θ, herglotzConormal k a γ θ =
      -Complex.I * deriv (fun s => herglotzCoeff k a 0 (γ s)) θ + k * herglotzQd k a γ θ := by
  filter_upwards [hK.ae_differentiableAt] with θ hθ
  obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 (γ θ)
  have hd : deriv (fun s => herglotzCoeff k a 0 (γ s)) θ =
      fderiv ℝ (herglotzCoeff k a 0) (γ θ) (deriv γ θ) :=
    (h0.comp_hasDerivAt θ hθ.hasDerivAt).deriv
  rw [hd, h0L, herglotzConormal_eq ha, herglotzQd]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num]
  ring_nf; rw [Complex.I_sq]; ring

private lemma primitive_herglotzConormal_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) (θ : ℝ) :
    ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s =
      -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
        k * herglotzQ k a γ θ := by
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
  have hh : LipschitzWith (C * K) (fun s => herglotzCoeff k a 0 (γ s)) := hC.comp hK
  have hdi : IntervalIntegrable (deriv fun s => herglotzCoeff k a 0 (γ s)) volume 0 θ :=
    intervalIntegrable_of_norm_le (measurable_deriv _).aestronglyMeasurable
      (fun _ => norm_deriv_le_of_lipschitz hh) 0 θ
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  have hqi : IntervalIntegrable (herglotzQd k a γ) volume 0 θ :=
    intervalIntegrable_of_norm_le hqm (fun t => hqB t) 0 θ
  rw [intervalIntegral.integral_congr_ae
      ((herglotzConormal_ae_eq ha k hK).mono fun _ hs _ => hs),
    intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_deriv_of_lipschitz hh, herglotzQ]

private def herglotzPrincipal (Ω : Set ℂ) (γ : ℝ → ℂ) (k : ℝ) (a : ℝ → ℂ) : ℝ :=
  2 * k ^ 2 * ((∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2) +
    2 * (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) -
    3 * ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2) -
  2 * k ^ 2 * (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ).im

private theorem re_integral_herglotz_principal (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    (h0 : ∫ z in Ω, herglotzCoeff k a 0 z = 0) :
    (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal k a γ θ) *
        (2 * herglotzWave k a (γ θ) +
          Complex.I * (2 * ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s))).re =
      herglotzPrincipal Ω γ k a := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set g := herglotzConormal k a γ with hgdef
  set h : ℝ → ℂ := fun s => herglotzCoeff k a 0 (γ s) with hhdef
  set q := herglotzQd k a γ with hqdef
  set Q := herglotzQ k a γ with hQdef
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded ha k hK
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  have hcgi : IntervalIntegrable (fun θ => conj (g θ)) volume 0 (2 * π) :=
    intervalIntegrable_conj' (intervalIntegrable_of_norm_le hgm hgB _ _)
  have hQc : ContinuousOn Q (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le h2π]
    exact continuousOn_primitive_of_bound h2π hqm.restrict (fun t _ => hqB t)
  have hQL : Q (2 * π) = 0 := by
    rw [hQdef, herglotzQ]; simp only [herglotzQd]
    rw [integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha, h0, mul_zero]
  have hcg0 : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) = 0 := by
    rw [intervalIntegral_conj, hgdef, integral_herglotzConormal hb hL hγ ha, h0, mul_zero, map_zero]
  obtain ⟨CK0, hCK0⟩ := lipschitzWith_herglotzCoeff ha k 0
  have hh : LipschitzWith (CK0 * K) h := hCK0.comp hK
  have hibp : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ := by
    have hdm : AEStronglyMeasurable (fun θ => conj (deriv h θ))
        (volume.restrict (Icc 0 (2 * π))) :=
      Complex.continuous_conj.comp_aestronglyMeasurable (measurable_deriv _).aestronglyMeasurable
    have key := integral_primitive_mul_eq h2π hqm.restrict hdm
      (fun t _ => hqB t) (fun t _ => by rw [Complex.norm_conj]; exact norm_deriv_le_of_lipschitz hh)
    have hin : ∀ t, ∫ s in t..(2 * π), conj (deriv h s) = conj (h (2 * π)) - conj (h t) := fun t => by
      rw [intervalIntegral_conj, integral_deriv_of_lipschitz hh, map_sub]
    have hqi : IntervalIntegrable q volume 0 (2 * π) :=
      intervalIntegrable_of_norm_le hqm (fun t => hqB t) 0 (2 * π)
    have hci : IntervalIntegrable (fun t => q t * conj (h t)) volume 0 (2 * π) :=
      hqi.mul_continuousOn ((Complex.continuous_conj.comp
        ((continuous_herglotzCoeff ha k 0).comp hK.continuous)).continuousOn)
    rw [show ∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ =
        ∫ s in (0 : ℝ)..(2 * π), (∫ t in (0 : ℝ)..s, q t) * conj (deriv h s) from
      intervalIntegral.integral_congr fun _ _ => by rw [hQdef, herglotzQ, mul_comm], key]
    simp_rw [hin, mul_sub]
    rw [intervalIntegral.integral_sub (hqi.mul_const _) hci, intervalIntegral.integral_mul_const,
      show ∫ t in (0 : ℝ)..(2 * π), q t = Q (2 * π) from rfl, hQL, zero_mul, zero_sub]
    exact neg_inj.mpr (intervalIntegral.integral_congr fun _ _ => mul_comm _ _)
  have hX : ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ =
      ((k * ((∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) -
        ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) : ℂ) := by
    set F : ℤ → ℂ → ℂ := herglotzCoeff k a
    set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖
    obtain ⟨K1, hK1⟩ := lipschitzWith_herglotzCoeff ha k (-1)
    have hcb : ∀ z, ‖conj (F (-1) z)‖ ≤ A := fun z => by
      rw [Complex.norm_conj]; exact norm_herglotzCoeff_le k (-1) z
    obtain ⟨KΦ, hKΦ⟩ := lipschitzWith_mul_of_bounded hCK0
      (Complex.isometry_conj.lipschitz.comp hK1) (norm_herglotzCoeff_le k 0) hcb
    set Φ : ℂ → ℂ := fun z => F 0 z * conj (F (-1) z) with hΦ
    have hKΦ' : LipschitzWith KΦ Φ := hKΦ
    have hg := integral_boundary_eq_dbar_of_bounded hb hL hγ hKΦ' (C := A * A)
      fun z => by
        simp only [hΦ, norm_mul]
        exact mul_le_mul (norm_herglotzCoeff_le k 0 z) (hcb z) (norm_nonneg _)
          ((norm_nonneg _).trans (norm_herglotzCoeff_le k 0 0))
    have hd : ∀ z, dbar Φ z = Complex.I * k / 2 *
        ((‖F 0 z‖ ^ 2 - ‖F (-1) z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      obtain ⟨hd0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 z
      obtain ⟨hd1, h1L⟩ := herglotzCoeff_hasFDerivAt' ha k (-1) z
      rw [dbar_mul_conj hd0 h0L hd1 h1L]
      simp only [show (-1 : ℤ) + 1 = 0 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
        map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; rw [← Complex.mul_conj', ← Complex.mul_conj']; ring
    simp_rw [hd] at hg
    have e : ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ =
        conj (∫ θ in (0 : ℝ)..(2 * π), Φ (γ θ) * deriv γ θ) := by
      rw [← intervalIntegral_conj]
      exact intervalIntegral.integral_congr fun _ _ => by
        simp only [hhdef, hqdef, herglotzQd, Φ, F, map_mul, Complex.conj_conj]; ring
    rw [e, hg, integral_const_mul, integral_complex_ofReal,
      integral_sub (integrable_herglotzCoeff_sq hb ha k 0)
        (integrable_herglotzCoeff_sq hb ha k (-1))]
    simp only [F, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hgQ : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * Q θ =
      Complex.I * (∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ) +
        k * ∫ θ in (0 : ℝ)..(2 * π), conj (q θ) * Q θ := by
    have hdi : IntervalIntegrable (fun θ => conj (deriv h θ) * Q θ) volume 0 (2 * π) :=
      (intervalIntegrable_conj' (intervalIntegrable_of_norm_le
        (measurable_deriv h).aestronglyMeasurable
        (fun _ => norm_deriv_le_of_lipschitz hh) 0 (2 * π))).mul_continuousOn hQc
    have hqi : IntervalIntegrable (fun θ => conj (q θ) * Q θ) volume 0 (2 * π) :=
      (intervalIntegrable_conj' (intervalIntegrable_of_norm_le hqm hqB 0 (2 * π))).mul_continuousOn hQc
    rw [intervalIntegral.integral_congr_ae (g := fun θ =>
        Complex.I * (conj (deriv h θ) * Q θ) + (k : ℂ) * (conj (q θ) * Q θ)) ?_,
      intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    filter_upwards [herglotzConormal_ae_eq ha k hK] with θ hθ _
    rw [hgdef, hθ, hhdef, hqdef]
    simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; ring
  have hpt : ∀ θ, conj (g θ) * (2 * herglotzWave k a (γ θ) +
      Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) =
      4 * (conj (g θ) * herglotzWave k a (γ θ)) - 2 * h 0 * conj (g θ) +
        2 * Complex.I * k * (conj (g θ) * Q θ) := fun θ => by
    rw [primitive_herglotzConormal_eq ha k hK θ, herglotzWave_eq]
    ring_nf; rw [Complex.I_sq]; ring
  have hi1 : IntervalIntegrable (fun θ => conj (g θ) * herglotzWave k a (γ θ)) volume 0 (2 * π) :=
    hcgi.mul_continuousOn (by
      rw [show herglotzWave k a = herglotzCoeff k a 0 from funext (herglotzWave_eq k a)]
      exact ((continuous_herglotzCoeff ha k 0).comp hK.continuous).continuousOn)
  have hi3 : IntervalIntegrable (fun θ => conj (g θ) * Q θ) volume 0 (2 * π) :=
    hcgi.mul_continuousOn hQc
  have hI12 : IntegrableOn (fun z => ‖herglotzCoeff k a 1 z‖ ^ 2 +
      ‖herglotzCoeff k a (-1) z‖ ^ 2) Ω :=
    (integrable_herglotzCoeff_sq hb ha k 1).add (integrable_herglotzCoeff_sq hb ha k (-1))
  have hI02 : IntegrableOn (fun z => 2 * ‖herglotzCoeff k a 0 z‖ ^ 2) Ω :=
    (integrable_herglotzCoeff_sq hb ha k 0).const_mul 2
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hcgi.const_mul _)) (hi3.const_mul _),
    intervalIntegral.integral_sub (hi1.const_mul _) (hcgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcg0, hgQ, hibp,
    integral_conj_herglotzConormal_mul_wave hb hL hγ ha k, hX,
    integral_sub hI12 hI02,
    integral_add (integrable_herglotzCoeff_sq hb ha k 1)
      (integrable_herglotzCoeff_sq hb ha k (-1)),
    integral_const_mul, herglotzPrincipal]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_im, Complex.zero_re,
    Complex.zero_im]
  ring

end Basic

section SchurKernel

private def schurBeta (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : ℂ := smallB W θ - 2

private def schurKernel0 (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  if s ≤ θ then Complex.I * (volterraKernel W θ s - 1) else -(Complex.I * (volterraKernel W θ s - 1))

private def schurKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  schurKernel0 W θ s - schurBeta W θ * conj (schurBeta W s) / (smallA W : ℂ)

private def schurRho0 (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  if t ≤ θ then Complex.I * kernelRho γ E W θ t else -(Complex.I * kernelRho γ E W θ t)

private def schurRho (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ℂ :=
  schurRho0 γ E W θ t - schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

private theorem imSchur_herglotzVec (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    (hW : IsTransport γ E W) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      herglotzForm W γ E a -
        ‖∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ‖ ^ 2 /
          smallA W := by
  have hp : imPair (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      (Real.sqrt 2 : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ := by
    obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    obtain ⟨hO, -⟩ := herglotzForm_eq hK hclosed hW ha
    set V := W (2 * π)
    set v := herglotzVec ha (Real.sqrt E) (γ 0)
    have hVV : V * ContinuousLinearMap.adjoint V = 1 := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (Unitary.mem_iff.mp (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)).2
    have hR := inner_observationAdj_right hW.1 hgm hgB (radialVec W)
    rw [hO, inner_smul_right, show l2Inner (observation W (radialVec W))
        (herglotzConormal (Real.sqrt E) a γ) =
      ∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ from
        intervalIntegral.integral_congr fun θ _ => by
          simp [observation, smallB, basisVec, lp.inner_single_left] ] at hR
    have hkey : ⟪basisVec 0, (ContinuousLinearMap.adjoint V - V) v⟫_ℂ =
        ⟪radialVec W, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ := by
      have h1 : ⟪ContinuousLinearMap.adjoint V (basisVec 0),
          (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ = ⟪basisVec 0, v - V v⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply, map_sub,
          ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hVV,
          ContinuousLinearMap.one_apply]
      rw [radialVec, inner_add_left, h1, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
        inner_sub_right, inner_sub_right]
      ring
    unfold imPair
    rw [show monodromy W - ContinuousLinearMap.adjoint (monodromy W) =
      ContinuousLinearMap.adjoint V - V by simp [monodromy, V], hkey, ← hR]
    have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    linear_combination (-⟪radialVec W, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ * Complex.I) * h2
  unfold imSchur
  rw [hp, imForm_monodromy_basisVec, imForm, ← herglotzForm_eq_im hK hclosed hW ha, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rcases eq_or_ne (smallA W) 0 with h | h <;> [simp [h]; field_simp]

private lemma volterraKernel_diag (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) : volterraKernel W θ θ = 1 := by
  have hu := transport_mem_unitary hK hW hθ
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  rw [volterraKernel, ← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  simp [basisVec]

private lemma conj_volterraKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) :
    conj (volterraKernel W s θ) = volterraKernel W θ s := by
  rw [volterraKernel, volterraKernel, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left]

private lemma volterraKernel_add_end (hW : IsTransport γ E W) (θ : ℝ) :
    volterraKernel W θ (2 * π) + volterraKernel W θ 0 = smallB W θ := by
  rw [volterraKernel, volterraKernel, transport_zero_eq hW, smallB, ← inner_basisVec,
    ← inner_add_right, ← map_add, radialVec,
    ← ContinuousLinearMap.star_eq_adjoint (1 : Ell2 →L[ℂ] Ell2),
    star_one, ContinuousLinearMap.one_apply, add_comm]

private lemma smallB_end_sub (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    smallB W (2 * π) - smallB W 0 = Complex.I * smallA W := by
  have hu := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hu
  have h1 : W (2 * π) (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0)) = basisVec 0 := by
    rw [← ContinuousLinearMap.mul_apply, hu.2, ContinuousLinearMap.one_apply]
  have h2 : (ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0) : ℕ → ℂ) 0 =
      conj ((W (2 * π) (basisVec 0) : ℕ → ℂ) 0) := by
    rw [← inner_basisVec, ← inner_basisVec, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  unfold smallB radialVec smallA
  rw [transport_zero_eq hW, ContinuousLinearMap.one_apply, map_add, h1]
  simp only [lp.coeFn_add, Pi.add_apply, h2, basisVec_coord]
  apply Complex.ext <;> simp <;> ring

private lemma kernelRho_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (θ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (kernelRho γ E W θ) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW
    (ContinuousLinearMap.adjoint (W θ) (basisVec 0)) 0 ht
  simp only [transportCoeff_coord_zero] at this
  exact intervalIntegrable_conj' this

private lemma smallBDer_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) : IntervalIntegrable (smallBDer γ E W) volume 0 t := by
  have := transport_coord_intervalIntegrable' hK hW (radialVec W) 0 ht
  simp only [transportCoeff_coord_zero] at this
  exact this

private lemma schurRho0_intervalIntegrable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ s : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (schurRho0 γ E W θ) volume 0 s := by
  have hi := kernelRho_intervalIntegrable hK hW θ hs
  rcases le_or_gt s θ with hsθ | hθs
  · refine (hi.const_mul Complex.I).congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht; exact (if_pos (ht.2.trans hsθ)).symm
  · have hiθ := kernelRho_intervalIntegrable hK hW θ hθ
    refine ((hiθ.const_mul Complex.I).congr fun t ht => ?_).trans
      ((((hiθ.symm.trans hi).const_mul Complex.I).neg).congr fun t ht => ?_)
    · rw [uIoc_of_le hθ.1] at ht; exact (if_pos ht.2).symm
    · rw [uIoc_of_le hθs.le] at ht; exact (if_neg (not_le.mpr ht.1)).symm

private lemma schurKernel0_eq_integral (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ s : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel0 W θ s = schurKernel0 W θ 0 + ∫ t in (0 : ℝ)..s, schurRho0 γ E W θ t := by
  rw [show schurKernel0 W θ 0 = Complex.I * (volterraKernel W θ 0 - 1) from if_pos hθ.1]
  rcases le_or_gt s θ with hsθ | hθs
  · rw [schurKernel0, if_pos hsθ,
      intervalIntegral.integral_congr (g := fun t => Complex.I * kernelRho γ E W θ t)
        (fun t ht => by rw [uIcc_of_le hs.1] at ht; exact if_pos (ht.2.trans hsθ)),
      intervalIntegral.integral_const_mul, volterraKernel_eq_integral hK hW θ hs]
    ring
  · have hi := kernelRho_intervalIntegrable hK hW θ hs
    have hiθ := kernelRho_intervalIntegrable hK hW θ hθ
    have i1 := schurRho0_intervalIntegrable hK hW hθ hθ
    have i2 := i1.symm.trans (schurRho0_intervalIntegrable hK hW hθ hs)
    have c1 : ∫ t in (0 : ℝ)..θ, schurRho0 γ E W θ t =
        ∫ t in (0 : ℝ)..θ, Complex.I * kernelRho γ E W θ t :=
      intervalIntegral.integral_congr fun t ht => by rw [uIcc_of_le hθ.1] at ht; exact if_pos ht.2
    have c2 : ∫ t in θ..s, schurRho0 γ E W θ t =
        ∫ t in θ..s, -(Complex.I * kernelRho γ E W θ t) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hθs.le] at ht
        rcases eq_or_lt_of_le ht.1 with rfl | h
        · simp [schurRho0, kernelRho_diag hK hW hθ]
        · exact if_neg (not_le.mpr h)
    have e2 := volterraKernel_eq_integral hK hW θ hθ
    rw [volterraKernel_diag hK hW hθ] at e2
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, c1, c2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, schurKernel0, if_neg (not_le.mpr hθs),
      ← intervalIntegral.integral_interval_sub_left hi hiθ,
      volterraKernel_eq_integral hK hW θ hs]
    linear_combination (2 * Complex.I) * e2

private lemma schurBeta_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {s : ℝ}
    (hs : s ∈ Icc 0 (2 * π)) :
    schurBeta W s = schurBeta W 0 + ∫ t in (0 : ℝ)..s, smallBDer γ E W t := by
  rw [schurBeta, schurBeta, smallB_eq hK hW hs]; ring

private lemma schurKernel_eq_integral (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ s : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel W θ s = schurKernel W θ 0 + ∫ t in (0 : ℝ)..s, schurRho γ E W θ t := by
  have hi0 := schurRho0_intervalIntegrable hK hW hθ hs
  have hi1 : IntervalIntegrable (fun t => schurBeta W θ * conj (smallBDer γ E W t) /
      (smallA W : ℂ)) volume 0 s :=
    ((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hs)).const_mul _).div_const _
  unfold schurRho
  rw [intervalIntegral.integral_sub hi0 hi1, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, intervalIntegral_conj, schurKernel, schurKernel,
    schurKernel0_eq_integral hK hW hθ hs, schurBeta_eq hK hW hs, map_add]
  ring

private lemma schurKernel0_of_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hθs : θ ≤ s) :
    schurKernel0 W θ s = -(Complex.I * (volterraKernel W θ s - 1)) := by
  unfold schurKernel0
  split_ifs with h
  · obtain rfl := le_antisymm h hθs
    rw [volterraKernel_diag hK hW hθ]; ring
  · rfl

private lemma schurKernel_end_right (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    schurKernel W θ (2 * π) = schurKernel W θ 0 := by
  have ha' : (smallA W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk := volterraKernel_add_end hW θ
  have hcb : conj (schurBeta W (2 * π)) = conj (schurBeta W 0) - Complex.I * smallA W := by
    rw [show schurBeta W (2 * π) = schurBeta W 0 + Complex.I * smallA W by
      unfold schurBeta; linear_combination hb, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  unfold schurKernel
  rw [schurKernel0_of_le hK hW hθ hθ.2, show schurKernel0 W θ 0 =
    Complex.I * (volterraKernel W θ 0 - 1) from if_pos hθ.1, hcb]
  field_simp; unfold schurBeta
  linear_combination (-(Complex.I * smallA W)) * hk

private lemma schurKernel_end_left (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (ha : smallA W ≠ 0) {s : ℝ} (hs : s ∈ Icc 0 (2 * π)) :
    schurKernel W (2 * π) s = schurKernel W 0 s := by
  have ha' : (smallA W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hb := smallB_end_sub hK hW
  have hk : volterraKernel W (2 * π) s + volterraKernel W 0 s = conj (smallB W s) := by
    rw [← conj_volterraKernel W (2 * π) s, ← conj_volterraKernel W 0 s, ← map_add,
      volterraKernel_add_end hW]
  unfold schurKernel
  rw [schurKernel0_of_le hK hW ⟨le_rfl, by positivity⟩ hs.1, show schurKernel0 W (2 * π) s =
    Complex.I * (volterraKernel W (2 * π) s - 1) from if_pos hs.2]
  field_simp; unfold schurBeta; rw [map_sub, map_ofNat]
  linear_combination (Complex.I * smallA W) * hk - (conj (smallB W s) - 2) * hb

private lemma norm_schurBeta_sub_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B) {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π)) :
    ‖schurBeta W θ₁ - schurBeta W θ₂‖ ≤ B * |θ₁ - θ₂| := by
  rw [schurBeta_eq hK hW h₁, schurBeta_eq hK hW h₂, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (smallBDer_intervalIntegrable hK hW h₁)
      (smallBDer_intervalIntegrable hK hW h₂)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hB t ?_
  exact uIcc_subset_Icc h₂ h₁ (uIoc_subset_uIcc ht)

private lemma norm_schurRho_sub_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    {B : ℝ} (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {θ₁ θ₂ t : ℝ} (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π))
    (ht : t ∈ Icc 0 (2 * π)) :
    ‖schurRho γ E W θ₁ t - schurRho γ E W θ₂ t‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) * |θ₁ - θ₂| := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  set M := (K : ℝ) * (shiftConst * K) * E
  have hd : ∀ θ ∈ Icc 0 (2 * π), ‖kernelRho γ E W θ t‖ ≤ M * |θ - t| := fun θ hθ => by
    simpa [kernelRho_diag hK hW ht] using norm_kernelRho_sub_le hK hE hW hθ ht ht
  have h0' : ‖schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t‖ ≤ M * |θ₁ - θ₂| := by
    unfold schurRho0
    split_ifs with ha hb hb
    · rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
      exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
    · push_neg at hb
      calc ‖Complex.I * kernelRho γ E W θ₁ t - -(Complex.I * kernelRho γ E W θ₂ t)‖
          ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
            rw [sub_neg_eq_add, ← mul_add, norm_mul, Complex.norm_I, one_mul]
            exact norm_add_le _ _
        _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
        _ = M * |θ₁ - θ₂| := by
            rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith),
              abs_of_nonneg (by linarith)]; ring
    · push_neg at ha
      calc ‖-(Complex.I * kernelRho γ E W θ₁ t) - Complex.I * kernelRho γ E W θ₂ t‖
          ≤ ‖kernelRho γ E W θ₁ t‖ + ‖kernelRho γ E W θ₂ t‖ := by
            rw [← neg_add', ← mul_add, norm_neg, norm_mul, Complex.norm_I, one_mul]
            exact norm_add_le _ _
        _ ≤ M * |θ₁ - t| + M * |θ₂ - t| := add_le_add (hd θ₁ h₁) (hd θ₂ h₂)
        _ = M * |θ₁ - θ₂| := by
            rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith),
              abs_of_neg (by linarith)]; ring
    · rw [neg_sub_neg, ← mul_sub, norm_mul, Complex.norm_I, one_mul, norm_sub_rev]
      exact norm_kernelRho_sub_le hK hE hW h₁ h₂ ht
  have h2 : ‖(schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      B * B / |smallA W| * |θ₁ - θ₂| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (smallA W) 0 with h0 | h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (abs_pos.mpr h0)]
      calc ‖schurBeta W θ₁ - schurBeta W θ₂‖ * ‖smallBDer γ E W t‖ ≤ (B * |θ₁ - θ₂|) * B :=
            mul_le_mul (norm_schurBeta_sub_le hK hW hB h₁ h₂) (hB t ht) (norm_nonneg _)
              (by positivity)
        _ = B * B * |θ₁ - θ₂| := by ring
  rw [show schurRho γ E W θ₁ t - schurRho γ E W θ₂ t =
    (schurRho0 γ E W θ₁ t - schurRho0 γ E W θ₂ t) -
      (schurBeta W θ₁ - schurBeta W θ₂) * conj (smallBDer γ E W t) / (smallA W : ℂ) by
    unfold schurRho; ring]
  exact (norm_sub_le _ _).trans (by linarith)

private lemma norm_schurRho_le (hK : LipschitzWith K γ) (hE : 0 ≤ E) (hW : IsTransport γ E W)
    {B : ℝ} (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {θ t : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (ht : t ∈ Icc 0 (2 * π)) :
    ‖schurRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) +
      (‖schurBeta W 0‖ + B * (2 * π)) * B / |smallA W| := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hdist : |θ - t| ≤ 2 * π := abs_le.mpr ⟨by linarith [hθ.1, ht.2], by linarith [hθ.2, ht.1]⟩
  have hk : ‖kernelRho γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) := by
    have := norm_kernelRho_sub_le hK hE hW hθ ht ht
    rw [kernelRho_diag hK hW ht, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdist (by have := shiftConst_nonneg; positivity))
  have h0' : ‖schurRho0 γ E W θ t‖ ≤ K * (shiftConst * K) * E * (2 * π) := by
    unfold schurRho0; split_ifs <;> simpa [norm_mul, Complex.norm_I] using hk
  have hβ : ‖schurBeta W θ‖ ≤ ‖schurBeta W 0‖ + B * (2 * π) := by
    have := norm_schurBeta_sub_le hK hW hB hθ ⟨le_rfl, by positivity⟩
    rw [sub_zero, abs_of_nonneg hθ.1] at this
    have h3 := norm_add_le (schurBeta W 0) (schurBeta W θ - schurBeta W 0)
    rw [add_sub_cancel] at h3; nlinarith [hθ.2]
  have h1 : ‖schurBeta W θ * conj (smallBDer γ E W t) / (smallA W : ℂ)‖ ≤
      (‖schurBeta W 0‖ + B * (2 * π)) * B / |smallA W| := by
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (mul_le_mul hβ (hB t ht) (norm_nonneg _)
      (by positivity)) (abs_nonneg _)
  unfold schurRho
  exact (norm_sub_le _ _).trans (add_le_add h0' h1)

private lemma schurRho_aestronglyMeasurable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    AEStronglyMeasurable (schurRho γ E W θ) (volume.restrict (Icc 0 (2 * π))) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hi : IntervalIntegrable (schurRho γ E W θ) volume 0 (2 * π) :=
    (schurRho0_intervalIntegrable hK hW hθ hL).sub
      (((intervalIntegrable_conj' (smallBDer_intervalIntegrable hK hW hL)).const_mul _).div_const _)
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp hi).aestronglyMeasurable

private theorem norm_schurKernel_form_le (hK : LipschitzWith K γ) (hE : 0 ≤ E)
    (hW : IsTransport γ E W) (ha : smallA W ≠ 0) {B : ℝ}
    (hB : ∀ t ∈ Icc 0 (2 * π), ‖smallBDer γ E W t‖ ≤ B)
    {g : ℝ → ℂ} {Bg : ℝ} (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) (c : ℂ) :
    ‖∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s‖ ≤
      (K * (shiftConst * K) * E + B * B / |smallA W|) *
        (∫ t in (0 : ℝ)..(2 * π), ‖(∫ u in (0 : ℝ)..t, g u) - c‖) ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by positivity⟩)
  have hM : 0 ≤ (K : ℝ) * (shiftConst * K) * E + B * B / |smallA W| := by
    have := shiftConst_nonneg; positivity
  exact norm_kernel_form_le (by positivity) hM hg hgB
    (fun _ hθ => schurRho_aestronglyMeasurable hK hW hθ)
    (fun _ hθ _ ht => norm_schurRho_le hK hE hW hB hθ ht)
    (fun _ hθ _ hs => schurKernel_eq_integral hK hW hθ hs)
    (fun _ h₁ _ h₂ _ ht => norm_schurRho_sub_le hK hE hW hB h₁ h₂ ht)
    (fun _ hθ => schurKernel_end_right hK hW ha hθ)
    (fun _ hs => schurKernel_end_left hK hW ha hs) hG c

private lemma smallB_continuousOn (hW : IsTransport γ E W) :
    ContinuousOn (smallB W) (Icc 0 (2 * π)) :=
  (continuousOn_const.inner (hW.1.clm_apply continuousOn_const)).congr fun s _ => by
    beta_reduce; rw [smallB, inner_basisVec]

private lemma integral_schurKernel_mul_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {g : ℝ → ℂ} (hgi : IntervalIntegrable g volume 0 (2 * π))
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s =
      Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) - 2 * Complex.I * (∫ s in (0 : ℝ)..θ, g s) -
        schurBeta W θ * (∫ s in (0 : ℝ)..(2 * π), conj (smallB W s) * g s) / (smallA W : ℂ) := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hsub1 : uIcc 0 θ ⊆ uIcc 0 (2 * π) := by
    rw [uIcc_of_le hθ.1, uIcc_of_le hL]; exact Icc_subset_Icc le_rfl hθ.2
  have hsub2 : uIcc θ (2 * π) ⊆ uIcc 0 (2 * π) := by
    rw [uIcc_of_le hθ.2, uIcc_of_le hL]; exact Icc_subset_Icc hθ.1 le_rfl
  have hwc : ContinuousOn (volterraKernel W θ) (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL]
    exact continuousOn_const.inner ((W θ).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0)))
  have hg1 : IntervalIntegrable g volume 0 θ := hgi.mono_set hsub1
  have hg2 : IntervalIntegrable g volume θ (2 * π) := hgi.mono_set hsub2
  have hw1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
    hg1.continuousOn_mul (hwc.mono hsub1)
  have hw2 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume θ (2 * π) :=
    hg2.continuousOn_mul (hwc.mono hsub2)
  have A1 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume 0 θ :=
    ((hw1.sub hg1).const_mul Complex.I).congr fun s hs => by
      rw [uIoc_of_le hθ.1] at hs; simp only [schurKernel0, if_pos hs.2]; ring
  have A2 : IntervalIntegrable (fun s => schurKernel0 W θ s * g s) volume θ (2 * π) :=
    ((hw2.sub hg2).const_mul Complex.I).neg.congr fun s hs => by
      rw [uIoc_of_le hθ.2] at hs; simp only [schurKernel0, if_neg (not_le.mpr hs.1), Pi.neg_apply]; ring
  have I1 : ∫ s in (0 : ℝ)..θ, schurKernel0 W θ s * g s =
      Complex.I * (volterraOp W g θ - ∫ s in (0 : ℝ)..θ, g s) := by
    rw [intervalIntegral.integral_congr (g := fun s => Complex.I *
      (volterraKernel W θ s * g s - g s)) (fun s hs => by
        rw [uIcc_of_le hθ.1] at hs; simp only [schurKernel0, if_pos hs.2]; ring),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hw1 hg1]
    rfl
  have I2 : ∫ s in θ..(2 * π), schurKernel0 W θ s * g s =
      -(Complex.I * (volterraOpAdj W g θ - ∫ s in θ..(2 * π), g s)) := by
    rw [intervalIntegral.integral_congr (g := fun s => -(Complex.I *
      (volterraKernel W θ s * g s - g s))) (fun s hs => by
        rw [uIcc_of_le hθ.2] at hs; simp only [schurKernel0_of_le hK hW hθ hs.1]; ring),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hw2 hg2]
    unfold volterraOpAdj; simp only [conj_volterraKernel]
  have hsplit : ∫ s in θ..(2 * π), g s = -∫ s in (0 : ℝ)..θ, g s := by
    linear_combination (intervalIntegral.integral_add_adjacent_intervals hg1 hg2).trans hG
  have hB1 : IntervalIntegrable (fun s => conj (smallB W s) * g s) volume 0 (2 * π) :=
    hgi.continuousOn_mul (by
      rw [uIcc_of_le hL]; exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW))
  have hB2 : IntervalIntegrable (fun s => schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ)) volume 0 (2 * π) :=
    (((hB1.sub (hgi.const_mul 2)).const_mul (schurBeta W θ)).div_const (smallA W : ℂ)).congr
      fun _ _ => by simp only [schurBeta, map_sub, map_ofNat]; ring
  have hrk : ∫ s in (0 : ℝ)..(2 * π), schurBeta W θ * (conj (schurBeta W s) * g s) /
      (smallA W : ℂ) = schurBeta W θ *
        (∫ s in (0 : ℝ)..(2 * π), conj (smallB W s) * g s) / (smallA W : ℂ) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun s => conj (smallB W s) * g s - 2 * g s)
      (fun _ _ => by simp only [schurBeta, map_sub, map_ofNat]; ring),
      intervalIntegral.integral_sub hB1 (hgi.const_mul 2), intervalIntegral.integral_const_mul,
      hG, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr (g := fun s => schurKernel0 W θ s * g s -
      schurBeta W θ * (conj (schurBeta W s) * g s) / (smallA W : ℂ))
      (fun _ _ => by simp only [schurKernel]; ring),
    intervalIntegral.integral_sub (A1.trans A2) hB2, hrk,
    ← intervalIntegral.integral_add_adjacent_intervals A1 A2, I1, I2, hsplit]
  ring

private theorem re_volterra_sub_schur_eq (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) {g : ℝ → ℂ} {Bg : ℝ}
    (hg : AEStronglyMeasurable g volume) (hgB : ∀ t, ‖g t‖ ≤ Bg)
    (hG : ∫ t in (0 : ℝ)..(2 * π), g t = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable (fun θ => conj (g θ) * h θ) volume 0 (2 * π)) :
    (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ))).re -
      ‖∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * g θ‖ ^ 2 / smallA W =
    (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))).re +
      (∫ θ in (0 : ℝ)..(2 * π), conj (g θ) *
        ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s).re := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hgi : IntervalIntegrable g volume 0 (2 * π) := intervalIntegrable_of_norm_le hg hgB _ _
  have hcg : IntervalIntegrable (fun θ => conj (g θ)) volume 0 (2 * π) :=
    intervalIntegrable_conj' hgi
  set Y := ∫ θ in (0 : ℝ)..(2 * π), conj (smallB W θ) * g θ with hY
  set Φ := fun θ => ∫ s in (0 : ℝ)..(2 * π), schurKernel W θ s * g s with hΦ
  have hGcI : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ, g s) (Icc 0 (2 * π)) :=
    continuousOn_primitive_of_bound hL hg.restrict fun t _ => hgB t
  have hβcI : ContinuousOn (schurBeta W) (Icc 0 (2 * π)) :=
    (smallB_continuousOn hW).sub continuousOn_const
  have hVc : ContinuousOn (volterraOp W g) (Icc 0 (2 * π)) := by
    have hsmul : IntegrableOn (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
        (uIcc 0 (2 * π)) volume := by
      rw [uIcc_of_le hL]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp
        (intervalIntegrable_smul_of_continuousOn
          (continuousOn_adjoint_apply hW.1 (basisVec 0)) hg hgB ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩)
    have hprim : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ,
        g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) (Icc 0 (2 * π)) := by
      simpa [uIcc_of_le hL] using intervalIntegral.continuousOn_primitive_interval hsmul
    exact (continuousOn_const.inner (hW.1.clm_apply hprim)).congr fun θ hθ =>
      (inner_transport_integral hW.1 hg hgB θ ⟨le_rfl, hL⟩ hθ).symm
  have hobsc : ContinuousOn (observation W (observationAdj W g)) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  have hVadjc : ContinuousOn (volterraOpAdj W g) (Icc 0 (2 * π)) :=
    (hobsc.sub hVc).congr fun θ hθ => by
      have := volterraOp_add_adj hW.1 hg hgB hθ
      simp only [Pi.sub_apply]; linear_combination this
  have hΦc : ContinuousOn Φ (uIcc 0 (2 * π)) := by
    rw [uIcc_of_le hL]
    have hΦc' : ContinuousOn (fun θ => Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) -
        2 * Complex.I * (∫ s in (0 : ℝ)..θ, g s) - schurBeta W θ * Y / (smallA W : ℂ))
        (Icc 0 (2 * π)) :=
      (((continuousOn_const.mul (hVc.sub hVadjc)).sub (continuousOn_const.mul hGcI)).sub
        ((hβcI.mul continuousOn_const).div_const _))
    exact hΦc'.congr fun θ hθ => integral_schurKernel_mul_eq hK hW hgi hG hθ
  have hGc : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ, g s) (uIcc 0 (2 * π)) := by
    rwa [uIcc_of_le hL]
  have hβc : ContinuousOn (schurBeta W) (uIcc 0 (2 * π)) := by rwa [uIcc_of_le hL]
  have i1 : IntervalIntegrable (fun θ => conj (g θ) *
      (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s))) volume 0 (2 * π) :=
    ((hh.const_mul 2).add (hcg.mul_continuousOn
      ((hGc.const_smul (2 : ℂ)).const_smul Complex.I))).congr fun _ _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  have i2 : IntervalIntegrable (fun θ => conj (g θ) * Φ θ) volume 0 (2 * π) :=
    hcg.mul_continuousOn hΦc
  have i3 : IntervalIntegrable (fun θ => conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ))
      volume 0 (2 * π) := ((hcg.mul_continuousOn hβc).mul_const Y).div_const _
  have hpt : ∀ θ ∈ uIcc 0 (2 * π), conj (g θ) *
      (2 * h θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)) =
      conj (g θ) * (2 * h θ + Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) + conj (g θ) * Φ θ +
        conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) := fun θ hθ => by
    rw [uIcc_of_le hL] at hθ
    simp only [hΦ, integral_schurKernel_mul_eq hK hW hgi hG hθ, hY]; ring
  have h3 : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * schurBeta W θ * Y / (smallA W : ℂ) =
      conj Y * Y / (smallA W : ℂ) := by
    have hB1 : IntervalIntegrable (fun s => conj (smallB W s) * g s) volume 0 (2 * π) :=
      hgi.continuousOn_mul (by
        rw [uIcc_of_le hL]; exact Complex.continuous_conj.comp_continuousOn (smallB_continuousOn hW))
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
    congr 2
    rw [intervalIntegral.integral_congr (g := fun θ => conj (conj (smallB W θ) * g θ) -
        2 * conj (g θ)) (fun _ _ => by simp only [schurBeta, map_mul, Complex.conj_conj]; ring),
      intervalIntegral.integral_sub (intervalIntegrable_conj' hB1) (hcg.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral_conj, intervalIntegral_conj, hG,
      map_zero, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (i1.add i2) i3,
    intervalIntegral.integral_add i1 i2, h3, Complex.conj_mul', Complex.add_re, Complex.add_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

end SchurKernel

section Positivity

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

private theorem imSchur_herglotzVec_sub_principal_le (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ a (ha : IsDirDensity a), ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0 → ∀ c : ℂ,
        |imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) -
            herglotzPrincipal Ω γ (Real.sqrt E) a| ≤
          C * E * (∫ θ in (0 : ℝ)..(2 * π),
            ‖(∫ s in (0 : ℝ)..θ, herglotzConormal (Real.sqrt E) a γ s) - c‖) ^ 2 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨CA, hCA0, hCA⟩ := smallA_approx hK
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_smallBDer_le hK
  set v := (volume Ω).toReal
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * v := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  refine ⟨K * (shiftConst * K) + C₁ * C₁ / v, min 1 ((v / (CA + 1)) ^ 2),
    lt_min one_pos (by positivity), fun E hE hEδ W hW a ha h0 c => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le (min_le_left _ _)).le
  have hs : (CA + 1) * Real.sqrt E < v := by
    have := Real.sqrt_lt_sqrt hE.le (hEδ.trans_le (min_le_right _ _))
    rw [Real.sqrt_sq (by positivity), lt_div_iff₀ (by positivity)] at this
    linarith
  have hAE : smallA W ≤ -(v * E) := by
    have h := hCA E hE.le hE1 W hW
    rw [harea] at h
    nlinarith [(abs_le.mp h).2, Real.sqrt_nonneg E, mul_lt_mul_of_pos_left hs hE]
  have hApos : v * E ≤ |smallA W| := by rw [abs_of_neg (by nlinarith)]; linarith
  have ha0 : smallA W ≠ 0 := by intro h; rw [h] at hAE; nlinarith
  have hai := ha.intervalIntegrable
  obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded hai (Real.sqrt E) hK
  have hG : ∫ θ in (0 : ℝ)..(2 * π), herglotzConormal (Real.sqrt E) a γ θ = 0 := by
    rw [integral_herglotzConormal hb hL hγ hai, h0, mul_zero]
  have hh : IntervalIntegrable (fun θ => conj (herglotzConormal (Real.sqrt E) a γ θ) *
      herglotzWave (Real.sqrt E) a (γ θ)) volume 0 (2 * π) :=
    (intervalIntegrable_conj' (intervalIntegrable_of_norm_le hgm hgB _ _)).mul_continuousOn (by
      rw [show (fun θ => herglotzWave (Real.sqrt E) a (γ θ)) =
        fun θ => herglotzCoeff (Real.sqrt E) a 0 (γ θ) from funext fun _ => herglotzWave_eq _ _ _]
      exact ((continuous_herglotzCoeff hai _ 0).comp hK.continuous).continuousOn)
  rw [imSchur_herglotzVec hK hclosed hW ha, herglotzForm,
    re_volterra_sub_schur_eq hK hW hgm hgB hG hh,
    re_integral_herglotz_principal hb hL hγ hai _ h0, add_sub_cancel_left]
  refine (Complex.abs_re_le_norm _).trans
    ((norm_schurKernel_form_le hK hE.le hW ha0 (hC₁ E hE.le hE1 W hW) hgm hgB hG c).trans ?_)
  gcongr
  have hB : C₁ * E * (C₁ * E) / |smallA W| ≤ C₁ * C₁ / v * E := by
    rw [div_le_iff₀ (abs_pos.mpr ha0)]
    calc C₁ * E * (C₁ * E) = C₁ * C₁ / v * E * (v * E) := by field_simp
      _ ≤ C₁ * C₁ / v * E * |smallA W| := by gcongr
  nlinarith

private lemma sq_intervalIntegral_norm_le {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ θ in (0:ℝ)..(2 * π), ‖g θ‖) ^ 2 ≤ 2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖g θ‖ ^ 2 := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖g θ‖
  set m := S / (2 * π) with hm
  have h1 : IntervalIntegrable (fun θ => ‖g θ‖ ^ 2) volume 0 (2 * π) :=
    (hg.norm.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => 2 * m * ‖g θ‖) volume 0 (2 * π) :=
    (continuous_const.mul hg.norm).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), (‖g θ‖ - m) ^ 2 :=
    intervalIntegral.integral_nonneg h2π.le fun _ _ => sq_nonneg _
  rw [show (fun θ => (‖g θ‖ - m) ^ 2) = fun θ => (‖g θ‖ ^ 2 - 2 * m * ‖g θ‖) + m ^ 2 from
      funext fun _ => by ring,
    intervalIntegral.integral_add (h1.sub h2) intervalIntegrable_const,
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, hm] at hnn
  field_simp at hnn; nlinarith

private lemma norm_herglotzQ_le (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖herglotzQ k a γ θ‖ ≤ ∫ t in (0:ℝ)..(2 * π), ‖herglotzQd k a γ t‖ := by
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded ha k hK
  exact (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans
    (intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
      (Eventually.of_forall fun _ => norm_nonneg _)
      ((intervalIntegrable_of_norm_le hqm hqB _ _).norm))

private lemma schur_numeric {E A I0 Im1 Im2 T0 T1 S G C₁ CT CS K : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC₁ : 0 ≤ C₁) (hCT : 0 ≤ CT) (hCS : 0 ≤ CS) (hA : 0 ≤ A) (hI0 : 0 ≤ I0) (hIm1 : 0 ≤ Im1)
    (hIm2 : 0 ≤ Im2)
    (hED : E * (6 * C₁ + 2 * (2 * π * K ^ 2 * (2 * CT * C₁)) +
      CS * (4 * π * (CT * (2 * C₁ + 1)) + 8 * π ^ 2 * (2 * π * K ^ 2 * (2 * CT * C₁))) + 1) ≤ 1)
    (hm0 : I0 ≤ C₁ * E * A) (hm12 : Im1 + Im2 ≤ C₁ * E ^ 2 * A)
    (hT0 : T0 ≤ CT * (I0 + E / 2 * (A + Im1))) (hT1 : T1 ≤ CT * (Im1 + E / 2 * (I0 + Im2)))
    (hS : S ^ 2 ≤ K ^ 2 * (2 * π * T1)) (hG : G ^ 2 ≤ 2 * (2 * π * T0) + 2 * (4 * π ^ 2 * E * S ^ 2)) :
    0 ≤ 2 * E * A - 6 * E * I0 - 2 * E * S ^ 2 - CS * E * G ^ 2 := by
  set b0 := CT * (2 * C₁ + 1)
  set cq := 2 * π * K ^ 2 * (2 * CT * C₁)
  set cG := 4 * π * b0 + 8 * π ^ 2 * cq
  have hE2 : E ^ 2 ≤ E := by nlinarith
  have hCE21 : C₁ * E ^ 2 * A ≤ C₁ * E * A := by
    nlinarith [mul_nonneg hC₁ hA, hE2]
  have hIm1A : Im1 ≤ C₁ * A := by
    have : E ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hC₁ hA]
  have hT0' : T0 ≤ b0 * E * A := by
    have h : I0 + E / 2 * (A + Im1) ≤ (2 * C₁ + 1) * E * A := by
      nlinarith [mul_le_mul_of_nonneg_left hIm1A hE.le, mul_nonneg hC₁ (mul_nonneg hE.le hA)]
    calc T0 ≤ CT * (I0 + E / 2 * (A + Im1)) := hT0
      _ ≤ CT * ((2 * C₁ + 1) * E * A) := mul_le_mul_of_nonneg_left h hCT
      _ = b0 * E * A := by simp [b0]; ring
  have hT1' : T1 ≤ 2 * CT * C₁ * E ^ 2 * A := by
    have h : Im1 + E / 2 * (I0 + Im2) ≤ 2 * C₁ * E ^ 2 * A := by
      have : I0 + Im2 ≤ 2 * C₁ * E * A := by linarith
      have := mul_le_mul_of_nonneg_left this hE.le
      linarith [show E * (2 * C₁ * E * A) = 2 * C₁ * E ^ 2 * A by ring,
        show E * (I0 + Im2) = 2 * (E / 2 * (I0 + Im2)) by ring]
    calc T1 ≤ CT * (Im1 + E / 2 * (I0 + Im2)) := hT1
      _ ≤ CT * (2 * C₁ * E ^ 2 * A) := mul_le_mul_of_nonneg_left h hCT
      _ = 2 * CT * C₁ * E ^ 2 * A := by ring
  have hSq : S ^ 2 ≤ cq * E * A := by
    have h1 : S ^ 2 ≤ cq * E ^ 2 * A := hS.trans (by
      calc K ^ 2 * (2 * π * T1) ≤ K ^ 2 * (2 * π * (2 * CT * C₁ * E ^ 2 * A)) := by gcongr
        _ = cq * E ^ 2 * A := by simp [cq]; ring)
    have hcqA : 0 ≤ cq * A := by positivity
    nlinarith
  have hSA : S ^ 2 ≤ cq * A := by
    have hcqA : 0 ≤ cq * A := by positivity
    nlinarith
  have hES : E * S ^ 2 ≤ cq * E * A :=
    (mul_le_mul_of_nonneg_left hSA hE.le).trans_eq (by ring)
  have hGsq : G ^ 2 ≤ cG * E * A := by
    refine hG.trans ?_
    have h1 : 2 * (2 * π * T0) ≤ 4 * π * b0 * E * A :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT0' (by positivity))
        (by norm_num)).trans_eq (by ring)
    have h2 : 2 * (4 * π ^ 2 * E * S ^ 2) ≤ 8 * π ^ 2 * cq * E * A :=
      (show 2 * (4 * π ^ 2 * (E * S ^ 2)) ≤ 2 * (4 * π ^ 2 * (cq * E * A)) by gcongr).trans_eq'
        (by ring) |>.trans_eq (by ring)
    linarith [show cG * E * A = 4 * π * b0 * E * A + 8 * π ^ 2 * cq * E * A by simp [cG]; ring]
  have t1 : 6 * E * I0 ≤ 6 * C₁ * E ^ 2 * A :=
    (mul_le_mul_of_nonneg_left hm0 (by positivity : 0 ≤ 6 * E)).trans_eq (by ring)
  have t2 : 2 * E * S ^ 2 ≤ 2 * cq * E ^ 2 * A :=
    (mul_le_mul_of_nonneg_left hSq (by positivity : 0 ≤ 2 * E)).trans_eq (by ring)
  have t3 : CS * E * G ^ 2 ≤ CS * cG * E ^ 2 * A :=
    (mul_le_mul_of_nonneg_left hGsq (by positivity : 0 ≤ CS * E)).trans_eq (by ring)
  have hEA : 0 ≤ E * A := by positivity
  have t4 := mul_le_mul_of_nonneg_right hED hEA
  linarith [mul_nonneg hE.le hEA,
    show E * (6 * C₁ + 2 * cq + CS * cG + 1) * (E * A) =
      6 * C₁ * E ^ 2 * A + 2 * cq * E ^ 2 * A + CS * cG * E ^ 2 * A + E * (E * A) by ring]

/-- **Lemma 8.5 on Herglotz data.** Fix a disc `B(z₁, r) ⊆ Ω`. For small `E > 0`, the Schur
complement is nonnegative on the Herglotz vector of every density whose wave has zero mean over
`Ω` and whose negative coefficients `F_{-j}` (`j ≥ 1`) vanish at `z₁`. -/
theorem herglotz_imSchur_nonneg (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ a (ha : IsDirDensity a),
        (∀ j : ℕ, 1 ≤ j → herglotzCoeff (Real.sqrt E) a (-(j : ℤ)) z₁ = 0) →
        ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0 →
          0 ≤ imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hmodes⟩ := herglotz_modes_small hb hL hr hball
  obtain ⟨CT, hCT0, htrace₀⟩ := trace_sq_le hb hL hγ
  obtain ⟨CS, δS, hδS, hS⟩ := imSchur_herglotzVec_sub_principal_le hb hL hγ
  have hCS'0 : 0 ≤ max CS 0 := le_max_right _ _
  obtain ⟨D, hD, hD0⟩ : ∃ D : ℝ, D = 6 * C₁ + 2 * (2 * π * (Kγ : ℝ) ^ 2 * (2 * CT * C₁)) +
      max CS 0 * (4 * π * (CT * (2 * C₁ + 1)) + 8 * π ^ 2 * (2 * π * (Kγ : ℝ) ^ 2 *
        (2 * CT * C₁))) + 1 ∧ 0 < D := ⟨_, rfl, by positivity⟩
  refine ⟨min (min 1 δ₁) (min δS (1 / D)), by positivity,
    fun E hE hEδ W hW a ha hz hmean => ?_⟩
  have hE1 : E ≤ 1 := (hEδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hEδ₁ : E ≤ δ₁ := (hEδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hEδS : E < δS := hEδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hED : E * D ≤ 1 :=
    (le_div_iff₀ hD0).mp (hEδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  rw [hD] at hED
  have hai := ha.intervalIntegrable
  set k := Real.sqrt E
  have hk0 : 0 ≤ k := Real.sqrt_nonneg E
  have hk2 : k ^ 2 = E := Real.sq_sqrt hE.le
  obtain ⟨hm0, hm12⟩ := hmodes a ha k (by rw [hk2]; exact hEδ₁) hz hmean
  rw [hk2] at hm0
  rw [show k ^ 4 = (k ^ 2) ^ 2 by ring, hk2] at hm12
  have htrace : ∀ m : ℤ, ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a m (γ θ)‖ ^ 2 ≤
      CT * ((∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2) +
        E / 2 * ((∫ z in Ω, ‖herglotzCoeff k a (m + 1) z‖ ^ 2) +
          ∫ z in Ω, ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := fun m => by
    obtain ⟨Kf, hKf⟩ := lipschitzWith_herglotzCoeff hai k m
    have h := htrace₀ _ Kf hKf _ (norm_herglotzCoeff_le k m)
    simp only [gradSq_herglotzCoeff hai] at h
    rwa [integral_const_mul, integral_add (integrable_herglotzCoeff_sq hb hai k _)
      (integrable_herglotzCoeff_sq hb hai k _), hk2] at h
  have hT0 := htrace 0
  have hT1 := htrace (-1)
  norm_num at hT0 hT1
  obtain ⟨hqm, hqB⟩ := herglotzQd_bounded hai k hKγ
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖
  have hS0 : 0 ≤ S := intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
  have hSq : S ^ 2 ≤ Kγ ^ 2 * (2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖ ^ 2) := by
    have h1 : S ≤ Kγ * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by positivity)
        ((intervalIntegrable_of_norm_le hqm hqB _ _).norm)
        ((continuous_const.mul ((continuous_herglotzCoeff hai k (-1)).comp
          hKγ.continuous).norm).intervalIntegrable _ _) fun θ _ => ?_
      rw [herglotzQd, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg _)
    calc S ^ 2 ≤ (Kγ * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖) ^ 2 :=
          pow_le_pow_left₀ hS0 h1 2
      _ = Kγ ^ 2 * (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖) ^ 2 := by ring
      _ ≤ _ := by
          gcongr
          exact sq_intervalIntegral_norm_le ((continuous_herglotzCoeff hai k (-1)).comp hKγ.continuous)
  set G := ∫ θ in (0:ℝ)..(2 * π),
    ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) - Complex.I * herglotzCoeff k a 0 (γ 0)‖
  have hGsq : G ^ 2 ≤ 2 * (2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖ ^ 2) +
      2 * (4 * π ^ 2 * E * S ^ 2) := by
    obtain ⟨hgm, Bg, hgB⟩ := herglotzConormal_bounded hai k hKγ
    have hGc : Continuous fun θ =>
        ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) - Complex.I * herglotzCoeff k a 0 (γ 0)‖ :=
      ((intervalIntegral.continuous_primitive
        (fun _ _ => intervalIntegrable_of_norm_le hgm hgB _ _) 0).sub continuous_const).norm
    have hh : Continuous fun θ => ‖herglotzCoeff k a 0 (γ θ)‖ :=
      ((continuous_herglotzCoeff hai k 0).comp hKγ.continuous).norm
    have h1 : G ≤ (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖) + 2 * π * k * S := by
      calc G ≤ ∫ θ in (0:ℝ)..(2 * π), (‖herglotzCoeff k a 0 (γ θ)‖ + k * S) := by
            refine intervalIntegral.integral_mono_on (by positivity) (hGc.intervalIntegrable _ _)
              ((hh.add continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
            rw [primitive_herglotzConormal_eq hai k hKγ θ,
              show -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
                k * herglotzQ k a γ θ - Complex.I * herglotzCoeff k a 0 (γ 0) =
                -Complex.I * herglotzCoeff k a 0 (γ θ) + k * herglotzQ k a γ θ by ring]
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
            · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0]
              exact mul_le_mul_of_nonneg_left (norm_herglotzQ_le hai k hKγ hθ) hk0
        _ = _ := by
            rw [intervalIntegral.integral_add (hh.intervalIntegrable _ _) intervalIntegrable_const,
              intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
    have h2 : (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖) ^ 2 ≤
        2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖ ^ 2 :=
      sq_intervalIntegral_norm_le ((continuous_herglotzCoeff hai k 0).comp hKγ.continuous)
    have hG0 : 0 ≤ G := intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    set H := ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖
    have h3 : G ^ 2 ≤ 2 * H ^ 2 + 2 * (2 * π * k * S) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hG0 h1 2, sq_nonneg (H - 2 * π * k * S)]
    have h4 : (2 * π * k * S) ^ 2 = 4 * π ^ 2 * E * S ^ 2 := by
      rw [show (2 * π * k * S) ^ 2 = 4 * π ^ 2 * k ^ 2 * S ^ 2 by ring, hk2]
    linarith
  have hQ : ‖∫ θ in (0:ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ‖ ≤ S ^ 2 := by
    have hqi : IntervalIntegrable (fun t => ‖herglotzQd k a γ t‖) volume 0 (2 * π) :=
      (intervalIntegrable_of_norm_le hqm hqB _ _).norm
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    calc ∫ θ in (0:ℝ)..(2 * π), ‖conj (herglotzQd k a γ θ) * herglotzQ k a γ θ‖
        ≤ ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ * S := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) ?_ (hqi.mul_const _)
            fun θ hθ => ?_
          · have hQc : Continuous (herglotzQ k a γ) :=
              intervalIntegral.continuous_primitive
                (fun _ _ => intervalIntegrable_of_norm_le hqm hqB _ _) 0
            simpa using ((intervalIntegrable_conj' (intervalIntegrable_of_norm_le hqm hqB 0 (2 * π))).mul_continuousOn
              hQc.continuousOn).norm
          · rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul_of_nonneg_left (norm_herglotzQ_le hai k hKγ ⟨hθ.1.le, hθ.2.le⟩)
              (norm_nonneg _)
      _ = S ^ 2 := by rw [intervalIntegral.integral_mul_const]; ring
  have hP : 2 * E * (∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2) -
      6 * E * (∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2) - 2 * E * S ^ 2 ≤
      herglotzPrincipal Ω γ k a := by
    unfold herglotzPrincipal; rw [hk2]
    have him := (Complex.im_le_norm _).trans hQ
    have hIm1 : 0 ≤ ∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    nlinarith
  have hlow := (abs_le.mp (hS E hE hEδS W hW a ha hmean
    (Complex.I * herglotzCoeff k a 0 (γ 0)))).1
  have hCS : CS * E * G ^ 2 ≤ max CS 0 * E * G ^ 2 := by gcongr; exact le_max_left _ _
  have hnum := schur_numeric hE hE1 hC₁.le hCT0 hCS'0 (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity) hED hm0 (by linarith) hT0 hT1 hSq hGsq
  linarith

end Positivity

section Admissible

variable {Ω : Set ℂ}

private lemma herglotzVec_congr_ae {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b)
    (h : a =ᵐ[volume.restrict (Ioc 0 (2 * π))] b) (k : ℝ) (z : ℂ) :
    herglotzVec ha k z = herglotzVec hb k z := by
  have hc : ∀ m, herglotzCoeff k a m z = herglotzCoeff k b m z := fun m => by
    unfold herglotzCoeff; congr 1
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le (by positivity)]
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h
    filter_upwards [h] with φ hφ hmem using by rw [hφ hmem]
  refine lp.ext (funext fun n => ?_)
  simp only [herglotzVec_apply, herglotzSeq, hc]

private lemma ae_restrict_Ioc_of_ae_haar {p : AddCircle (2 * π) → Prop}
    (h : ∀ᵐ x ∂(@AddCircle.haarAddCircle (2 * π) _), p x) :
    ∀ᵐ φ : ℝ ∂(volume.restrict (Ioc 0 (2 * π))), p φ := by
  have hv : ∀ᵐ x ∂(volume : Measure (AddCircle (2 * π))), p x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; exact Measure.ae_smul_measure h _
  simpa using (AddCircle.measurePreserving_mk (2 * π) 0).quasiMeasurePreserving.ae hv

private def synthCoeff (v : Ell2) (m : ℤ) : ℂ :=
  if m = 0 then (Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0 else if 0 < m then (v : ℕ → ℂ) m.toNat else 0

private lemma hasSum_sq_synthCoeff (v : Ell2) :
    HasSum (fun m => ‖synthCoeff v m‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
  have hv : HasSum (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ 2) (‖v‖ ^ 2) := by
    simpa [two_toReal] using lp.hasSum_norm (p := 2) (by norm_num) v
  have hpos : HasSum (fun n : ℕ => ‖synthCoeff v n‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
    refine (hv.add (hasSum_ite_eq 0 (‖(v : ℕ → ℂ) 0‖ ^ 2))).congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hr : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
      simp [synthCoeff, mul_pow]; ring
    · rw [synthCoeff, if_neg (by exact_mod_cast hn.ne'), if_pos (by exact_mod_cast hn),
        Int.toNat_natCast, if_neg hn.ne', add_zero]
  have hneg : HasSum (fun n : ℕ => ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2) 0 := by
    convert hasSum_zero with n
    rw [synthCoeff, if_neg (by omega), if_neg (by omega), norm_zero]; norm_num
  simpa using HasSum.of_nat_of_neg_add_one (f := fun m => ‖synthCoeff v m‖ ^ 2) hpos hneg

private def synthL2 (v : Ell2) : Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) :=
  fourierBasis.repr.symm ⟨synthCoeff v, (memℓp_gen_iff (by simp)).mpr <| by
    simpa [two_toReal] using (hasSum_sq_synthCoeff v).summable⟩

private def synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (φ : ℝ) : ℂ :=
  (synthL2 v : AddCircle (2 * π) → ℂ) φ * planeWave k (-z₁) φ

private lemma isDirDensity_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    IsDirDensity (synthDens k z₁ v) := by
  have ha₀ : IsDirDensity fun φ : ℝ => (synthL2 v : AddCircle (2 * π) → ℂ) φ := by
    have := (memLp_haarAddCircle_iff.mp (Lp.memLp (synthL2 v))).comp_measurePreserving
      (AddCircle.measurePreserving_mk (2 * π) 0)
    rwa [zero_add] at this
  exact ha₀.of_le (ha₀.aestronglyMeasurable.mul (continuous_planeWave k (-z₁)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by rw [synthDens, norm_mul, norm_planeWave, mul_one])

private lemma herglotzCoeff_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (m : ℤ) :
    herglotzCoeff k (synthDens k z₁ v) m z₁ = synthCoeff v m := by
  unfold synthDens
  rw [herglotzCoeff_shift, herglotzCoeff_zero_eq_fourierCoeff,
    ← fourierBasis_repr, synthL2, LinearIsometryEquiv.apply_symm_apply]

private lemma herglotzVec_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    herglotzVec (isDirDensity_synthDens k z₁ v) k z₁ = v := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply]; unfold herglotzSeq
  split_ifs with hn
  · subst hn; rw [herglotzCoeff_synthDens, synthCoeff, if_pos rfl]
    have hr : (Real.sqrt 2 : ℂ) ≠ 0 :=
      by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    field_simp
  · rw [herglotzCoeff_synthDens, synthCoeff, if_neg (by exact_mod_cast hn),
      if_pos (by omega), Int.toNat_natCast]

private lemma herglotzVec_synthDens_add (k : ℝ) (z₁ : ℂ) (v w : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (v + w)) k z =
      herglotzVec (isDirDensity_synthDens k z₁ v) k z +
        herglotzVec (isDirDensity_synthDens k z₁ w) k z := by
  have hl : synthL2 (v + w) = synthL2 v + synthL2 w := by
    unfold synthL2; rw [← map_add]; congr 1
    refine lp.ext (funext fun m => ?_)
    rw [lp.coeFn_add, Pi.add_apply]
    show synthCoeff (v + w) m = synthCoeff v m + synthCoeff w m
    unfold synthCoeff; split_ifs <;> simp [mul_add]
  have hae : synthDens k z₁ (v + w) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      synthDens k z₁ v + synthDens k z₁ w := by
    have h := Lp.coeFn_add (synthL2 v) (synthL2 w)
    rw [← hl] at h
    filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
    simp [synthDens, hφ, add_mul]
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).add (isDirDensity_synthDens k z₁ w))
    hae, herglotzVec_add]

private lemma herglotzVec_synthDens_smul (k : ℝ) (z₁ : ℂ) (c : ℂ) (v : Ell2) (z : ℂ) :
    herglotzVec (isDirDensity_synthDens k z₁ (c • v)) k z =
      c • herglotzVec (isDirDensity_synthDens k z₁ v) k z := by
  have hl : synthL2 (c • v) = c • synthL2 v := by
    unfold synthL2; rw [← map_smul]; congr 1
    refine lp.ext (funext fun m => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    show synthCoeff (c • v) m = c * synthCoeff v m
    unfold synthCoeff; split_ifs <;> simp <;> ring
  have hae : synthDens k z₁ (c • v) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      c • synthDens k z₁ v := by
    have h := Lp.coeFn_smul c (synthL2 v)
    rw [← hl] at h
    filter_upwards [ae_restrict_Ioc_of_ae_haar h] with φ hφ
    simp [synthDens, hφ, mul_assoc]
  rw [herglotzVec_congr_ae _ ((isDirDensity_synthDens k z₁ v).const_smul c) hae, herglotzVec_smul]

private lemma norm_herglotzVec_synthDens_sub_le (k : ℝ) (z₁ z : ℂ) (v : Ell2) :
    ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z - v‖ ≤
      |k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖ := by
  have h := norm_herglotzVec_sub_le (isDirDensity_synthDens k z₁ v) k z z₁
  rw [herglotzVec_synthDens] at h
  refine h.trans ?_
  have hsq : (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    have h1 := hasSum_sq_herglotzCoeff (isDirDensity_synthDens k z₁ v) k z₁
    simp only [herglotzCoeff_synthDens] at h1
    rw [h1.unique (hasSum_sq_synthCoeff v)]
    have := lp.norm_apply_le_norm (p := 2) (by norm_num) v 0
    nlinarith [norm_nonneg ((v : ℕ → ℂ) 0)]
  have hs : Real.sqrt ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖synthDens k z₁ v φ‖ ^ 2) ≤
      Real.sqrt 2 * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hsq
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (abs_nonneg k))
    (norm_nonneg (z - z₁))
  linarith

private def synthOp (k : ℝ) (z₁ z₀ : ℂ) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun v => herglotzVec (isDirDensity_synthDens k z₁ v) k z₀
      map_add' := fun v w => herglotzVec_synthDens_add k z₁ v w z₀
      map_smul' := fun c v => herglotzVec_synthDens_smul k z₁ c v z₀ }
    (1 + |k| * Real.sqrt 2 * ‖z₀ - z₁‖) fun v => by
      have h := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
      have := norm_le_insert' (herglotzVec (isDirDensity_synthDens k z₁ v) k z₀) v
      show ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z₀‖ ≤ _
      nlinarith [norm_nonneg v]

private lemma herglotzCoeff_zero_eq_herglotzVec {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (z : ℂ) :
    herglotzCoeff k a 0 z = (Real.sqrt 2 : ℂ) * (herglotzVec ha k z : ℕ → ℂ) 0 := by
  rw [herglotzVec_apply]; unfold herglotzSeq; rw [if_pos rfl]
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 :=
    by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  field_simp

private def synthMean (Ω : Set ℂ) (k : ℝ) (z₁ : ℂ) (v : Ell2) : ℂ :=
  ∫ z in Ω, herglotzCoeff k (synthDens k z₁ v) 0 z

private lemma norm_synthMean_sub_le (hb : Bornology.IsBounded Ω) {R : ℝ} {z₁ : ℂ}
    (hR : Ω ⊆ closedBall z₁ R) (k : ℝ) (v : Ell2) :
    ‖synthMean Ω k z₁ v - (volume Ω).toReal * ((Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0)‖ ≤
      2 * |k| * ‖v‖ * R * (volume Ω).toReal := by
  have hint := integrableOn_herglotzCoeff hb (isDirDensity_synthDens k z₁ v).intervalIntegrable k 0
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  unfold synthMean
  rw [show (volume Ω).toReal * ((Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0) =
      ∫ _ in Ω, (Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0 by
    rw [setIntegral_const, Complex.real_smul, Measure.real_def],
    ← integral_sub hint (integrable_const _)]
  have := norm_setIntegral_le_of_norm_le_const_ae' (C := 2 * |k| * ‖v‖ * R)
    (f := fun z => herglotzCoeff k (synthDens k z₁ v) 0 z - (Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0)
    (hb.measure_lt_top (μ := volume)) (Eventually.of_forall fun z hz => ?_)
  · simpa [Measure.real_def] using this
  rw [herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v), ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : ‖(herglotzVec (isDirDensity_synthDens k z₁ v) k z : ℕ → ℂ) 0 - (v : ℕ → ℂ) 0‖ ≤
      ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z - v‖ := by
    simpa using lp.norm_apply_le_norm (p := 2) (by norm_num)
      (herglotzVec (isDirDensity_synthDens k z₁ v) k z - v) 0
  have h2 := norm_herglotzVec_synthDens_sub_le k z₁ z v
  have h3 : ‖z - z₁‖ ≤ R := by simpa [dist_eq_norm] using hR hz
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * ‖(herglotzVec (isDirDensity_synthDens k z₁ v) k z : ℕ → ℂ) 0 -
        (v : ℕ → ℂ) 0‖ ≤ Real.sqrt 2 * (|k| * Real.sqrt 2 * ‖v‖ * ‖z - z₁‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)
    _ = 2 * |k| * ‖v‖ * ‖z - z₁‖ := by linear_combination (|k| * ‖v‖ * ‖z - z₁‖) * hs2
    _ ≤ 2 * |k| * ‖v‖ * R := by gcongr

/-- **Admissible Herglotz data.** For a bounded `Ω` of positive area and points `z₀, z₁`, there is
`δ > 0` such that for `|k| < δ` every `w ∈ ℓ²` can be moved along `e₀` to the Herglotz vector
`y_a(z₀)` of a density whose negative coefficients vanish at `z₁` and whose wave has zero mean
over `Ω`. -/
theorem exists_admissible_herglotzVec (hb : Bornology.IsBounded Ω)
    (hΩ : 0 < (volume Ω).toReal) (z₀ z₁ : ℂ) :
    ∃ δ > 0, ∀ k : ℝ, |k| < δ → ∀ w : Ell2, ∃ (t : ℂ) (a : ℝ → ℂ) (ha : IsDirDensity a),
      herglotzVec ha k z₀ = w + t • basisVec 0 ∧
      (∀ j : ℕ, 1 ≤ j → herglotzCoeff k a (-(j : ℤ)) z₁ = 0) ∧
      ∫ z in Ω, herglotzCoeff k a 0 z = 0 := by
  obtain ⟨R₀, hR₀⟩ := hb.subset_closedBall z₁
  set R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : Ω ⊆ closedBall z₁ R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set d := ‖z₀ - z₁‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨min (1 / (4 * Real.sqrt 2 * (d + 1))) (1 / (4 * (R + 1))), by positivity,
    fun k hk w => ?_⟩
  have hk1 : |k| ≤ 1 / (4 * Real.sqrt 2 * (d + 1)) := (hk.trans_le (min_le_left _ _)).le
  have hk2 : |k| ≤ 1 / (4 * (R + 1)) := (hk.trans_le (min_le_right _ _)).le
  have hε : |k| * Real.sqrt 2 * d ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hk1; nlinarith [abs_nonneg k]
  have hkR : |k| * R ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hk2; nlinarith [abs_nonneg k]
  have hsurj : Function.Surjective (synthOp k z₁ z₀) := by
    have hn : ‖1 - synthOp k z₁ z₀‖ < 1 := by
      refine (ContinuousLinearMap.opNorm_le_bound _ (M := |k| * Real.sqrt 2 * d)
        (by positivity) fun v => ?_).trans_lt (by linarith)
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_sub_rev]
      have := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v
      change ‖herglotzVec (isDirDensity_synthDens k z₁ v) k z₀ - v‖ ≤ |k| * Real.sqrt 2 * d * ‖v‖
      linarith [show |k| * Real.sqrt 2 * ‖v‖ * ‖z₀ - z₁‖ = |k| * Real.sqrt 2 * d * ‖v‖ by simp [d]; ring]
    obtain ⟨S, hS⟩ := (show IsUnit (synthOp k z₁ z₀) by
      simpa using isUnit_one_sub_of_norm_lt_one hn).exists_right_inv
    exact fun u => ⟨S u, by simpa using congrArg (fun T : Ell2 →L[ℂ] Ell2 => T u) hS⟩
  obtain ⟨v₂, hv₂⟩ := hsurj (basisVec 0)
  have hT2 := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v₂
  change ‖synthOp k z₁ z₀ v₂ - v₂‖ ≤ |k| * Real.sqrt 2 * ‖v₂‖ * d at hT2
  rw [hv₂] at hT2
  have hv2n : ‖v₂‖ ≤ 4 / 3 := by
    have := norm_le_insert' v₂ (basisVec 0)
    rw [show ‖basisVec 0‖ = 1 by simp [basisVec, lp.norm_single], norm_sub_rev] at this
    nlinarith [norm_nonneg v₂]
  have hv20 : ‖(v₂ : ℕ → ℂ) 0 - 1‖ ≤ 1 / 3 := by
    have h1 := lp.norm_apply_le_norm (p := 2) (by norm_num) (v₂ - basisVec 0) 0
    rw [show ((v₂ - basisVec 0 : Ell2) : ℕ → ℂ) 0 = (v₂ : ℕ → ℂ) 0 - 1 by simp [basisVec],
      norm_sub_rev v₂] at h1
    nlinarith [norm_nonneg v₂]
  have hlam2 : synthMean Ω k z₁ v₂ ≠ 0 := by
    intro h0
    have h1 := norm_synthMean_sub_le hb hR k v₂
    rw [h0, zero_sub, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hΩ.le, Real.norm_of_nonneg hs2.le] at h1
    have h3 : 2 / 3 ≤ ‖(v₂ : ℕ → ℂ) 0‖ := by
      have := norm_sub_norm_le (1 : ℂ) ((v₂ : ℕ → ℂ) 0)
      rw [norm_one, norm_sub_rev] at this; linarith
    have h4 : 2 * |k| * ‖v₂‖ * R ≤ 2 / 3 := by nlinarith [abs_nonneg k, norm_nonneg v₂]
    have h5 : (1.4 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    nlinarith [mul_lt_mul_of_pos_left (by nlinarith : 2 / 3 < Real.sqrt 2 * ‖(v₂ : ℕ → ℂ) 0‖) hΩ,
      mul_le_mul_of_nonneg_left h4 hΩ.le]
  obtain ⟨v₁, hv₁⟩ := hsurj w
  set t : ℂ := -(synthMean Ω k z₁ v₁ / synthMean Ω k z₁ v₂) with ht
  refine ⟨t, synthDens k z₁ (v₁ + t • v₂), isDirDensity_synthDens k z₁ _, ?_, fun j hj => ?_, ?_⟩
  · change synthOp k z₁ z₀ (v₁ + t • v₂) = _
    rw [map_add, map_smul, hv₁, hv₂]
  · rw [herglotzCoeff_synthDens, synthCoeff, if_neg (by omega), if_neg (by omega)]
  · have hlin : synthMean Ω k z₁ (v₁ + t • v₂) =
        synthMean Ω k z₁ v₁ + t * synthMean Ω k z₁ v₂ := by
      unfold synthMean
      rw [← integral_const_mul, ← integral_add
        (integrableOn_herglotzCoeff hb (isDirDensity_synthDens k z₁ v₁).intervalIntegrable k 0)
        ((integrableOn_herglotzCoeff hb (isDirDensity_synthDens k z₁ v₂).intervalIntegrable k 0).const_mul _)]
      congr 1; funext z
      rw [herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ _),
        herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v₁),
        herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v₂),
        herglotzVec_synthDens_add, herglotzVec_synthDens_smul]
      simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring
    show synthMean Ω k z₁ (v₁ + t • v₂) = 0
    rw [hlin, ht]; field_simp; ring

end Admissible

end PolyaNeumann

end
