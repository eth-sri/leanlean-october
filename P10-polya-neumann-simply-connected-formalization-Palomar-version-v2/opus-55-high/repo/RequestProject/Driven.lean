module

public import RequestProject.CurveContinuity

/-!
# Driven transport equations and their endpoint identities (Lemma 4.10)

For a Lipschitz curve `γ`, an energy `E` and the transport `W = W_E`, consider an
`ℓ²(ℕ₀)`-valued solution `y` of the driven equation `y' = C_E y + f` (in integral form).
Variation of constants gives `y(θ) = W(θ) (y(0) + ∫₀^θ W(s)^* f(s) ds)`.

For the paper's forcing `f = -(i/√2) g e₀` this yields Lemma 4.10:
* `√2 ⟨e₀, y(θ)⟩ = √2 (O_E v)(θ) - i (T_E g)(θ)` (the trace identity `h_a = √2 O_E v - i T_E g`),
* if moreover `y(L) = y(0) = v`, then `(I - V_E) v = -(i/√2) V_E O_E^* g` and
  `O_E^* g = √2 i (V_E^* - I) v`,

where `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`, `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds` and
`O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`.  We also prove the adjoint formula for `O_E^*` and the
kernel identity `T_E + T_E^* = O_E O_E^*` of Lemma 4.6.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The observation map `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`. -/
def observation (W : ℝ → Ell2 →L[ℂ] Ell2) (v : Ell2) (θ : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ v)

/-- The adjoint observation map `O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`. -/
def observationAdj (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) : Ell2 :=
  ∫ s in (0 : ℝ)..(2 * π), g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)

/-- The Volterra kernel `k(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩`. -/
def volterraKernel (W : ℝ → Ell2 →L[ℂ] Ell2) (θ s : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ (ContinuousLinearMap.adjoint (W s) (basisVec 0)))

/-- The Volterra operator `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds`. -/
def volterraOp (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..θ, volterraKernel W θ s * g s

/-- The adjoint Volterra operator `(T_E^* g)(θ) = ∫_θ^L conj(k(s, θ)) g(s) ds`. -/
def volterraOpAdj (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in θ..(2 * π), conj (volterraKernel W s θ) * g s

/-- Compatibility instance: real scalars commute with the adjoint star on complex operators. -/
instance instStarModuleRealCLMComplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : StarModule ℝ (E →L[ℂ] E) :=
  ⟨fun r A => by
    norm_num⟩

variable {γ : ℝ → ℂ} {K : NNReal} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- A bounded Lipschitz family of operators applied to a bounded Lipschitz family of vectors
is Lipschitz. -/
theorem lipschitzOnWith_apply_of_bounded {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℝ → E →L[ℂ] F}
    {g : ℝ → E} {s : Set ℝ} {Kf Kg : NNReal} {B : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzOnWith (Kf * B.toNNReal + B.toNNReal * Kg) (fun x => f x (g x)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hB  := (norm_nonneg _).trans (hfB x hx)
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm] at h1 h2 ⊢
  have e : f x (g x) - f y (g y) = (f x - f y) (g x) + f y (g x - g y) := by
    norm_num
  rw [e]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  calc ‖(f x - f y) (g x) + f y (g x - g y)‖
      ≤ ‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
          (ContinuousLinearMap.le_opNorm _ _))
    _ ≤ (Kf * dist x y) * B + B * (Kg * dist x y) := by
        gcongr
        all_goals simp_all
    _ = _ := by ring

/-- Product rule for a family of complex-linear operators applied to a family of vectors,
differentiated with respect to a real parameter. -/
theorem hasDerivAt_clm_apply_real {A : ℝ → Ell2 →L[ℂ] Ell2} {A' : Ell2 →L[ℂ] Ell2}
    {u : ℝ → Ell2} {u' : Ell2} {θ : ℝ} (hA : HasDerivAt A A' θ) (hu : HasDerivAt u u' θ) :
    HasDerivAt (fun x => A x (u x)) (A' (u θ) + A θ u') θ :=
  ((ContinuousLinearMap.restrictScalarsL ℂ Ell2 Ell2 ℝ ℝ).hasFDerivAt.comp_hasDerivAt θ
    hA).clm_apply hu

/-- Variation of constants for the driven transport equation: if `y` solves
`y(θ) = y(0) + ∫₀^θ (C_E y + f)` on `[0, L]` with a bounded measurable forcing `f`, then
`y(θ) = W(θ) (y(0) + ∫₀^θ W(s)^* f(s) ds)`. -/
theorem driven_eq_transport (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {f : ℝ → Ell2}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in 0..θ, (transportCoeff γ E s (y s) + f s)) :
    ∀ θ ∈ Icc 0 (2 * π),
      y θ = W θ (y 0 + ∫ s in 0..θ, ContinuousLinearMap.adjoint (W s) (f s)) := by
  have h0 : 0 ∈ Icc 0 (2 * π) := ⟨le_rfl, by positivity⟩
  set C := transportCoeff γ E with hCdef
  have hC : AEStronglyMeasurable C volume := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  set M := ‖(-(Complex.I * Real.sqrt E) / 2)‖ *
      (K * ‖ContinuousLinearMap.adjoint shiftN‖ + K * ‖shiftN‖)
  have hM0  := (norm_nonneg _).trans (hM 0)
  have hB0  := (norm_nonneg _).trans (hfB 0)
  obtain ⟨Sy, hSy⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hSy0  := (norm_nonneg _).trans (hSy 0 h0)
  have happ : Continuous fun p : (Ell2 →L[ℂ] Ell2) × Ell2 => p.1 p.2 := by fun_prop
  -- the integrand of the driven equation
  set G : ℝ → Ell2 := fun s => C s (y s) + f s with hG
  have hGB  := fun x hx =>
    (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hM x) (hSy x hx) (norm_nonneg _) hM0)) (hfB x))
  have hGi : IntegrableOn G (Icc 0 (2 * π)) :=
    Integrable.of_bound ((happ.comp_aestronglyMeasurable₂ hC.restrict
      (hy.aestronglyMeasurable measurableSet_Icc)).add hf.restrict) (M * Sy + B)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hGB))
  have hGii : ∀ θ ∈ Icc 0 (2 * π), IntervalIntegrable G volume 0 θ := fun θ hθ =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hθ.1).mpr
      (hGi.mono_set (Icc_subset_Icc le_rfl hθ.2))
  -- `y` is Lipschitz with a.e. derivative `G`
  have hyL : LipschitzOnWith (M * Sy + B).toNNReal y (Icc 0 (2 * π)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity), ey x hx, ey x' hx',
      add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hGii x hx) (hGii x' hx')]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hGB t ?_
    grind
  have hyd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) → HasDerivAt y (G θ) θ := by
    set g : ℝ → Ell2 := (Icc 0 (2 * π)).indicator G
    have hgi : Integrable g := hGi.integrable_indicator measurableSet_Icc
    filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hgi.locallyIntegrable]
      with θ hθ hmem
    have h1 := (hθ 0).const_add (y 0)
    rw [show g θ = G θ by simp [g, indicator_of_mem (Ioo_subset_Icc_self hmem)]] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    rw [ey x (Ioo_subset_Icc_self hx)]
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    have : t ∈ Icc 0 (2 * π) := by
      rw [uIcc_of_le hx.1.le] at ht; grind
    simp [g, G, indicator_of_mem this]
  -- facts about `W^*`
  have hW0 : W 0 = 1 := by simpa using hW.2 0 h0
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn hC hM hW.1 hW.2
  have hWs1 : ∀ x ∈ Icc 0 (2 * π), ‖star (W x)‖ ≤ 1 := fun x hx => by
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hx)
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
    filter_upwards [volterra_ae_hasDerivAt hC hM hW.1 hW.2] with θ hθ hmem
    have := (hθ hmem).star
    rw [star_mul, transportCoeff_star] at this
    convert this using 1
    simp [hCdef]
  -- `z = W^* y` has a.e. derivative `W^* f`
  have hzL := lipschitzOnWith_apply_of_bounded (LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        ← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
      exact hKW.dist_le_mul x hx y hy) hyL 
    (fun x hx => (hWs1 x hx).trans (le_max_left _ _))
    (fun x hx => (hSy x hx).trans ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  have hgB  := fun x hx =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul (hWs1 x hx) (hfB x) (norm_nonneg _) zero_le_one).trans_eq (one_mul B))
  have hWm : AEStronglyMeasurable W (volume.restrict (Icc 0 (2 * π))) :=
    hW.1.aestronglyMeasurable measurableSet_Icc
  have hWsm : AEStronglyMeasurable (fun s => star (W s)) (volume.restrict (Icc 0 (2 * π))) := by
    fun_prop
  intro θ hθ
  have h1 := eq_add_integral_of_ae_hasDerivAt hzL (Integrable.of_bound (happ.comp_aestronglyMeasurable₂ hWsm hf.restrict) B
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))) hgB (by
    filter_upwards [hyd, hds] with θ h1 h2 hmem
    have := hasDerivAt_clm_apply_real (h2 hmem) (h1 hmem)
    convert this using 1
    simp [G]) θ hθ
  rw [hW0, star_one] at h1
  have hu : W θ * star (W θ) = 1 := transport_mul_adjoint hK hW hθ
  have e1 : y θ = W θ (star (W θ) (y θ)) := by
    rw [← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
  rw [e1, h1]
  rfl

/-- A bounded measurable scalar function times a function continuous on `[0, L]` is interval
integrable between any two points of `[0, L]`. -/
lemma intervalIntegrable_smul_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {u : ℝ → F} (hu : ContinuousOn u (Icc 0 (2 * π))) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {a b : ℝ}
    (ha : a ∈ Icc 0 (2 * π)) (hb : b ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => g s • u s) volume a b := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hI : IntegrableOn (fun s => g s • u s) (Icc 0 (2 * π)) :=
    Integrable.of_bound (hg.restrict.smul (hu.aestronglyMeasurable measurableSet_Icc)) (B * S) ((ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun s hs => by
        rw [norm_smul]
        exact mul_le_mul (hgB s) (hS s hs) (norm_nonneg _) ((norm_nonneg _).trans (hgB s))))
  exact intervalIntegrable_iff.mpr (hI.mono_set (uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)))

/-- `s ↦ W(s)^* e₀` is continuous on `[0, L]`. -/
lemma continuousOn_adjoint_apply (hW : ContinuousOn W (Icc 0 (2 * π)))
    (x : Ell2) : ContinuousOn (fun s => ContinuousLinearMap.adjoint (W s) x) (Icc 0 (2 * π)) := by
  fun_prop

/-- Pulling the observation functional `⟨e₀, W(θ) ·⟩` inside the integral defining `O_E^*`:
`⟨e₀, W(θ) ∫_a^b g(s) W(s)^* e₀ ds⟩ = ∫_a^b k(θ, s) g(s) ds`. -/
lemma inner_transport_integral {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (θ : ℝ)
    {a b : ℝ} (ha : a ∈ Icc 0 (2 * π)) (hb : b ∈ Icc 0 (2 * π)) :
    inner ℂ (basisVec 0) (W θ (∫ s in a..b, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))) =
      ∫ s in a..b, volterraKernel W θ s * g s := by
  set Lf : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp (W θ)
  have := Lf.intervalIntegral_comp_comm (intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB ha hb)
  simp only [Lf, ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul] at this
  rw [← this]
  simp only [volterraKernel]
  ring

/-- Variation of constants for the paper's forcing `-(i/√2) g e₀`:
`y(θ) = W(θ) y(0) - (i/√2) W(θ) ∫₀^θ g(s) W(s)^* e₀ ds`. -/
theorem driven_formula (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in 0..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), y θ = W θ (y 0) + (-(Complex.I / Real.sqrt 2)) •
      W θ (∫ s in 0..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) := by
  set c : ℂ := -(Complex.I / Real.sqrt 2)
  have hfB : ∀ s, ‖(c * g s) • basisVec 0‖ ≤ ‖c‖ * B * ‖basisVec 0‖ := fun s => by
    rw [norm_smul, norm_mul]
    gcongr
    simp_all
  intro θ hθ
  rw [driven_eq_transport hK hW ((hg.const_mul c).smul_const _) hfB hy ey θ hθ, ← map_smul]
  simp [← intervalIntegral.integral_smul, smul_smul]

/-- **Lemma 4.10 (trace identity).**  Let `y` solve the driven equation
`y' = C_E y - (i/√2) g e₀` on `[0, L]` (in integral form), with `g` bounded and measurable,
and let `v = y(0)`.  Then `h = √2 ⟨e₀, y⟩` satisfies `h = √2 O_E v - i T_E g` on `[0, L]`. -/
theorem driven_trace {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in 0..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), Real.sqrt 2 * inner ℂ (basisVec 0) (y θ) =
      Real.sqrt 2 * observation W (y 0) θ - Complex.I * volterraOp W g θ := by
  intro θ hθ
  rw [driven_formula hK hW hg hgB hy ey θ hθ, inner_add_right, inner_smul_right,
    inner_transport_integral hW.1 hg hgB θ ⟨le_rfl, hθ.1.trans hθ.2⟩ hθ]
  simp only [observation, volterraOp]
  field_simp
  ring

/-- **Lemma 4.10 (endpoint identities).**  If in addition `y` is periodic, `y(L) = y(0) = v`,
then `(I - V_E) v = -(i/√2) V_E O_E^* g` and `O_E^* g = √2 i (V_E^* - I) v`. -/
theorem driven_endpoint (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) {y : ℝ → Ell2}
    (hy : ContinuousOn y (Icc 0 (2 * π)))
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in 0..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0))
    (hper : y (2 * π) = y 0) :
    (1 - W (2 * π)) (y 0) = (-(Complex.I / Real.sqrt 2)) • W (2 * π) (observationAdj W g) ∧
      observationAdj W g =
        (Real.sqrt 2 * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1) (y 0) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hform := driven_formula hK hW hg hgB hy ey (2 * π) hL
  rw [hper] at hform
  have hform' : y 0 = W (2 * π) (y 0) + (-(Complex.I / Real.sqrt 2)) •
      W (2 * π) (observationAdj W g) := hform
  refine ⟨?_, ?_⟩
  · grind
  · have hu : ContinuousLinearMap.adjoint (W (2 * π)) * W (2 * π) = 1 := by
      have := (transport_mem_unitary hK hW hL)
      exact this.1
    have hV : ContinuousLinearMap.adjoint (W (2 * π)) (y 0) =
        y 0 + (-(Complex.I / Real.sqrt 2)) • observationAdj W g := by
      conv_lhs => rw [hform']
      simp [← ContinuousLinearMap.mul_apply, hu]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hV, add_sub_cancel_left,
      smul_smul]
    have : Real.sqrt 2 * Complex.I * -(Complex.I / Real.sqrt 2) = 1 := by
      field_simp
      norm_num
    rw [this, one_smul]

/-- **Lemma 4.6 (adjoint formula).**  `O_E^* g = ∫₀^L W(s)^* e₀ g(s) ds` is the adjoint of
the observation map: `⟨O_E^* g, v⟩ = ∫₀^L conj(g(s)) (O_E v)(s) ds`. -/
theorem inner_observationAdj {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) (v : Ell2) :
    inner ℂ (observationAdj W g) v =
      ∫ s in 0..(2 * π), conj (g s) * observation W v s := by
  have hL : 0 ≤ 2 * π := by positivity
  have := (innerSL ℂ v).intervalIntegral_comp_comm (intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩)
  simp  at this
  rw [observationAdj, ← inner_conj_symm, ← this, intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_of_le hL, ← integral_conj]
  simp [ContinuousLinearMap.adjoint_inner_left, observation]

/-- **Lemma 4.6 (`T_E + T_E^* = O_E O_E^*`).**  The kernels of the Volterra operator and its
adjoint combine to that of `O_E O_E^*`. -/
theorem volterraOp_add_adj {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    volterraOp W g θ + volterraOpAdj W g θ = observation W (observationAdj W g) θ := by
  have hL : 0 ≤ 2 * π := by positivity
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp [volterraKernel, ← ContinuousLinearMap.adjoint_inner_right]
  have hkc : ContinuousOn (volterraKernel W θ) (Icc 0 (2 * π)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW (basisVec 0))
  have hint : ∀ {a b : ℝ}, a ∈ Icc 0 (2 * π) → b ∈ Icc 0 (2 * π) →
      IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume a b := fun ha hb => by
    have := intervalIntegrable_smul_of_continuousOn hkc hg hgB ha hb
    simp_all [mul_comm]
  have h0 : 0 ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  simp [volterraOpAdj, hk, volterraOp, intervalIntegral.integral_add_adjacent_intervals (hint h0 hθ) (hint hθ hL'), observation, observationAdj, inner_transport_integral hW hg hgB θ h0 hL']

/-- Complex conjugation commutes with interval integrals. -/
lemma intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp [intervalIntegral, integral_conj]

end PolyaNeumann

end
