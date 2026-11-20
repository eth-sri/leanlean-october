module

public import RequestProject.CurveContinuity
public import RequestProject.IntervalFTC

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

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2)
include W

/-- The observation map `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`. -/
def observation  (v : Ell2) (θ : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ v)

/-- The adjoint observation map `O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`. -/
def observationAdj  (g : ℝ → ℂ) : Ell2 :=
  ∫ s in (0 : ℝ)..(2 * π), g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)

/-- The Volterra kernel `k(θ, s) = ⟨e₀, W(θ) W(s)^* e₀⟩`. -/
def volterraKernel  (θ s : ℝ) : ℂ :=
  inner ℂ (basisVec 0) (W θ (ContinuousLinearMap.adjoint (W s) (basisVec 0)))

/-- The Volterra operator `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds`. -/
def volterraOp  (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..θ, volterraKernel W θ s * g s

/-- The adjoint Volterra operator `(T_E^* g)(θ) = ∫_θ^L conj(k(s, θ)) g(s) ds`. -/
def volterraOpAdj  (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in θ..(2 * π), conj (volterraKernel W s θ) * g s

end

/-- Compatibility instance: real scalars commute with the adjoint star on complex operators. -/
instance instStarModuleRealCLMComplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : StarModule ℝ (E →L[ℂ] E) :=
  ⟨fun r A => by simp⟩

/-- Product rule for a family of complex-linear operators applied to a family of vectors,
differentiated with respect to a real parameter. -/
theorem hasDerivAt_clm_apply_real {A : ℝ → Ell2 →L[ℂ] Ell2} {A' : Ell2 →L[ℂ] Ell2}
    {u : ℝ → Ell2} {u' : Ell2} {θ : ℝ} (hA : HasDerivAt A A' θ) (hu : HasDerivAt u u' θ) :
    HasDerivAt (fun x => A x (u x)) (A' (u θ) + A θ u') θ :=
  ((ContinuousLinearMap.restrictScalarsL ℂ Ell2 Ell2 ℝ ℝ).hasFDerivAt.comp_hasDerivAt θ
    hA).clm_apply hu

local notation "L" => (2 * π)
local notation "J" => Icc (0 : ℝ) L

lemma intervalIntegrable_conj' {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => conj (f t)) volume a b :=
  ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩

lemma intervalIntegrable_adjoint_apply {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W J)
    {f : ℝ → Ell2} (hf : IntervalIntegrable f volume 0 L) :
    IntervalIntegrable (fun s => ContinuousLinearMap.adjoint (W s) (f s)) volume 0 L := by
  rw [intervalIntegrable_iff] at hf ⊢
  have hWa := ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hWa
  have hs := uIoc_subset_uIcc.trans (uIcc_of_le Real.two_pi_pos.le).le
  apply (hf.norm.const_mul C).mono' ((ContinuousLinearMap.apply ℂ Ell2).flip.aestronglyMeasurable_comp₂
    ((hWa.mono hs).aestronglyMeasurable measurableSet_uIoc) hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs'
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC s (hs hs')) (norm_nonneg _))

/-- Variation of constants for integrable forcing, by differentiating `W* y`. -/
theorem driven_eq_transport {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {f : ℝ → Ell2}
    (hf : IntervalIntegrable f volume 0 L) {y : ℝ → Ell2} (hy : ContinuousOn y J)
    (ey : ∀ θ ∈ J, y θ = y 0 + ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (y s) + f s)) :
    ∀ θ ∈ J, y θ = W θ (y 0 + ∫ s in (0 : ℝ)..θ, ContinuousLinearMap.adjoint (W s) (f s)) := by
  have hJ := uIcc_of_le Real.two_pi_pos.le
  have hG := (intervalIntegrable_transportCoeff_apply hK E ((uIcc_of_le Real.two_pi_pos.le).symm ▸ hy)).add hf
  have hy₁ := absolutelyContinuousOnInterval_intervalIntegral_banach hG (by simp : (0 : ℝ) ∈ uIcc 0 L)
  have hyac : AbsolutelyContinuousOnInterval y 0 L := by
    refine (((LipschitzWith.const (y 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add hy₁).congr ?_
    rw [hJ]
    exact fun θ hθ => (ey θ hθ).symm
  have hyd : ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt y (transportCoeff γ E θ (y θ) + f θ) θ := by
    filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hG] with θ hd ht
    refine ((hd ht).const_add (y 0)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using ey s (Ioo_subset_Icc_self hs)
  have hC := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn hC hM hW.1 hW.2
  have hWac := (hJ ▸ hKW : LipschitzOnWith KW W (uIcc 0 L)).absolutelyContinuousOnInterval
  have hz := absolutelyContinuousOnInterval_clm_apply
    (show AbsolutelyContinuousOnInterval (fun θ => star (W θ)) 0 L from
      ContinuousLinearMap.adjoint.lipschitz.comp_absolutelyContinuousOnInterval hWac) hyac
  have hd := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le hz
    ((intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).1
      (intervalIntegrable_adjoint_apply hW.1 hf)) (by
    filter_upwards [hyd, volterra_ae_hasDerivAt hC hM hW.1 hW.2] with θ h1 h2 ht
    have hw := (h2 ht).star
    rw [star_mul, transportCoeff_star] at hw
    refine (hasDerivAt_clm_apply_real hw (h1 ht)).congr_deriv ?_
    simp [ContinuousLinearMap.star_eq_adjoint])
  intro θ hθ
  have e := hd θ hθ
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, Real.two_pi_pos.le⟩
  rw [hW0, star_one, ContinuousLinearMap.one_apply] at e
  rw [← e, ← ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    transport_mul_adjoint hK hW hθ, ContinuousLinearMap.one_apply]


section

variable {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
include W hW

/-- `s ↦ W(s)^* e₀` is continuous on `[0, L]`. -/
lemma continuousOn_adjoint_apply 
    (x : Ell2) : ContinuousOn (fun s => ContinuousLinearMap.adjoint (W s) x) (Icc 0 (2 * π)) := by fun_prop

/-- Pulling the observation functional `⟨e₀, W(θ) ·⟩` inside the integral defining `O_E^*`:
`⟨e₀, W(θ) ∫_a^b g(s) W(s)^* e₀ ds⟩ = ∫_a^b k(θ, s) g(s) ds`. -/
lemma inner_transport_integral (θ : ℝ) {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (hab : uIcc a b ⊆ J) :
    inner ℂ (basisVec 0) (W θ (∫ s in a..b, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))) =
      ∫ s in a..b, volterraKernel W θ s * g s := by
  have hi := hg.smul_continuousOn ((continuousOn_adjoint_apply hW (basisVec 0)).mono hab)
  simpa [volterraKernel, smul_eq_mul, mul_comm] using
    (((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi).symm

end

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 L) {y : ℝ → Ell2} (hy : ContinuousOn y (Icc 0 (2 * π)))
include γ K hK E W hW g hg y hy

/-- Variation of constants for the paper's forcing `-(i/√2) g e₀`:
`y(θ) = W(θ) y(0) - (i/√2) W(θ) ∫₀^θ g(s) W(s)^* e₀ ds`. -/
theorem driven_formula 
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), y θ = W θ (y 0) + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      W θ (∫ s in (0 : ℝ)..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) := by
  set c : ℂ := -(Complex.I / (Real.sqrt 2 : ℂ))
  have hf : IntervalIntegrable (fun s => (c * g s) • basisVec 0) volume 0 L :=
    (hg.const_mul c).smul_continuousOn continuousOn_const
  intro θ hθ
  rw [driven_eq_transport hK hW hf hy ey θ hθ,
    map_add, ← map_smul]
  congr 2
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp  [map_smul, smul_smul]

/-- **Lemma 4.10 (trace identity).**  Let `y` solve the driven equation
`y' = C_E y - (i/√2) g e₀` on `[0, L]` (in integral form), with `g` bounded and measurable,
and let `v = y(0)`.  Then `h = √2 ⟨e₀, y⟩` satisfies `h = √2 O_E v - i T_E g` on `[0, L]`. -/
theorem driven_trace 
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)) :
    ∀ θ ∈ Icc 0 (2 * π), (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (y θ) =
      (Real.sqrt 2 : ℂ) * observation W (y 0) θ - Complex.I * volterraOp W g θ := by
  intro θ hθ
  rw [driven_formula hK hW hg hy ey θ hθ, inner_add_right, inner_smul_right,
    inner_transport_integral hW.1 θ (hg.mono_set' (by grind)) (uIcc_subset_Icc ⟨le_rfl, Real.two_pi_pos.le⟩ hθ)]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp
  simp only [observation, volterraOp]
  field_simp
  ring

/-- The adjoint observation of the forcing of a periodic driven solution. -/
theorem driven_endpoint 
    (ey : ∀ θ ∈ Icc 0 (2 * π), y θ = y 0 + ∫ s in (0 : ℝ)..θ,
      (transportCoeff γ E s (y s) + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0))
    (hper : y (2 * π) = y 0) :
    observationAdj W g =
      ((Real.sqrt 2 : ℂ) * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1) (y 0) := by
  have hL : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hform := driven_formula hK hW hg hy ey (2 * π) hL
  rw [hper] at hform
  have hform' : y 0 = W (2 * π) (y 0) + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      W (2 * π) (observationAdj W g) := hform
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp
  have hu : ContinuousLinearMap.adjoint (W (2 * π)) * W (2 * π) = 1 := by
    have := (transport_mem_unitary hK hW hL)
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at this
    tauto
  have hV : ContinuousLinearMap.adjoint (W (2 * π)) (y 0) =
      y 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) • observationAdj W g := by
    conv_lhs => rw [hform']
    rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, hu,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hV, add_sub_cancel_left,
    smul_smul]
  have : (Real.sqrt 2 : ℂ) * Complex.I * -(Complex.I / (Real.sqrt 2 : ℂ)) = 1 := by
    field_simp
    simp
  rw [this, one_smul]

end

section

variable {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π))) {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 L)
include W hW g hg

/-- **Lemma 4.6 (adjoint formula).**  `O_E^* g = ∫₀^L W(s)^* e₀ g(s) ds` is the adjoint of
the observation map: `⟨O_E^* g, v⟩ = ∫₀^L conj(g(s)) (O_E v)(s) ds`. -/
theorem inner_observationAdj  (v : Ell2) :
    inner ℂ (observationAdj W g) v =
      ∫ s in (0 : ℝ)..(2 * π), conj (g s) * observation W v s := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have hi := hg.smul_continuousOn ((uIcc_of_le hL).symm ▸ continuousOn_adjoint_apply hW (basisVec 0))
  have := (innerSL ℂ v).intervalIntegral_comp_comm hi
  simp only [innerSL_apply_apply] at this
  rw [observationAdj, ← inner_conj_symm, ← this, intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_of_le hL, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp  [inner_smul_right, map_mul, inner_conj_symm,
    ContinuousLinearMap.adjoint_inner_left, observation]

end

/-- **Lemma 4.6 (`T_E + T_E^* = O_E O_E^*`).** -/
theorem volterraOp_add_adj_of_intervalIntegrable {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W J)
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 L) {θ : ℝ} (hθ : θ ∈ J) :
    volterraOp W g θ + volterraOpAdj W g θ = observation W (observationAdj W g) θ := by
  have hk : ∀ s, conj (volterraKernel W s θ) = volterraKernel W θ s := fun s => by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  have hJ := uIcc_of_le Real.two_pi_pos.le
  have hkc := ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
    (continuousOn_adjoint_apply hW (basisVec 0))
  have hi : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 L :=
    hg.continuousOn_mul (hJ.symm ▸ hkc)
  simp  [volterraOpAdj, hk, volterraOp, observation, observationAdj]
  rw [intervalIntegral.integral_add_adjacent_intervals (hi.mono_set' (by grind)) (hi.mono_set' (by grind)),
    inner_transport_integral hW θ hg hJ.le]

end PolyaNeumann

end
