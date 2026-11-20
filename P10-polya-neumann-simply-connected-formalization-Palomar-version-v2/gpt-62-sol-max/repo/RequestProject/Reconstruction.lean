module

public import RequestProject.ReconGreen
public import RequestProject.ReconChordArc
public import RequestProject.ReconCompat
public import RequestProject.ReconFourier
public import RequestProject.ReconVanish
public import RequestProject.TraceH1
public import RequestProject.ReconTrace

/-!
# Cauchy reconstruction with zero conormal data (Lemmas 4.8 and 4.9)

Let `Ω` be a bounded simply connected Lipschitz domain with positively oriented boundary
parametrization `γ`, and `E > 0`. Every compatible trace `h` (a closed Lipschitz function on
`[0, 2π]` orthogonal to the conormal traces of all Herglotz waves) is the Dirichlet trace of a
Neumann eigenfunction with eigenvalue `E`, depending linearly on `h`
(`neumann_reconstruction_of_compatible`).

Construction. Let `μ_h(φ) = ∫₀^{2π} h Dφ(γ)(-iγ')` be the double layer of `h`. The unique
`u ∈ L²(ℝ²)` with `(Δ + E) u = μ_h` weakly (`IsReconSol`) is obtained by Fourier transform: by
compatibility, `μ̂_h` vanishes on the energy circle, and with a Lipschitz extension `V` of `h`
one has `u - 1_Ω V ∈ H¹(ℝ²)` (`exists_helmholtz_solution`). The function `u` vanishes outside
`Ω̄` (`ae_eq_zero_of_helmholtz`, a Rellich-type argument and unique continuation in the connected
exterior). By Green's formula (`doubleLayer_eq_integral`) and the density of smooth functions in
`H¹(Ω)`, `u|_Ω` is a Neumann eigenfunction. If `u|_Ω = 0`, then `1_Ω V ∈ H¹(ℝ²)`, which forces
`h = 0` by Green's formula (`eq_zero_of_integral_comp_mul_deriv`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-! ### Generalities -/

/-! ### Geometry of the domain -/

section Geometry

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

lemma volume_frontier_eq_zero (hγ : IsBoundaryParam Ω γ) : volume (frontier Ω) = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  rw [← hγ.image]
  exact volume_image_Icc_eq_zero hK 0 (2 * π)

lemma isConnected_exterior (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) : IsConnected (closure Ω)ᶜ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  refine isConnected_compl_closure_of_frontier hb hL ?_
  rw [← hγ.image]
  exact isPreconnected_Icc.image γ hK.continuous.continuousOn

lemma exists_exterior_radius (hb : Bornology.IsBounded Ω) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → z ∈ (closure Ω)ᶜ := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
  refine ⟨R, fun z hz hzc => ?_⟩
  have := hR hzc
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- Almost every point is in `Ω` or in the exterior. -/
lemma ae_mem_or_mem_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω ∨ z ∈ (closure Ω)ᶜ := by
  have h0 := volume_frontier_eq_zero hγ
  have := measure_eq_zero_iff_ae_notMem.mp h0
  grind [frontier, hΩo.interior_eq]

end Geometry

/-! ### The reconstructed function -/

/-- `u ∈ L²(ℝ²)` solves `(Δ + E) u = μ_h` weakly, `μ_h` the double layer of `h`. -/
def IsReconSol (γ : ℝ → ℂ) (E : ℝ) (h : ℝ → ℂ) (u : Lp ℂ 2 (volume : Measure ℂ)) : Prop :=
  ∀ φ : ℂ → ℂ, TestFunction univ φ → ∫ z, u z * (lap φ z + E * φ z) = doubleLayer γ h φ

section Recon

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {E : ℝ}

/-- Integrability of `Dφ(γ)(-iγ')` on `[0, 2π]`. -/
lemma intervalIntegrable_fderiv_comp {K : NNReal} (hK : LipschitzWith K γ) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) :
    IntervalIntegrable (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume 0
      (2 * π) := by
  have hc :=
    (hφ.continuous_fderiv one_ne_zero).comp hK.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  have hmeas : AEStronglyMeasurable (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk
        ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
  refine Measure.integrableOn_of_bounded (M := M * K) measure_Ioc_lt_top.ne hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc ‖fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))‖
      ≤ ‖fderiv ℝ φ (γ θ)‖ * ‖-(Complex.I * deriv γ θ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * K := by
        gcongr
        exact (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
        grind
        simpa using norm_deriv_le_of_lipschitz hK

lemma intervalIntegrable_doubleLayer {K : NNReal} (hK : LipschitzWith K γ) {h : ℝ → ℂ}
    (hc : ContinuousOn h (Icc 0 (2 * π))) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    IntervalIntegrable (fun θ => h θ * fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume 0
      (2 * π) :=
  (intervalIntegrable_fderiv_comp hK hφ).continuousOn_mul
    (by rwa [uIcc_of_le (by positivity)])

/-- The double layer is linear in the density (for Lipschitz `γ`, continuous densities). -/
lemma doubleLayer_add {K : NNReal} (hK : LipschitzWith K γ) {h₁ h₂ : ℝ → ℂ}
    (h₁c : ContinuousOn h₁ (Icc 0 (2 * π))) (h₂c : ContinuousOn h₂ (Icc 0 (2 * π)))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    doubleLayer γ (h₁ + h₂) φ = doubleLayer γ h₁ φ + doubleLayer γ h₂ φ := by
  unfold doubleLayer
  rw [← intervalIntegral.integral_add (intervalIntegrable_doubleLayer hK h₁c hφ)
    (intervalIntegrable_doubleLayer hK h₂c hφ)]
  congr 1
  funext θ
  grind [Pi.add_apply]

lemma doubleLayer_smul (c : ℂ) (h : ℝ → ℂ) (φ : ℂ → ℂ) :
    doubleLayer γ (c • h) φ = c * doubleLayer γ h φ := by grind [doubleLayer, intervalIntegral.integral_const_mul, Pi.smul_apply, smul_eq_mul]

/-- Uniqueness of the reconstruction. -/
lemma IsReconSol.unique (hE : 0 < E) {h : ℝ → ℂ} {u u' : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) (hu' : IsReconSol γ E h u') : u = u' := by
  have hz := ae_eq_zero_of_helmholtz hE isOpen_univ isConnected_univ (R := 0)
    (fun z _ => mem_univ z) (Lp.memLp (u - u')) (fun φ hφ => by
      have hi : ∀ v : Lp ℂ 2 (volume : Measure ℂ),
          Integrable (fun z => v z * (lap φ z + E * φ z)) := fun v =>
        integrable_mul_test (Lp.memLp v) (hφ.helm E)
      rw [integral_congr_ae (g := fun z => u z * (lap φ z + E * φ z) -
          u' z * (lap φ z + E * φ z)), integral_sub (hi u) (hi u'), hu φ hφ, hu' φ hφ, sub_self]
      filter_upwards [Lp.coeFn_sub u u'] with z hz
      rw [hz, Pi.sub_apply, sub_mul])
  rw [Measure.restrict_univ] at hz
  rw [← sub_eq_zero]
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z h1 h2
  simp_all

/-- The reconstruction vanishes outside `Ω̄`. -/
lemma IsReconSol.ae_eq_zero_exterior (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E) {h : ℝ → ℂ} {u : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), u z = 0 := by
  obtain ⟨R, hR⟩ := exists_exterior_radius hb
  refine ae_eq_zero_of_helmholtz hE isClosed_closure.isOpen_compl
    (isConnected_exterior hb hL hγ) hR (Lp.memLp u) (fun φ hφ => ?_)
  rw [hu φ hφ.univ']
  unfold doubleLayer
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero]
  intro θ hθ
  rw [uIcc_of_le (by positivity)] at hθ
  have hmem := frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ)
  have hnot := fun h' => hφ.2.2 h' hmem
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]

lemma contDiff_ePlane (ξ : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (ePlane ξ) := by
  unfold ePlane
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (Complex.reCLM.contDiff.comp (Complex.conjCLE.contDiff.mul contDiff_const))))

lemma memLp_indicator_of_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    MemLp (Ω.indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict hΩ]
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  exact MemLp.of_bound hf.restrict C (Eventually.of_forall hC)

lemma hasCompactSupport_indicator_of_bounded {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (f : ℂ → ℂ) : HasCompactSupport (Ω.indicator f) :=
  IsCompact.of_isClosed_subset hb.isCompact_closure (isClosed_tsupport _)
    (closure_mono (support_indicator_subset))

lemma integral_indicator_combo {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (V : ℂ → ℂ)
    (G' : Fin 2 → ℂ → ℂ) (L : ℂ → ℂ) (M : Fin 2 → ℂ → ℂ) :
    ∫ z, (Ω.indicator V z * L z + ∑ i : Fin 2, Ω.indicator (G' i) z * M i z) =
      ∫ z in Ω, (V z * L z + ∑ i : Fin 2, G' i z * M i z) := by
  rw [← integral_indicator hΩ]
  congr 1
  funext z
  by_cases hz : z ∈ Ω <;> simp [hz]

private lemma integral_mul_congr_ae {μ : Measure ℂ} {f g k : ℂ → ℂ} (h : f =ᵐ[μ] g) :
    (∫ z, f z * k z ∂μ) = ∫ z, g z * k z ∂μ :=
  integral_congr_ae (h.mul .rfl)

private lemma integral_mul_lap_of_weakGrad {w : ℂ → ℂ} {gw : Fin 2 → ℂ → ℂ}
    (hw : MemLp w 2 volume) (hwg : IsWeakGradOn univ w gw) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    ∫ z, w z * lap φ z = -∑ i : Fin 2, ∫ z, gw i z * dirD φ (coordDir i) z := by
  have h (i : Fin 2) := hwg (dirD φ (coordDir i)) (hφ.dirD _) i
  simp only [lap, mul_add, Fin.sum_univ_two]
  rw [integral_add (integrable_mul_test hw ((hφ.dirD 1).dirD 1))
      (integrable_mul_test hw ((hφ.dirD Complex.I).dirD Complex.I))]
  change (∫ z, w z * fderiv ℝ (dirD φ (coordDir 0)) z (coordDir 0)) +
      (∫ z, w z * fderiv ℝ (dirD φ (coordDir 1)) z (coordDir 1)) = _
  rw [h 0, h 1, neg_add]

/-- Existence of the reconstruction, with its structure `u = 1_Ω V + w`, `w ∈ H¹(ℝ²)`. -/
theorem exists_reconSol (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E) {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) :
    ∃ u : Lp ℂ 2 (volume : Measure ℂ), IsReconSol γ E h u ∧
      ∃ (V : ℂ → ℂ) (K : NNReal) (w : ℂ → ℂ) (gw : Fin 2 → ℂ → ℂ), LipschitzWith K V ∧
        HasCompactSupport V ∧ (∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ) ∧ MemLp w 2 volume ∧
        (∀ i, MemLp (gw i) 2 volume) ∧ IsWeakGradOn univ w gw ∧
        ((u : ℂ → ℂ) =ᵐ[volume] fun z => Ω.indicator V z + w z) ∧
        ∀ φ : ℂ → ℂ, TestFunction univ φ →
          ∑ i : Fin 2, ∫ z, (Ω.indicator (dirD V (coordDir i)) z + gw i z) * dirD φ (coordDir i) z =
            (E : ℂ) * ∫ z, u z * φ z := by
  have hΩm := hL.1.1.measurableSet
  obtain ⟨⟨Kh, hKh⟩, hper, -⟩ := id hh
  obtain ⟨V, ⟨KV, hV⟩, hVc, hVh⟩ := exists_lipschitz_extension_of_trace hL hγ hKh hper
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  set G : ℂ → ℂ := Ω.indicator V with hG
  set G' : Fin 2 → ℂ → ℂ := fun i => Ω.indicator (dirD V (coordDir i)) with hG'
  have hGm :=
    memLp_indicator_of_bound hb hΩm hV.continuous.aestronglyMeasurable hCV
  have hG'm : ∀ i, MemLp (G' i) 2 volume := fun i =>
    memLp_indicator_of_bound hb hΩm (C := KV * ‖coordDir i‖)
      (measurable_fderiv_apply_const ℝ V (coordDir i)).aestronglyMeasurable
      (fun z => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hV) (norm_nonneg _)))
  have hgreen : ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ →
      ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) =
        doubleLayer γ h φ := by
    intro φ hφ
    rw [integral_indicator_combo hΩm V (fun i => dirD V (coordDir i)) (lap φ)
      (fun i => dirD φ (coordDir i)), doubleLayer_eq_integral hb hL hγ hV hVc hVh hφ]
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨w, gw, hw, hgw, hwg, heq⟩ := exists_helmholtz_solution hE hGm
    (hasCompactSupport_indicator_of_bounded hb V) hG'm
    (fun i => hasCompactSupport_indicator_of_bounded hb _)
    (fun ξ hξ => by
      rw [hgreen _ (contDiff_ePlane ξ)]
      exact doubleLayer_ePlane_eq_zero hK hE hh hξ)
  have hu := (hGm.add hw).coeFn_toLp
  refine ⟨_, ?_, V, KV, w, gw, hV, hVc, hVh, hw, hgw, hwg, hu,
    fun φ hφ => (heq φ hφ).trans (congrArg ((E : ℂ) * ·) (integral_mul_congr_ae hu).symm)⟩
  intro φ hφ
  have hL := integral_mul_lap_of_weakGrad hw hwg hφ
  have hG'd (i : Fin 2) := integrable_mul_test (hG'm i) (hφ.dirD (coordDir i))
  have hgd (i : Fin 2) := integrable_mul_test (hgw i) (hφ.dirD (coordDir i))
  have hsum (i : Fin 2) := integral_add (hG'd i) (hgd i)
  have hEq := heq φ hφ
  simp_rw [add_mul, hsum, Finset.sum_add_distrib] at hEq
  rw [integral_mul_congr_ae hu, ← hgreen _ hφ.1]
  simp_rw [mul_add]
  rw [integral_add (integrable_mul_test (hGm.add hw) hφ.lap)
    (integrable_mul_test (hGm.add hw) (hφ.const_mul _))]
  have hmass : (∫ z, (G z + w z) * ((E : ℂ) * φ z)) = (E : ℂ) * ∫ z, (G z + w z) * φ z := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun z => mul_left_comm _ _ _)
  have hLap : (∫ z, (G z + w z) * lap φ z) =
      (∫ z, G z * lap φ z) - ∑ i : Fin 2, ∫ z, gw i z * dirD φ (coordDir i) z := by
    simp_rw [add_mul]
    rw [integral_add (integrable_mul_test hGm hφ.lap) (integrable_mul_test hw hφ.lap), hL, sub_eq_add_neg]
  change (∫ z, (G z + w z) * lap φ z) + (∫ z, (G z + w z) * ((E : ℂ) * φ z)) = _
  rw [hmass, hLap,
    integral_add (integrable_mul_test hGm hφ.lap) (integrable_finset_sum _ fun i _ => hG'd i),
    integral_finset_sum _ fun i _ => hG'd i]
  simp_rw [add_mul]
  linear_combination -hEq

/-- The restriction of an `L²(ℝ²)` function to `Ω`. -/
def restrictL2 (Ω : Set ℂ) : Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] L2 Ω where
  toFun u := MemLp.toLp u ((Lp.memLp u).restrict Ω)
  map_add' u v := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    exact ae_restrict_of_ae (Lp.coeFn_add u v)
  map_smul' c u := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    exact ae_restrict_of_ae (Lp.coeFn_smul c u)

lemma restrictL2_coeFn (Ω : Set ℂ) (u : Lp ℂ 2 (volume : Measure ℂ)) :
    (restrictL2 Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] u :=
  MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω)

/-! ### Structure of the reconstruction -/

lemma continuousOn_of_mem_compatibleTraces {γ : ℝ → ℂ} {E : ℝ} {h : ℝ → ℂ} (hh : h ∈ compatibleTraces γ E) :
    ContinuousOn h (Icc 0 (2 * π)) := by
  obtain ⟨⟨K, hK⟩, -, -⟩ := hh
  exact hK.continuousOn



/-- A function vanishing a.e. off `Ω̄` integrates to its integral over `Ω`. -/
lemma integral_eq_setIntegral_of_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω)
    {f : ℂ → ℂ} (hf : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), f z = 0) :
    ∫ z, f z = ∫ z in Ω, f z := by
  refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
  have hf' := (ae_restrict_iff' isClosed_closure.isOpen_compl.measurableSet).mp hf
  filter_upwards [hf', ae_mem_or_mem_exterior hγ hΩo] with x; grind

/-- `L²` functions are locally integrable. -/
lemma MemLp.locallyIntegrable_two {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    LocallyIntegrable f volume :=
  hf.locallyIntegrable (by norm_num)

/-- Bounded measurable functions times test functions are integrable. -/
lemma integrable_bdd_mul_test {f : ℂ → ℂ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {D : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction D φ) : Integrable (fun z => f z * φ z) μ :=
  ((hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1).bdd_mul hf
    (Eventually.of_forall hC)

lemma norm_dirD_le_of_lipschitz {V : ℂ → ℂ} {K : NNReal} (hV : LipschitzWith K V) (v z : ℂ) :
    ‖dirD V v z‖ ≤ K * ‖v‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hV) (norm_nonneg _))

lemma aestronglyMeasurable_dirD (V : ℂ → ℂ) (v : ℂ) {μ : Measure ℂ} :
    AEStronglyMeasurable (dirD V v) μ :=
  (measurable_fderiv_apply_const ℝ V v).aestronglyMeasurable

lemma coordDir_zero : coordDir 0 = 1 := rfl
lemma coordDir_one : coordDir 1 = Complex.I := rfl

section Structure

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {E : ℝ} {V : ℂ → ℂ} {KV : NNReal} {w : ℂ → ℂ}
  {gw : Fin 2 → ℂ → ℂ}

/-- The weak gradient of `w` vanishes outside `Ω̄` when `w` does. -/
lemma gw_ae_eq_zero_exterior (hwg : IsWeakGradOn univ w gw) (hgw : ∀ i, MemLp (gw i) 2 volume)
    (hw0 : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), w z = 0) (i : Fin 2) :
    ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), gw i z = 0 := by
  have hU : IsOpen (closure Ω)ᶜ := isClosed_closure.isOpen_compl
  refine ae_eq_zero_of_integral_mul_test hU (MemLp.locallyIntegrable_two (hgw i)) (fun φ hφ => ?_)
  have e := hwg φ hφ.univ' i
  have hz : ∫ z, w z * fderiv ℝ φ z (coordDir i) = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)), integral_zero]
    have hw0' := (ae_restrict_iff' hU.measurableSet).mp hw0
    filter_upwards [hw0'] with z hz
    by_cases hzU : z ∈ (closure Ω)ᶜ
    simp_all
    · have := fun h' => hzU (hφ.2.2 h')
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
  simp_all

end Structure

/-- The restriction of the reconstruction to `Ω` is a Neumann eigenfunction. -/
theorem IsReconSol.restrict_spec (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E) {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) {u : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) : restrictL2 Ω u ∈ neumannEigenspace Ω E ∧
      (restrictL2 Ω u = 0 → ∀ θ ∈ Icc 0 (2 * π), h θ = 0) := by
  have hΩo := hL.1.1
  have hΩm := hΩo.measurableSet
  have hUm : MeasurableSet (closure Ω)ᶜ := isClosed_closure.isOpen_compl.measurableSet
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  obtain ⟨u', hu', V, KV, w, gw, hV, hVc, hVh, hw, hgw, hwg, hue, hweak⟩ :=
    exists_reconSol hb hL hγ hE hh
  obtain rfl := hu'.unique hE hu
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  have hext := hu'.ae_eq_zero_exterior hb hL hγ hE
  have hw0 : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), w z = 0 := by
    filter_upwards [hext, ae_restrict_of_ae hue, ae_restrict_mem hUm] with z h1 h2 h3
    have hzΩ := fun h' => h3 (subset_closure h')
    simp_all
  have hgw0 := gw_ae_eq_zero_exterior hwg hgw hw0
  have hgm : ∀ i, MemLp (fun z => dirD V (coordDir i) z + gw i z) 2 (volume.restrict Ω) :=
    fun i => (MemLp.of_bound (aestronglyMeasurable_dirD V _) _
      (Eventually.of_forall (norm_dirD_le_of_lipschitz hV _))).add ((hgw i).restrict Ω)
  set g : Fin 2 → L2 Ω := fun i => (hgm i).toLp _ with hgdef
  have hUe : (restrictL2 Ω u' : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => V z + w z := by
    filter_upwards [restrictL2_coeFn Ω u', ae_restrict_of_ae hue, ae_restrict_mem hΩm]
      with z h1 h2 h3
    simp_all
  have testIntegral {a b φ : ℂ → ℂ} (ha : a =ᵐ[volume.restrict Ω] b)
      (hφ : TestFunction Ω φ) : (∫ z in Ω, a z * φ z) = ∫ z, b z * φ z :=
    (integral_mul_congr_ae ha).trans (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      by rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hφ.2.2 ht)), mul_zero])
  have hg : IsWeakGradient Ω (restrictL2 Ω u') g := by
    intro φ hφ i
    let d := dirD φ (coordDir i)
    change (∫ z in Ω, restrictL2 Ω u' z * d z) = -∫ z in Ω, g i z * φ z
    rw [testIntegral hUe (hφ.dirD _), testIntegral (hgm i).coeFn_toLp hφ]
    simp_rw [add_mul]
    rw [integral_add (integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV
      (hφ.univ'.dirD _)) (integrable_mul_test hw (hφ.univ'.dirD _)),
      integral_add (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
        (norm_dirD_le_of_lipschitz hV _) hφ.univ') (integrable_mul_test (hgw i) hφ.univ')]
    unfold dirD
    rw [integral_mul_fderiv_of_lipschitz hV (hφ.1.of_le (by trivial)) hφ.2.1, hwg φ hφ.univ' i, neg_add]
  refine ⟨⟨g, hg, ?_⟩, ?_⟩
  · -- the eigenvalue equation, by density of smooth functions
    intro v hv hvg
    let L (u : NeumannH1 Ω) := ∑ i, inner ℂ (h1Gradient Ω i u) (g i)
    let R (u : NeumannH1 Ω) := (E : ℂ) * inner ℂ (h1Value Ω u) (restrictL2 Ω u')
    have hL' : Continuous L := continuous_finset_sum _ fun i _ =>
      (h1Gradient Ω i).continuous.inner continuous_const
    have hR' : Continuous R := continuous_const.mul ((h1Value Ω).continuous.inner continuous_const)
    have hkey (φ : ℂ → ℂ) (hφ : TestFunction univ φ) :
        ∑ i : Fin 2, ∫ z in Ω, (dirD V (coordDir i) z + gw i z) * dirD φ (coordDir i) z =
          (E : ℂ) * ∫ z in Ω, u' z * φ z := by
      have hext' : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), u' z * φ z = 0 := by
        filter_upwards [hext] with z hz using by simp [hz]
      rw [← integral_eq_setIntegral_of_exterior hγ hΩo hext']
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (hweak φ hφ)
      rw [integral_eq_setIntegral_of_exterior hγ hΩo (f := fun z =>
        (Ω.indicator (dirD V (coordDir i)) z + gw i z) * dirD φ (coordDir i) z)]
      · exact setIntegral_congr_fun hΩm fun z hz => by simp [hz]
      · filter_upwards [hgw0 i, ae_restrict_mem hUm] with z hz hzc
        simp [hz, Set.indicator_of_notMem (fun h => hzc (subset_closure h))]
    have hEq := (denseRange_smoothTraceH1Lin hb hL).equalizer hL' hR' (funext fun φ => by
      simp only [Function.comp_apply, L, R, smoothTraceH1Lin_apply, h1Gradient_smoothTraceH1,
        h1Value_smoothTraceH1, L2.inner_def, RCLike.inner_apply']
      convert hkey _ φ.property.conj using 1
      · refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
        filter_upwards [(smoothTraceTests_memLp_deriv Ω φ i).coeFn_toLp, (hgm i).coeFn_toLp] with z h1 h2
        rw [h1, h2, dirD_conj (φ.property.1.of_le (by trivial)), mul_comm]
        rfl
      · congr 1
        refine integral_congr_ae ?_
        filter_upwards [(smoothTraceTests_memLp Ω φ).coeFn_toLp, restrictL2_coeFn Ω u'] with z h1 h2
        simp [h1, h2, mul_comm])
    exact congrFun hEq (h1Vector hvg)

  · intro h0
    have hg0 : g = 0 := IsWeakGradient.eq_zero_of_zero hΩo (h0 ▸ hg)
    have hwV : w =ᵐ[volume.restrict Ω] fun z => -V z := by
      filter_upwards [h0 ▸ hUe, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with z h1 h2
      simp only [h2, Pi.zero_apply] at h1
      linear_combination -h1
    have hgwV (i : Fin 2) : gw i =ᵐ[volume.restrict Ω] fun z => -dirD V (coordDir i) z := by
      have hge : (g i : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => dirD V (coordDir i) z + gw i z :=
        (hgm i).coeFn_toLp
      filter_upwards [hg0 ▸ hge, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with z h1 h2
      simp only [Pi.zero_apply, h2] at h1
      linear_combination -h1
    have hstar {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (i : Fin 2) :
        Integrable (fun z => V z * dirD φ (coordDir i) z + dirD V (coordDir i) z * φ z)
          (volume.restrict Ω) ∧
        (∫ z in Ω, V z * dirD φ (coordDir i) z + dirD V (coordDir i) z * φ z) = 0 := by
      have hA := integrable_bdd_mul_test (μ := volume.restrict Ω)
        hV.continuous.aestronglyMeasurable hCV (hφ.dirD (coordDir i))
      have hB := integrable_bdd_mul_test (μ := volume.restrict Ω)
        (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV (coordDir i)) hφ
      refine ⟨hA.add hB, ?_⟩
      have e := hwg φ hφ i
      rw [integral_eq_setIntegral_of_exterior hγ hΩo (f := fun z => w z * _)
          (hw0.mono fun z hz => by simp [hz]),
        integral_eq_setIntegral_of_exterior hγ hΩo (f := fun z => gw i z * _)
          ((hgw0 i).mono fun z hz => by simp [hz]), integral_mul_congr_ae hwV,
        integral_mul_congr_ae (hgwV i)] at e
      rw [integral_add hA hB]
      simp only [neg_mul, integral_neg, neg_neg] at e
      exact neg_eq_iff_add_eq_zero.mp e
    have hdbar (φ : ℂ → ℂ) (hφ : TestFunction univ φ) :
        ∫ z in Ω, dbar (fun z => V z * φ z) z = 0 := by
      let q (i : Fin 2) z := V z * dirD φ (coordDir i) z + dirD V (coordDir i) z * φ z
      have he : dbar (fun z => V z * φ z) =ᵐ[volume.restrict Ω]
          fun z => (q 0 z + Complex.I * q 1 z) / 2 := by
        refine ae_restrict_of_ae ?_
        filter_upwards [hV.ae_differentiableAt] with z hz
        simp only [dbar, q, dirD, fderiv_fun_mul hz ((hφ.1.differentiable (by simp)) z),
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordDir_zero, coordDir_one]
        ring
      rw [integral_congr_ae he, integral_div, integral_add (hstar hφ 0).1 ((hstar hφ 1).1.const_mul _),
        integral_const_mul, (hstar hφ 0).2, (hstar hφ 1).2]
      simp
    -- Green's formula
    have hint : ∀ φ : ℂ → ℂ, TestFunction univ φ →
        ∫ θ in (0 : ℝ)..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0 := by
      intro φ hφ
      obtain ⟨Cφ, hCφ⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
      obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
      obtain ⟨Kp, hKp⟩ := lipschitzWith_mul_of_bounded hV hKφ hCV hCφ
      have hg := integral_boundary_eq_dbar hb hL hγ hKp (hVc.mul_right)
      rw [hdbar φ hφ, mul_zero] at hg
      rw [← hg]
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le (by positivity)] at hθ
      simp_all
    exact eq_zero_of_integral_comp_mul_deriv hγ (continuousOn_of_mem_compatibleTraces hh) hint

/-- The reconstruction map `h ↦ u`, as a function on compatible traces. -/
def reconFun (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E)
    (h : compatibleTraces γ E) : Lp ℂ 2 (volume : Measure ℂ) :=
  Classical.choose (exists_reconSol hb hL hγ hE h.2)

lemma reconFun_spec (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E)
    (h : compatibleTraces γ E) : IsReconSol γ E h (reconFun hb hL hγ hE h) :=
  (Classical.choose_spec (exists_reconSol hb hL hγ hE h.2)).1

/-- Lemma 4.8 with zero conormal data and the uniqueness of Lemma 4.9: a linear reconstruction
map from compatible traces to Neumann eigenfunctions that only kills traces vanishing on
`[0, 2π]`. -/
theorem neumann_reconstruction_of_compatible (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (hE : 0 < E) :
    ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ Icc 0 (2 * π), (h : ℝ → ℂ) θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  set F := reconFun hb hL hγ hE with hF
  have hspec := reconFun_spec hb hL hγ hE
  have hadd : ∀ h₁ h₂ : compatibleTraces γ E, F (h₁ + h₂) = F h₁ + F h₂ := by
    intro h₁ h₂
    refine (hspec (h₁ + h₂)).unique hE ?_
    intro φ hφ
    have e1 := hspec h₁ φ hφ
    have e2 := hspec h₂ φ hφ
    have hi : ∀ u : Lp ℂ 2 (volume : Measure ℂ),
        Integrable (fun z => u z * (lap φ z + E * φ z)) := fun u =>
      integrable_mul_test (Lp.memLp u)
        (hφ.helm E)
    rw [integral_congr_ae (g := fun z => F h₁ z * (lap φ z + E * φ z) +
        F h₂ z * (lap φ z + E * φ z)), integral_add (hi _) (hi _), e1, e2,
      Submodule.coe_add, doubleLayer_add hK (continuousOn_of_mem_compatibleTraces h₁.2)
        (continuousOn_of_mem_compatibleTraces h₂.2) (hφ.1.of_le (by trivial))]
    filter_upwards [Lp.coeFn_add (F h₁) (F h₂)] with z hz
    rw [hz, Pi.add_apply, add_mul]
  have hsmul : ∀ (c : ℂ) (h : compatibleTraces γ E), F (c • h) = c • F h := by
    intro c h
    refine (hspec (c • h)).unique hE ?_
    intro φ hφ
    rw [integral_congr_ae (g := fun z => c * (F h z * (lap φ z + E * φ z))),
      integral_const_mul, hspec h φ hφ, Submodule.coe_smul, doubleLayer_smul]
    filter_upwards [Lp.coeFn_smul c (F h)] with z hz
    rw [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let Flin : compatibleTraces γ E →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨((restrictL2 Ω).comp Flin).codRestrict (neumannEigenspace Ω E)
    (fun h => ((hspec h).restrict_spec hb hL hγ hE h.2).1), fun h h0 => ?_⟩
  have h0' : restrictL2 Ω (F h) = 0 := by
    have := congrArg Subtype.val h0
    assumption
  exact ((hspec h).restrict_spec hb hL hγ hE h.2).2 h0'

end Recon

end PolyaNeumann
