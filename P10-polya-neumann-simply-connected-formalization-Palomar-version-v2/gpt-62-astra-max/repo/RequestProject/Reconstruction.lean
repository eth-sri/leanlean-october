module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.ReconGreen
public import RequestProject.ReconChordArc
public import RequestProject.ReconCompat
public import RequestProject.ReconFourier
public import RequestProject.ReconVanish
public import RequestProject.ReconDensity
public import RequestProject.ReconTrace
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

/-! ### Generalities -/

/-! ### Geometry of the domain -/

section Geometry

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

lemma volume_frontier_eq_zero (hγ : IsBoundaryParam Ω γ) : volume (frontier Ω) = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  rw [← hγ.image]
  exact volume_image_Icc_eq_zero hK 0 anglePeriod

lemma isConnected_exterior (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) : IsConnected (closure Ω)ᶜ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  refine isConnected_compl_closure_of_frontier hb hL ?_
  rw [← hγ.image]
  exact isPreconnected_Icc.image γ hK.continuous.continuousOn

lemma exists_exterior_radius (hb : Bornology.IsBounded Ω) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → z ∈ (closure Ω)ᶜ := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
  refine ⟨R, fun z hz hzc => ?_⟩
  have := hR hzc
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- Almost every point is in `Ω` or in the exterior. -/
lemma ae_mem_or_mem_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω ∨ z ∈ (closure Ω)ᶜ := by
  
  have  := measure_eq_zero_iff_ae_notMem.mp (volume_frontier_eq_zero hγ)
  filter_upwards [this] with z hz
  by_cases hzc : z ∈ closure Ω
  · left
    rw [frontier, hΩo.interior_eq] at hz
    by_contra hzΩ
    exact (by grind)
  · right; exact hzc

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
      anglePeriod := by
  have hc  :=
    (hφ.continuous_fderiv one_ne_zero).comp hK.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc  (b := anglePeriod)).exists_bound_of_continuousOn
    hc.continuousOn
  
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
  refine Measure.integrableOn_of_bounded (M := M * K) measure_Ioc_lt_top.ne (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
    (hc.aestronglyMeasurable.prodMk
      ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc _
      ≤ _ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
        gcongr
        · exact (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
        · exact hM θ (Ioc_subset_Icc_self hθ)
        · rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
          exact norm_deriv_le_of_lipschitz hK

lemma intervalIntegrable_doubleLayer {K : NNReal} (hK : LipschitzWith K γ) {h : ℝ → ℂ}
    (hc : ContinuousOn h angleInterval) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    IntervalIntegrable (fun θ => h θ * fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume 0
      anglePeriod :=
  (intervalIntegrable_fderiv_comp hK hφ).continuousOn_mul
    (by rwa [uIcc_of_le (by positivity)])

/-- The double layer is linear in the density (for Lipschitz `γ`, continuous densities). -/
lemma doubleLayer_add {K : NNReal} (hK : LipschitzWith K γ) {h₁ h₂ : ℝ → ℂ}
    (h₁c : ContinuousOn h₁ angleInterval) (h₂c : ContinuousOn h₂ angleInterval)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    doubleLayer γ (h₁ + h₂) φ = doubleLayer γ h₁ φ + doubleLayer γ h₂ φ := by
  unfold doubleLayer
  rw [← intervalIntegral.integral_add (intervalIntegrable_doubleLayer hK h₁c hφ)
    (intervalIntegrable_doubleLayer hK h₂c hφ)]
  congr 1
  funext θ
  simp only [Pi.add_apply]
  ring

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (hE : 0 < E)

lemma doubleLayer_smul (c : ℂ) (h : ℝ → ℂ) (φ : ℂ → ℂ) :
    doubleLayer γ (c • h) φ = c * doubleLayer γ h φ := by
  unfold doubleLayer
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  simp [smul_eq_mul] <;> ring

include hE in
/-- Uniqueness of the reconstruction. -/
lemma IsReconSol.unique {h : ℝ → ℂ} {u u' : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) (hu' : IsReconSol γ E h u') : u = u' := by
  have hz := ae_eq_zero_of_helmholtz hE isOpen_univ isConnected_univ (R := 0)
    (fun z _ => mem_univ z) (Lp.memLp (u - u')) (fun φ hφ => by
      have hi : ∀ v : Lp ℂ 2 (volume : Measure ℂ),
          Integrable (fun z => v z * (lap φ z + E * φ z)) := fun v =>
        integrable_mul_test (Lp.memLp v) (hφ.helm E)
      rw [integral_congr_ae , integral_sub (hi u) (hi u'), hu φ hφ, hu' φ hφ, sub_self]
      filter_upwards [Lp.coeFn_sub u u'] with z hz
      rw [hz, Pi.sub_apply, sub_mul])
  rw [Measure.restrict_univ] at hz
  rw [← sub_eq_zero]
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 volume] with z h1 h2
  rw [h1, h2]; rfl

include hE hL hb hγ in
/-- The reconstruction vanishes outside `Ω̄`. -/
lemma IsReconSol.ae_eq_zero_exterior {h : ℝ → ℂ} {u : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), u z = 0 := by
  obtain ⟨R, hR⟩ := exists_exterior_radius hb
  refine ae_eq_zero_of_helmholtz hE isClosed_closure.isOpen_compl
    (isConnected_exterior hb hL hγ) hR (Lp.memLp u) (fun φ hφ => ?_)
  rw [hu φ hφ.univ']
  unfold doubleLayer
  rw [intervalIntegral.integral_congr , intervalIntegral.integral_zero]
  intro θ hθ
  rw [uIcc_of_le (by positivity)] at hθ
  
  have hnot  := fun h' => hφ.2.2 h' (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ))
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]

lemma contDiff_ePlane (ξ : ℂ) : ContDiff ℝ ∞ (ePlane ξ) := by
  
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (Complex.reCLM.contDiff.comp (Complex.conjCLE.contDiff.mul contDiff_const))))

lemma memLp_indicator_of_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    MemLp (Ω.indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict hΩ]
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  exact MemLp.of_bound hf.restrict C (Eventually.of_forall hC)

lemma hasCompactSupport_indicator_of_bounded {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (f : ℂ → ℂ) : HasCompactSupport (Ω.indicator f) :=
  IsCompact.of_isClosed_subset hb.isCompact_closure (isClosed_tsupport _)
    (closure_mono support_indicator_subset)

lemma integral_indicator_combo {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (V : ℂ → ℂ)
    (G' : Fin 2 → ℂ → ℂ) (L : ℂ → ℂ) (M : Fin 2 → ℂ → ℂ) :
    ∫ z, (Ω.indicator V z * L z + ∑ i : Fin 2, Ω.indicator (G' i) z * M i z) =
      ∫ z in Ω, (V z * L z + ∑ i : Fin 2, G' i z * M i z) := by
  rw [← integral_indicator hΩ]
  congr 1
  funext z
  by_cases hz : z ∈ Ω <;> simp [hz]

include hE hL hb hγ in
/-- Existence of the reconstruction, with its structure `u = 1_Ω V + w`, `w ∈ H¹(ℝ²)`. -/
theorem exists_reconSol {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) :
    ∃ u : Lp ℂ 2 (volume : Measure ℂ), IsReconSol γ E h u ∧
      ∃ (V : ℂ → ℂ) (K : NNReal) (w : ℂ → ℂ) (gw : Fin 2 → ℂ → ℂ), LipschitzWith K V ∧
        HasCompactSupport V ∧ (∀ θ ∈ angleInterval, V (γ θ) = h θ) ∧ MemLp w 2 volume ∧
        (∀ i, MemLp (gw i) 2 volume) ∧ IsWeakGradOn univ w gw ∧
        (u : ℂ → ℂ) =ᵐ[volume] fun z => Ω.indicator V z + w z := by
  have hΩm  := hL.1.1.measurableSet
  obtain ⟨⟨Kh, hKh⟩, hper, -⟩ := id hh
  obtain ⟨V, ⟨KV, hV⟩, hVc, hVh⟩ := exists_lipschitz_extension_of_trace hL hγ hKh hper
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  set G : ℂ → ℂ := Ω.indicator V with hG
  set G' : Fin 2 → ℂ → ℂ := fun i => Ω.indicator (dirD V (coordDir i)) with hG'
  have hGm  :=
    memLp_indicator_of_bound hb hΩm hV.continuous.aestronglyMeasurable hCV
  have hG'm : ∀ i, MemLp (G' i) 2 volume := fun i =>
    memLp_indicator_of_bound hb hΩm 
      (measurable_fderiv_apply_const ℝ V (coordDir i)).aestronglyMeasurable
      (fun z => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hV) (norm_nonneg _)))
  have hgreen : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ →
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
  refine ⟨(hGm.add hw).toLp _, fun φ hφ => ?_, V, KV, w, gw, hV, hVc, hVh, hw, hgw, hwg,
    MemLp.coeFn_toLp _⟩
  rw [integral_congr_ae , heq φ hφ,
    hgreen φ hφ.1]
  filter_upwards [MemLp.coeFn_toLp (hGm.add hw)] with z hz
  simp [hz]

end

/-- The restriction of an `L²(ℝ²)` function to `Ω`. -/
def restrictL2 (Ω : Set ℂ) : Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] L2 Ω where
  toFun u := MemLp.toLp u ((Lp.memLp u).restrict Ω)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (u + v)).restrict Ω),
      Lp.coeFn_add (MemLp.toLp u ((Lp.memLp u).restrict Ω)) (MemLp.toLp v ((Lp.memLp v).restrict Ω)),
      MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω), MemLp.coeFn_toLp ((Lp.memLp v).restrict Ω),
      ae_restrict_of_ae (Lp.coeFn_add u v)] with z h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • u)).restrict Ω),
      Lp.coeFn_smul c (MemLp.toLp u ((Lp.memLp u).restrict Ω)),
      MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω),
      ae_restrict_of_ae (Lp.coeFn_smul c u)] with z h1 h2 h3 h4
    simp [h1, h2, h3, h4]

lemma restrictL2_coeFn (Ω : Set ℂ) (u : Lp ℂ 2 (volume : Measure ℂ)) :
    (restrictL2 Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] u :=
  MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω)

/-! ### Structure of the reconstruction -/

lemma continuousOn_of_mem_compatibleTraces {γ : ℝ → ℂ} {E : ℝ} {h : ℝ → ℂ} (hh : h ∈ compatibleTraces γ E) :
    ContinuousOn h angleInterval := by
  obtain ⟨⟨K, hK⟩, -, -⟩ := hh
  exact hK.continuousOn

/-- A function vanishing a.e. off `Ω̄` integrates to its integral over `Ω`. -/
lemma integral_eq_setIntegral_of_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω)
    {f : ℂ → ℂ} (hf : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), f z = 0) :
    ∫ z, f z = ∫ z in Ω, f z := by
  refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
  
  filter_upwards [((ae_restrict_iff' isClosed_closure.isOpen_compl.measurableSet).mp hf), ae_mem_or_mem_exterior hγ hΩo] with z h1 h2 h3
  rcases h2 with h2 | h2
  · exact absurd h2 h3
  · exact h1 h2

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
    rw [integral_congr_ae , integral_zero]
    
    filter_upwards [((ae_restrict_iff' hU.measurableSet).mp hw0)] with z hz
    by_cases hzU : z ∈ (closure Ω)ᶜ
    · simp [*]
    · have  := fun h' => hzU (hφ.2.2 h')
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
  rw [hz, eq_comm, neg_eq_zero] at e
  exact e

/-- The key identity: `∑ᵢ ∫_Ω ∂ᵢψ (∂ᵢV + gwᵢ) = E ∫_Ω ψ u` for test functions `ψ`. -/
lemma recon_key_identity (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {h : ℝ → ℂ}
    (hV : LipschitzWith KV V) (hVc : HasCompactSupport V)
    (hVh : ∀ θ ∈ angleInterval, V (γ θ) = h θ) (hw : MemLp w 2 volume)
    (hgw : ∀ i, MemLp (gw i) 2 volume) (hwg : IsWeakGradOn univ w gw)
    {u : Lp ℂ 2 (volume : Measure ℂ)} (hu : IsReconSol γ E h u)
    (hue : (u : ℂ → ℂ) =ᵐ[volume] fun z => Ω.indicator V z + w z)
    (hext : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), u z = 0)
    (hgw0 : ∀ i, ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), gw i z = 0)
    {ψ : ℂ → ℂ} (hψ : TestFunction univ ψ) :
    ∑ i : Fin 2, ∫ z in Ω, dirD ψ (coordDir i) z * (dirD V (coordDir i) z + gw i z) =
      E * ∫ z in Ω, ψ z * u z := by
  have hΩo  := hL.1.1
  have hΩm  := hΩo.measurableSet
  
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  have h1 := hu ψ hψ
  rw [doubleLayer_eq_integral hb hL hγ hV hVc hVh hψ.1] at h1
  -- split the left side
  
  
  rw [show (fun z => u z * (lap ψ z + E * ψ z)) =
      fun z => u z * lap ψ z + u z * (E * ψ z) from funext fun z => mul_add _ _ _,
    integral_add (integrable_mul_test (Lp.memLp u) hψ.lap) (integrable_mul_test (Lp.memLp u) (hψ.const_mul _))] at h1
  -- the Laplacian term
  have hlap : ∫ z, u z * lap ψ z =
      (∫ z in Ω, V z * lap ψ z) - ∑ i : Fin 2, ∫ z in Ω, gw i z * dirD ψ (coordDir i) z := by
    
    
    rw [integral_congr_ae ,
      integral_add (integrable_bdd_mul_test (hV.continuous.aestronglyMeasurable.indicator hΩm)
        (C := CV) (fun z => by
          by_cases hz : z ∈ Ω
          · simp [*]
          · simp [hz]; exact (norm_nonneg _).trans (hCV z)) hψ.lap) (integrable_mul_test hw hψ.lap)]
    swap
    · filter_upwards [hue] with z hz
      rw [hz, add_mul]
    have hVΩ : ∫ z, Ω.indicator V z * lap ψ z = ∫ z in Ω, V z * lap ψ z := by
      rw [← integral_indicator hΩm]
      congr 1; funext z
      by_cases hz : z ∈ Ω <;> simp [hz]
    have hwl : ∫ z, w z * lap ψ z =
        -∑ i : Fin 2, ∫ z, gw i z * dirD ψ (coordDir i) z := by
      have e0 := hwg (dirD ψ 1) (hψ.dirD 1) 0
      have e1 := hwg (dirD ψ Complex.I) (hψ.dirD Complex.I) 1
      rw [coordDir_zero] at e0
      rw [coordDir_one] at e1
      
      
      unfold lap
      simp_rw [mul_add]
      rw [integral_add (integrable_mul_test hw ((hψ.dirD 1).dirD 1)) (integrable_mul_test hw ((hψ.dirD _).dirD _)), Fin.sum_univ_two, coordDir_zero, coordDir_one]
      unfold dirD at e0 e1 ⊢
      rw [e0, e1]
      ring
    rw [hVΩ, hwl, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine integral_eq_setIntegral_of_exterior hγ hΩo ?_
    filter_upwards [hgw0 i] with z hz
    simp [hz]
  have hEu : ∫ z, u z * (E * ψ z) = E * ∫ z in Ω, ψ z * u z := by
    rw [integral_eq_setIntegral_of_exterior hγ hΩo, ← integral_const_mul]
    · congr 1; funext z; ring
    · filter_upwards [hext] with z hz
      simp [hz]
  
  have hiVd : ∀ i : Fin 2, Integrable (fun z => dirD V (coordDir i) z * dirD ψ (coordDir i) z)
      (volume.restrict Ω) := fun i =>
    integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
      (norm_dirD_le_of_lipschitz hV _) (hψ.dirD _)
  have hig : ∀ i : Fin 2, Integrable (fun z => gw i z * dirD ψ (coordDir i) z)
      (volume.restrict Ω) := fun i => integrable_mul_test ((hgw i).restrict Ω) (hψ.dirD _)
  rw [hlap, hEu, integral_add (integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV hψ.lap) (integrable_finset_sum _ fun i _ => hiVd i),
    integral_finset_sum _ fun i _ => hiVd i] at h1
  have hsplit : ∀ i : Fin 2, ∫ z in Ω, dirD ψ (coordDir i) z * (dirD V (coordDir i) z + gw i z) =
      (∫ z in Ω, dirD V (coordDir i) z * dirD ψ (coordDir i) z) +
        ∫ z in Ω, gw i z * dirD ψ (coordDir i) z := by
    intro i
    rw [integral_congr_ae ]
    · exact integral_add (hiVd i) (hig i)
    · exact Eventually.of_forall fun z => by ring
  simp only [hsplit, Finset.sum_add_distrib]
  linear_combination -h1

end Structure

section

variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (hE : 0 < E) (h : compatibleTraces γ E)
include hE hL hb hγ

/-- The restriction of the reconstruction to `Ω` is a Neumann eigenfunction. -/
theorem IsReconSol.restrict_mem {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) {u : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) : restrictL2 Ω u ∈ neumannEigenspace Ω E := by
  
  have hΩm  := hL.1.1.measurableSet
  have hUm : MeasurableSet (closure Ω)ᶜ := isClosed_closure.isOpen_compl.measurableSet
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  obtain ⟨u', hu', V, KV, w, gw, hV, hVc, hVh, hw, hgw, hwg, hue⟩ :=
    exists_reconSol hb hL hγ hE hh
  obtain rfl := hu'.unique hE hu
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  have hext := hu'.ae_eq_zero_exterior hb hL hγ hE
  
  have hgw0 := gw_ae_eq_zero_exterior hwg hgw (by
    filter_upwards [hext, ae_restrict_of_ae hue, ae_restrict_mem hUm] with z h1 h2 h3
    have hzΩ : z ∉ Ω := fun h' => h3 (subset_closure h')
    simpa [h2, hzΩ] using h1)
  have hgm : ∀ i, MemLp (fun z => dirD V (coordDir i) z + gw i z) 2 (volume.restrict Ω) :=
    fun i => (MemLp.of_bound (aestronglyMeasurable_dirD V _) _
      (Eventually.of_forall (norm_dirD_le_of_lipschitz hV _))).add ((hgw i).restrict Ω)
  set g : Fin 2 → L2 Ω := fun i => (hgm i).toLp _ with hgdef
  have hUe : (restrictL2 Ω u') =ᵐ[volume.restrict Ω] fun z => V z + w z := by
    filter_upwards [restrictL2_coeFn Ω u', ae_restrict_of_ae hue, ae_restrict_mem hΩm]
      with z h1 h2 h3
    simp [*]
  refine ⟨g, ?_, ?_⟩
  · -- the weak gradient
    intro φ hφ i
    have hφ' := hφ.univ'
    have hoff : ∀ z, z ∉ Ω → fderiv ℝ φ z (coordDir i) = 0 := fun z hz => by
      have  := fun h' => hz (hφ.2.2 h')
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
    have hoff' : ∀ z, z ∉ Ω → φ z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (hφ.2.2 h'))
    have hiV : Integrable (fun z => V z * fderiv ℝ φ z (coordDir i)) :=
      integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV (hφ'.dirD (coordDir i))
    have hiw : Integrable (fun z => w z * fderiv ℝ φ z (coordDir i)) :=
      integrable_mul_test hw (hφ'.dirD (coordDir i))
    
    
    have e1 : ∫ z in Ω, (restrictL2 Ω u' : ℂ → ℂ) z * fderiv ℝ φ z (coordDir i) =
        ∫ z, (V z * fderiv ℝ φ z (coordDir i) + w z * fderiv ℝ φ z (coordDir i)) := by
      rw [integral_congr_ae ]
      · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [*]
      · filter_upwards [hUe] with z hz
        rw [hz, add_mul]
    have e2 : ∫ z in Ω, (g i) z * φ z =
        ∫ z, (dirD V (coordDir i) z * φ z + gw i z * φ z) := by
      rw [integral_congr_ae ]
      · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [*]
      · filter_upwards [MemLp.coeFn_toLp (hgm i)] with z hz
        rw [hz, add_mul]
    rw [e1, e2, integral_add hiV hiw, integral_add (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _) hφ') (integrable_mul_test (hgw i) hφ'),
      integral_mul_fderiv_of_lipschitz hV (hφ.1.of_le (by exact_mod_cast le_top)) hφ.2.1,
      hwg φ hφ' i, neg_add]
    rfl
  · -- the eigenvalue equation, by density of smooth functions
    intro v hv hvg
    obtain ⟨φ, hφ, hconv, hdconv⟩ := exists_testFunction_approx hb hL hvg
    set Φ : ℕ → L2 Ω := fun n => ((hφ n).memLp' 2).toLp (φ n) with hΦ
    set DΦ : ℕ → Fin 2 → L2 Ω := fun n i => (((hφ n).dirD (coordDir i)).memLp' 2).toLp _
      with hDΦ
    have hkey : ∀ n, ∑ i, inner ℂ (DΦ n i) (g i) = E * inner ℂ (Φ n) (restrictL2 Ω u') := by
      intro n
      
      have k := recon_key_identity hb hL hγ hV hVc hVh hw hgw hwg hu' hue hext hgw0 ((hφ n).conj)
      simp only [L2.inner_def, RCLike.inner_apply']
      convert k using 1
      · refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (((hφ n).dirD (coordDir i)).memLp' 2 ),
          MemLp.coeFn_toLp (hgm i)] with z h1 h2
        rw [h1, h2, dirD_conj ((hφ n).1.of_le (by exact_mod_cast le_top))]
      · congr 1
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp ((hφ n).memLp' 2 ),
          restrictL2_coeFn Ω u'] with z h1 h2
        simp [*]
    have hΦt : Tendsto Φ atTop (𝓝 v) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine hconv.congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp ((hφ n).memLp' 2 )] with z hz
      simp [hΦ, hz]
    have hDΦt : ∀ i, Tendsto (fun n => DΦ n i) atTop (𝓝 (hv i)) := by
      intro i
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine (hdconv i).congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (((hφ n).dirD (coordDir i)).memLp' 2
        )] with z hz
      simp only [Pi.sub_apply, hDΦ, hz]
      rfl
    
    
    exact tendsto_nhds_unique ((tendsto_finset_sum _ fun i _ => (hDΦt i).inner tendsto_const_nhds).congr hkey) ((hΦt.inner tendsto_const_nhds).const_mul _)

/-- If the reconstruction vanishes on `Ω`, the trace vanishes. -/
theorem IsReconSol.trace_eq_zero {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) {u : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) (h0 : restrictL2 Ω u = 0) :
    ∀ θ ∈ angleInterval, h θ = 0 := by
  have hΩo  := hL.1.1
  have hΩm  := hΩo.measurableSet
  have hUm : MeasurableSet (closure Ω)ᶜ := isClosed_closure.isOpen_compl.measurableSet
  obtain ⟨u', hu', V, KV, w, gw, hV, hVc, hVh, hw, hgw, hwg, hue⟩ :=
    exists_reconSol hb hL hγ hE hh
  obtain rfl := hu'.unique hE hu
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  have hext := hu'.ae_eq_zero_exterior hb hL hγ hE
  
  have hgw0 := gw_ae_eq_zero_exterior hwg hgw (by
    filter_upwards [hext, ae_restrict_of_ae hue, ae_restrict_mem hUm] with z h1 h2 h3
    have hzΩ : z ∉ Ω := fun h' => h3 (subset_closure h')
    simpa [h2, hzΩ] using h1)
  -- `u = 0` a.e.
  have hΩ0 : ∀ᵐ z ∂(volume.restrict Ω), u' z = 0 := by
    filter_upwards [restrictL2_coeFn Ω u', (Lp.coeFn_zero ℂ 2 (volume.restrict Ω))] with z h1 h2
    rw [← h1, h0, h2]; rfl
  have hu0 : ∀ᵐ z ∂volume, u' z = 0 := by
    filter_upwards [(ae_restrict_iff' hΩm).mp hΩ0, (ae_restrict_iff' hUm).mp hext,
      ae_mem_or_mem_exterior hγ hΩo] with z h1 h2 h3
    rcases h3 with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hwV : ∀ᵐ z ∂volume, w z = -Ω.indicator V z := by
    filter_upwards [hu0, hue] with z h1 h2
    rw [h2] at h1
    linear_combination h1
  -- `gwᵢ = -∂ᵢV` on `Ω`
  have hgV : ∀ i, ∀ᵐ z ∂(volume.restrict Ω), gw i z + dirD V (coordDir i) z = 0 := by
    intro i
    
    refine ae_eq_zero_of_integral_mul_test hΩo ((MemLp.locallyIntegrable_two (hgw i)).add ((memLp_top_of_bound
      (aestronglyMeasurable_dirD V _) _ (Eventually.of_forall
        (norm_dirD_le_of_lipschitz hV _))).locallyIntegrable le_top)) (fun χ hχ => ?_)
    have hχ' := hχ.univ'
    have e1 := hwg χ hχ' i
    
    have e3 : ∫ z, w z * fderiv ℝ χ z (coordDir i) = -∫ z, V z * fderiv ℝ χ z (coordDir i) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hwV] with z hz
      rw [hz]
      by_cases hzΩ : z ∈ Ω
      · simp [hzΩ]
      · have  := fun h' => hzΩ (hχ.2.2 h')
        simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
    
    
    rw [show (fun z => (gw i z + dirD V (coordDir i) z) * χ z) =
        fun z => gw i z * χ z + dirD V (coordDir i) z * χ z from funext fun z => add_mul _ _ _,
      integral_add (integrable_mul_test (hgw i) hχ') (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _)
        hχ')]
    unfold dirD
    rw [e3, (integral_mul_fderiv_of_lipschitz hV (hχ.1.of_le (by exact_mod_cast le_top))
      hχ.2.1 (coordDir i)), neg_neg] at e1
    linear_combination e1
  -- integration by parts against `1_Ω V`
  have hstar : ∀ φ : ℂ → ℂ, TestFunction univ φ → ∀ i : Fin 2,
      ∫ z in Ω, (V z * fderiv ℝ φ z (coordDir i) + dirD V (coordDir i) z * φ z) = 0 := by
    intro φ hφ i
    have e1 := hwg φ hφ i
    have hiV : Integrable (fun z => V z * fderiv ℝ φ z (coordDir i)) (volume.restrict Ω) :=
      integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV (hφ.dirD (coordDir i))
    
    have e2 : ∫ z, w z * fderiv ℝ φ z (coordDir i) = -∫ z in Ω, V z * fderiv ℝ φ z (coordDir i) := by
      rw [← integral_neg, ← integral_indicator hΩm]
      refine integral_congr_ae ?_
      filter_upwards [hwV] with z hz
      rw [hz]
      by_cases hzΩ : z ∈ Ω <;> simp [hzΩ]
    have e3 : ∫ z, gw i z * φ z = -∫ z in Ω, dirD V (coordDir i) z * φ z := by
      rw [integral_eq_setIntegral_of_exterior hγ hΩo, ← integral_neg]
      · refine integral_congr_ae ?_
        filter_upwards [hgV i] with z hz
        rw [show gw i z = -dirD V (coordDir i) z from eq_neg_of_add_eq_zero_left hz]
        ring
      · filter_upwards [hgw0 i] with z hz
        simp [hz]
    rw [integral_add hiV (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _) hφ)]
    rw [e2, e3] at e1
    linear_combination -e1
  -- `∫_Ω ∂̄(Vφ) = 0`
  have hdbar : ∀ φ : ℂ → ℂ, TestFunction univ φ → ∫ z in Ω, dbar (fun z => V z * φ z) z = 0 := by
    intro φ hφ
    have hiV : ∀ i : Fin 2, Integrable (fun z => V z * fderiv ℝ φ z (coordDir i) +
        dirD V (coordDir i) z * φ z) (volume.restrict Ω) := fun i =>
      (integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV
        (hφ.dirD (coordDir i))).add
      (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _) hφ)
    rw [integral_congr_ae (g := fun z => ((V z * fderiv ℝ φ z (coordDir 0) +
        dirD V (coordDir 0) z * φ z) + Complex.I * (V z * fderiv ℝ φ z (coordDir 1) +
        dirD V (coordDir 1) z * φ z)) / 2)]
    · rw [integral_div, integral_add (hiV 0) ((hiV 1).const_mul _), integral_const_mul,
        hstar φ hφ 0, hstar φ hφ 1]
      simp
    · refine ae_restrict_of_ae ?_
      filter_upwards [hV.ae_differentiableAt] with z hz
      
      unfold dbar dirD
      rw [fderiv_fun_mul hz ((hφ.1.differentiable (by simp)) z)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        coordDir_zero, coordDir_one]
      ring
  -- Green's formula
  
  apply eq_zero_of_integral_comp_mul_deriv hγ (continuousOn_of_mem_compatibleTraces hh)
  intro φ hφ
  obtain ⟨Cφ, hCφ⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  obtain ⟨Kp, hKp⟩ := lipschitzWith_mul_of_bounded hV hKφ hCV hCφ
  have hg := integral_boundary_eq_dbar hb hL hγ hKp (hVc.mul_right)
  rw [hdbar φ hφ, mul_zero] at hg
  rw [← hg]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le (by positivity)] at hθ
  simp [*]

include h in
/-- The reconstruction map `h ↦ u`, as a function on compatible traces. -/
def reconFun : Lp ℂ 2 (volume : Measure ℂ) :=
  Classical.choose (exists_reconSol hb hL hγ hE h.2)

lemma reconFun_spec : IsReconSol γ E h (reconFun hb hL hγ hE h) :=
  (Classical.choose_spec (exists_reconSol hb hL hγ hE h.2)).1

/-- Lemma 4.8 with zero conormal data and the uniqueness of Lemma 4.9: a linear reconstruction
map from compatible traces to Neumann eigenfunctions that only kills traces vanishing on
`[0, 2π]`. -/
theorem neumann_reconstruction_of_compatible :
    ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ angleInterval, (h : ℝ → ℂ) θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  set F := reconFun hb hL hγ hE with hF
  have hspec := reconFun_spec hb hL hγ hE
  have hadd : ∀ h₁ h₂ : compatibleTraces γ E, F (h₁ + h₂) = F h₁ + F h₂ := by
    intro h₁ h₂
    refine (hspec (h₁ + h₂)).unique hE ?_
    intro φ hφ
    
    
    have hi : ∀ u : Lp ℂ 2 (volume : Measure ℂ),
        Integrable (fun z => u z * (lap φ z + E * φ z)) := fun u =>
      integrable_mul_test (Lp.memLp u)
        (⟨hφ.lap.1.add (contDiff_const.mul hφ.1), (hφ.lap.2.1.add
          (hφ.2.1.mul_left)), subset_univ _⟩ : TestFunction univ (fun z => lap φ z + E * φ z))
    rw [integral_congr_ae (g := fun z => F h₁ z * (lap φ z + E * φ z) +
        F h₂ z * (lap φ z + E * φ z)), integral_add (hi _) (hi _), (hspec h₁ φ hφ), (hspec h₂ φ hφ),
      Submodule.coe_add, doubleLayer_add hK (continuousOn_of_mem_compatibleTraces h₁.2)
        (continuousOn_of_mem_compatibleTraces h₂.2) (hφ.1.of_le (by exact_mod_cast le_top))]
    filter_upwards [Lp.coeFn_add (F h₁) (F h₂)] with z hz
    rw [hz, Pi.add_apply, add_mul]
  have hsmul : ∀ (c : ℂ) (h : compatibleTraces γ E), F (c • h) = c • F h := by
    intro c h
    refine (hspec (c • h)).unique hE ?_
    intro φ hφ
    rw [integral_congr_ae ,
      integral_const_mul, hspec h φ hφ, Submodule.coe_smul, doubleLayer_smul]
    filter_upwards [Lp.coeFn_smul c (F h)] with z hz
    rw [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let Flin : compatibleTraces γ E →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨((restrictL2 Ω).comp Flin).codRestrict (neumannEigenspace Ω E)
    (fun h => (hspec h).restrict_mem hb hL hγ hE h.2), fun h h0 => ?_⟩
  
  apply (hspec h).trace_eq_zero hb hL hγ hE h.2
  have := congrArg Subtype.val h0
  exact this

end

end Recon

end PolyaNeumann
