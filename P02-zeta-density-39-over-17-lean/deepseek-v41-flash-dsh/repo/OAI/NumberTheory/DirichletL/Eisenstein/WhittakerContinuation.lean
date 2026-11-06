module
public import OAI.NumberTheory.DirichletL.Eisenstein.ScatteringCoefficients

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

section
open Filter MeasureTheory Finset AddChar MulChar EisensteinEmbedding
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma cuspWhittakerHeightFactor_analyticAt (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWhittakerHeightFactor w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWhittakerAverage_differentiableAt (cuspFrequency h) w hw

lemma kernelCuspFourierFamily_analyticAt_nonreal (h : ActualEisensteinCubic.O) (a b : ℝ)
    (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspFourierFamily h a b ha hab) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspFourier h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact a b ha hab s hs hi) rfl

def continuedNonzeroScattering (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)

def nonzeroScatteringResidue (h : ActualEisensteinCubic.O) : ℂ :=
  kernelCuspFourier h cubicEisensteinResidue /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)

lemma kernelCuspFourierFamily_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h)
      {s : ℂ | 2<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 2<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (2:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)) domain := by
    intro s hs
    exact kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hright : AnalyticOnNhd ℂ
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (analyticAt_const.mul (scatteringCoefficient_analyticOnNhd h s hs.1)).mul
      (cuspWhittakerHeightFactor_analyticAt h s (by linarith [hs.1]))
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
      (by norm_num) (by norm_num) s (by linarith [hs.1])
      (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

theorem kernelCompact_projection_measure_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃N : ℕ,Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (N:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  choose e he heq using kernelQuotient_localHomeomorph
  have hcover : K⊆⋃w : HyperbolicSpace,(e w).source := by
    intro w _
    exact Set.mem_iUnion.mpr ⟨w,he w⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun w => (e w).source) (fun w => (e w).open_source) hcover
  have hinj (w : HyperbolicSpace) :
      Set.InjOn (integralOrbitProjection globalKubotaKernel) (e w).source := by
    rw [heq w]
    exact (e w).injOn
  refine ⟨t.card,Measure.le_iff.mpr ?_⟩
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.smul_apply]
  change hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ K)≤
    (t.card:ℝ≥0∞)*integralQuotientVolume globalKubotaKernel B
  calc
    _ ≤ hyperbolicVolume (⋃w∈t,(integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) := by
      apply measure_mono
      rintro w ⟨hw,hK⟩
      obtain ⟨v,hv,hwv⟩ := Set.mem_iUnion₂.mp (ht hK)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,hw,hwv⟩
    _ ≤ ∑w∈t,hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑_w∈t,integralQuotientVolume globalKubotaKernel B := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := kernelProjection_measurePreserving_on (e w).source (e w).open_source.measurableSet (hinj w)
      rw [←Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),
        ←Measure.map_apply (measurable_integralOrbitProjection _) hB,hm.map_eq]
      exact Measure.restrict_le_self B
    _ = _ := by simp [nsmul_eq_mul]

section DominatedComplexL2
variable {α : Type*} [MeasurableSpace α] {«μ» ν : Measure α} {c : ℝ≥0∞}

def dominatedComplexL2 (hc : c≠⊤) (h : ν≤c•«μ») : Lp ℂ 2 «μ»→L[ℂ]Lp ℂ 2 ν where
  toFun := Lp.LpToLpOfMeasureLeSMul hc h
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hc h)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z•f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul hc h f),
      (Measure.absolutelyContinuous_of_le_smul h).ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,Pi.smul_apply] at *
    rw [h1,h3,h2,h4]
  cont := (Lp.LpToLpOfMeasureLeSMul hc h).continuous

lemma dominatedComplexL2_ae (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    dominatedComplexL2 hc h f=ᵐ[ν]f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f

lemma dominatedComplexL2_norm_le (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    ‖dominatedComplexL2 hc h f‖≤c.toReal^((1:ℝ)/2)*‖f‖ := by
  have hb := (Lp.LpToLpOfMeasureLeSMul hc h : Lp ℂ 2 «μ»→L[ℝ]Lp ℂ 2 ν).le_opNorm f
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc h
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hn

end DominatedComplexL2

def kernelCompactMultiplicity (K : Set HyperbolicSpace) (hK : IsCompact K) : ℕ :=
  (kernelCompact_projection_measure_bound K hK).choose

lemma kernelCompactMultiplicity_spec (K : Set HyperbolicSpace) (hK : IsCompact K) :
    Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (kernelCompactMultiplicity K hK:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel :=
  (kernelCompact_projection_measure_bound K hK).choose_spec

def kernelCompactPullbackCLM (K : Set HyperbolicSpace) (hK : IsCompact K) :
    KernelQuotientL2→L[ℂ]Lp ℂ 2 (hyperbolicVolume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _,rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤)
        (kernelCompactMultiplicity_spec K hK))

theorem kernelCompactPullbackCLM_ae (K : Set HyperbolicSpace) (hK : IsCompact K)
    (F : KernelQuotientL2) :
    kernelCompactPullbackCLM K hK F=ᵐ[hyperbolicVolume.restrict K]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict K)
      (Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)) :=
    ⟨measurable_integralOrbitProjection _,rfl⟩
  have he := dominatedComplexL2_ae
    (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤) (kernelCompactMultiplicity_spec K hK) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)

lemma whittaker_bound_integrable_finite («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) («μ».prod volume) := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) «μ» := integrable_const _
  simpa only [one_mul] using hv.mul_prod hk

lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))

lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]

lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm

end

open Filter MeasureTheory Finset AddChar MulChar EisensteinEmbedding
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

local notation "O" => ActualEisensteinCubic.O

def cuspWeightedFourierPhase (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*cuspFourierPhase h w

lemma cuspWeightedFourierPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Continuous (cuspWeightedFourierPhase ρ h) :=
  (ρ.continuous.comp hyperbolicHeight_continuous).mul (cuspFourierPhase_continuous h)

lemma cuspWeightedFourierPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) :
    ‖cuspWeightedFourierPhase ρ h w‖≤‖ρ‖ := by
  rw [cuspWeightedFourierPhase,norm_mul,cuspFourierPhase_norm,mul_one]
  exact ρ.norm_coe_le_norm _

end CubicEisenstein

end

end OAI
