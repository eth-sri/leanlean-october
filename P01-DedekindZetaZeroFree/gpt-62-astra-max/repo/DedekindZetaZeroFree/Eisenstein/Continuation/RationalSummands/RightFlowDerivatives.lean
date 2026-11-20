module

public import DedekindZetaZeroFree.Eisenstein.Sections.FlatRightWordJets
public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords
public import DedekindZetaZeroFree.Eisenstein.Induction.SphericalFlatSection
public import DedekindZetaZeroFree.Eisenstein.Continuation.RationalSummands.MixedJets

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

open KPContActualChamberNormalSeries

section ParameterSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
  {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
  (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
  (f : ℂ → S)

theorem actual_parameterTerm_formula
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g =
      ∑ i : Fin (Module.finrank ℂ S), ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℂ) *
        iteratedDerivWithin j (fun z => (Module.finBasis ℂ S).repr (f z) i) V s *
        KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
          (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι)
          (k - j) s ((Module.finBasis ℂ S) i) (lift F ζ hζ q * g) := by
  let B := Module.finBasis ℂ S
  let α := fun g : G F ζ hζ => (KPContFlatSourceRecipe.alpha F ζ hζ (lift F ζ hζ q * g) : ℂ)
  let c := fun i : Fin (Module.finrank ℂ S) => fun z : ℂ => B.repr (f z) i
  let v := fun i : Fin (Module.finrank ℂ S) => fun g : G F ζ hζ =>
    KPContActualSphericalFlatStage.L F ζ hζ U ι 0 (B i) (lift F ζ hζ q * g)
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz; change -(1 : ℝ)/6 < z.re; change (1 : ℝ)/3 < z.re at hz; linarith
  have hc : ∀ i, ContDiffOn ℂ (⊤ : WithTop ℕ∞) (c i) V := by
    intro i
    exact ((⟨B.coord i, (B.coord i).continuous_of_finiteDimensional⟩ : S →L[ℂ] ℂ).differentiable.comp_differentiableOn
      (hf.mono hVΩ)).contDiffOn KPChamberL2Defect.chamber_isOpen
  have heq : (fun z => term F ζ hζ U ι f q z g) =
      fun z => ∑ i, (c i z * Complex.exp (α g * z)) * v i g := by
    funext z
    unfold term
    conv_lhs => rw [← B.sum_repr (f z)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, v, α, KPContFlatCommonLevelKernel.L_formula, zero_mul, Complex.exp_zero, one_mul]
    rw [mul_comm z]
    ring
  change iteratedDerivWithin k (fun z => term F ζ hζ U ι f q z g) V s = _
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ S))),
      ContDiffWithinAt ℂ (k : WithTop ℕ∞) (fun z => (c i z * Complex.exp (α g*z)) * v i g) V s := by
    intro i _
    exact ((hc i s hs).of_le (by simp)).mul (by fun_prop) |>.mul contDiffWithinAt_const
  rw [heq, iteratedDerivWithin_fun_sum hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDerivWithin_mul_const_field]
  change iteratedDerivWithin k (c i * (fun z => Complex.exp (α g*z))) V s * _ = _
  rw [iteratedDerivWithin_mul hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    ((hc i s hs).of_le (by simp)) (by fun_prop), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen hs,
    iteratedDeriv_cexp_const_mul]
  change _ = (k.choose j : ℂ) * iteratedDeriv j (c i) s *
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) (k-j) s (B i) _
  simp only [KPContFlatStageJetHolomorphy.parameterSection,
    KPContFlatStageJetHolomorphy.L, KPContFlatCommonLevelKernel.L_formula, v,
    zero_mul, Complex.exp_zero, one_mul]
  change _ = _ * (α g ^ (k-j) * (Complex.exp (s * α g) * _))
  rw [mul_comm s]
  change _ = _ * (α g ^ (k-j) * (Complex.exp (α g * s) *
    (ι (B i)).val.val.val (lift F ζ hζ q * g)))
  ring

theorem actual_parameterSection_right_chart_smooth
    (m : ℕ) (s : ℂ) (v : S) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
        (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hleft := KPContFlatStageJetHolomorphy.parameterSection_contDiffOn F ζ hζ
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι)
    (KPContActualSphericalFlatStage.stage_smooth F ζ hζ U ι)
    (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀) m s v
  apply ((hleft.comp hq hqO).congr (fun x hx => congrArg
    (KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v)
    (heq x hx))).mono
  exact Set.inter_subset_right

theorem actual_parameterTerm_right_chart_smooth
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  simp_rw [actual_parameterTerm_formula F ζ hζ U ι f hf q k s hs]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  apply contDiffOn_const.mul
  simpa only [mul_assoc] using
    actual_parameterSection_right_chart_smooth F ζ hζ U ι (k-j) s
      ((Module.finBasis ℂ S) i) (lift F ζ hζ q * g)

theorem actual_parameterSection_level (m : ℕ) (s : ℂ) (v : S)
    (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v (g*u.val) =
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v g := by
  have hc := (ι v).property.1 g u
  change (KPContFlatSourceRecipe.alpha F ζ hζ (g*u.val) : ℂ)^m *
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v (g*u.val) =
    (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)^m *
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v g
  rw [KPContFlatCommonLevelKernel.L_formula, KPContFlatCommonLevelKernel.L_formula, hc.1]
  rcases mul_eq_zero.mp hc.2 with ha | hz
  · rw [(sub_eq_zero.mp (Complex.ofReal_eq_zero.mp ha))]
  · rw [hz]
    simp

theorem actual_parameterTerm_level
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s (g*u.val) =
      mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g := by
  simp_rw [actual_parameterTerm_formula F ζ hζ U ι f hf q k s hs, ← mul_assoc,
    actual_parameterSection_level F ζ hζ U ι]

end ParameterSource

namespace PositiveChart
open Filter
open KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 section

variable (b : KPSmoothActualFlowData.B F)

def flowMatrix (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
 def theta (t : ℝ) : ArchCoordinates F :=
  fun v => KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates (flowMatrix F b t v).val
private theorem flowMatrix_zero (v : NumberField.InfinitePlace F) :
    flowMatrix F b 0 v = 1 := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.flowMatrix_zero <;> assumption
private theorem theta_zero : theta F b 0 = archBase F := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_zero <;> assumption
private theorem flowEntry_smooth
    (v : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.flowEntry_smooth <;> assumption

private theorem theta_smooth :
    ContDiffAt ℝ (⊤ : ℕ∞) (theta F b) 0 := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_smooth <;> assumption
private theorem theta_chart :
    ∀ᶠ t in nhds (0 : ℝ), KPGlobalResidualConstruction.archChart F ζ hζ (theta F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_chart <;> assumption

end
 def chartProduct (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
private theorem chartProduct_base_right (x : ArchCoordinates F) :
    chartProduct F (x,archBase F) = x := by
  funext q i
  fin_cases i <;> simp [chartProduct, archBase]
 section

variable (b : KPSmoothActualFlowData.B F)

def transport (p : ArchCoordinates F × ℝ) : ArchCoordinates F :=
  chartProduct F (p.1, theta F b p.2)
 def field (x : ArchCoordinates F) : ArchCoordinates F :=
  fderiv ℝ (transport F b) (x,0) (0,1)
private theorem transport_zero (x : ArchCoordinates F) :
    transport F b (x,0) = x := by
  simp [transport, theta_zero, chartProduct_base_right]

end
section

variable (b : KPSmoothActualFlowData.B F) (V : Set (ArchCoordinates F)) (hVo : IsOpen V)
    (hb : archBase F ∈ V) (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))

include hVo hb hμ in
private theorem transport_smooth (x : ArchCoordinates F) (hx : x ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (transport F b) (x,0) := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.transport_smooth <;> assumption
include hVo hb hμ in
private theorem field_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (field F b) V := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.field_smooth <;> assumption
include hVo hb hμ in
private theorem transport_hasDeriv (x : ArchCoordinates F) (hx : x ∈ V) :
    HasDerivAt (fun t => transport F b (x,t)) (field F b x) 0 := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.transport_hasDeriv <;> assumption

end

 def coordWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (fields : ι → E → E) : List ι → (E → ℂ) → E → ℂ
  | [], u => u
  | b :: w, u => fun x => fderiv ℝ (coordWord fields w u) x (fields b x)
private theorem coordWord_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (fields : ι → E → E) (U : Set E)
    (hU : IsOpen U) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (w : List ι) (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)

section

variable (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)

private theorem scalar_word_in_chart
    (huAll : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hVD : V ⊆ archDomain F)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    ∀ x ∈ V,
      w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
        (u) (g * archChart F ζ hζ x) =
      coordWord (field F) w (fun y => u (g * archChart F ζ hζ y)) x := by
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    let u₀ := fun y => u (g * archChart F ζ hζ y)
    let q := coordWord (field F) w u₀
    have htr := transport_hasDeriv F b V hVo hb hμ x hx
    have htr0 := transport_zero F b x
    have hder : HasDerivAt (fun t => q (transport F b (x,t)))
        (fderiv ℝ q x (field F b x)) 0 := by
      simpa using! ((show HasFDerivAt q (fderiv ℝ q x) (transport F b (x,0)) from htr0.symm ▸ ((((coordWord_smooth (field F) V hVo (fun b => field_smooth F b V hVo hb hμ) w u₀ ((huAll g).mono hVD)).contDiffAt (hVo.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt)).comp_hasDerivAt 0 htr)
    have he : (fun t : ℝ =>
        w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
          (u) ((g * archChart F ζ hζ x) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        =ᶠ[nhds 0] (fun t => q (transport F b (x,t))) := by
      have htV : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ V :=
        (theta_smooth F b).continuousAt.eventually (by simpa [theta_zero] using hVo.mem_nhds hb)
      have hpV : ∀ᶠ t in nhds (0 : ℝ), transport F b (x,t) ∈ V :=
        htr.continuousAt.eventually (by simpa only [htr0] using (show ∀ᶠ y in nhds x, y ∈ V from hVo.mem_nhds hx))
      filter_upwards [theta_chart F ζ hζ b, htV, hpV] with t ht htV hpV
      rw [← ht, mul_assoc, ← hprod x hx (theta F b t) htV]
      exact ih (transport F b (x,t)) hpV
    change deriv _ 0 = fderiv ℝ q x (field F b x)
    rw [he.deriv_eq]
    exact hder.deriv

theorem rightWord_hasDerivAt_of_chart_smooth
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : Word F) (b : KPSmoothActualFlowData.B F) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    HasDerivAt (fun t : ℝ => rightWord F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (rightWord F ζ hζ (b :: w) u g) 0 := by
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  let q := coordWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hθ := theta_smooth F b
  have hθO : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ O :=
    hθ.continuousAt.eventually (by simpa [theta_zero] using hOo.mem_nhds hb)
  have he : (fun t : ℝ => rightWord F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t))) =ᶠ[nhds 0]
      (fun t => q (theta F b t)) := by
    filter_upwards [theta_chart F ζ hζ b, hθO] with t ht htO
    rw [← ht]
    exact scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g _ htO
  have hd := ((((coordWord_smooth (field F) O hOo (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)).contDiffAt (by simpa [theta_zero] using hOo.mem_nhds hb)).comp 0 hθ).differentiableAt (by simp))
  exact (hd.congr_of_eventuallyEq he).hasDerivAt

theorem rightWord_level
    (a : KPContActualChamberNormalSeries.G F ζ hζ)
    (ha : ∀ x, Commute (archChart F ζ hζ x) a)
    (hu : ∀ g, u (g*a) = u g) (w : Word F)
    (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    rightWord F ζ hζ w u (g*a) = rightWord F ζ hζ w u g := by
  induction w generalizing g with
  | nil => exact hu g
  | cons b w ih =>
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [theta_chart F ζ hζ b] with t ht
    rw [← ht, mul_assoc, (ha (theta F b t)).eq.symm, ← mul_assoc]
    exact ih _

end

theorem rightWord_continuous_of_chart_smooth
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hlevel : ∀ g, ∀ a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      u (g*a.val) = u g) (w : Word F) :
    Continuous (rightWord F ζ hζ w u) := by
  letI : IsTopologicalGroup (KPContActualChamberNormalSeries.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  apply continuous_iff_continuousAt.mpr
  intro g
  let q := coordWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O :=
    coordWord_smooth (field F) O hOo (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)
  have hbase : q (archBase F) = rightWord F ζ hζ w u g := by
    have hh := scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g _ hb
    simpa only [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one, rightWord, q] using hh.symm
  apply tendsto_def.mpr
  intro N hN
  have hn : q ⁻¹' N ∈ nhds (archBase F) :=
    (hq.continuousOn.continuousAt (hOo.mem_nhds hb)).preimage_mem_nhds (hbase.symm ▸ hN)
  obtain ⟨W, hWN, hWo, hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hOo.mem_nhds hb))
  have hWO : W ⊆ O := fun x hx => (hWN hx).2
  have hT := hthick W hWo hbW hWO U
  change ∀ᶠ y in nhds (1 : KPContActualChamberNormalSeries.G F ζ hζ),
    ∃ x ∈ W, ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      y = archChart F ζ hζ x * a at hT
  have hg : ∀ᶠ y in nhds g, ∃ x ∈ W,
      ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹*y = archChart F ζ hζ x * a :=
    (show ContinuousAt (fun y : KPContActualChamberNormalSeries.G F ζ hζ => g⁻¹*y) g from
      continuousAt_const.mul continuousAt_id).eventually (by simpa using hT)
  filter_upwards [hg] with y hy
  obtain ⟨x, hx, a, ha, he⟩ := hy
  have hy' : y = (g * archChart F ζ hζ x)*a := by
    calc y = g*(g⁻¹*y) := by simp
         _ = _ := by rw [he, mul_assoc]
  change rightWord F ζ hζ w u y ∈ N
  rw [hy', rightWord_level F ζ hζ u a (fun x => hcomm U a ha x)
    (fun g => hlevel g ⟨a,ha⟩) w]
  change w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v) u
    (g * archChart F ζ hζ x) ∈ N
  rw [scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g x (hWO hx)]
  exact (hWN hx).1

theorem rightWord_chart_realization :
    ∃ (O : Set (ArchCoordinates F)) (fields : KPSmoothActualFlowData.B F → ArchCoordinates F → ArchCoordinates F),
      IsOpen O ∧ archBase F ∈ O ∧ O ⊆ archDomain F ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O) ∧
      ∀ (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ),
        (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) →
        ∀ (w : Word F) (g : KPContActualChamberNormalSeries.G F ζ hζ) (x : ArchCoordinates F),
          x ∈ O → rightWord F ζ hζ w u (g * archChart F ζ hζ x) =
            RightFrame.PullbackWords.directionalWord fields w
              (fun y => u (g * archChart F ζ hζ y)) x := by
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  refine ⟨O, field F, hOo, hb, hOD, fun b => field_smooth F b O hOo hb hμ, ?_⟩
  intro u hu w g x hx
  have he : coordWord (field F) w = RightFrame.PullbackWords.directionalWord (field F) w := by
    induction w with
    | nil => rfl
    | cons b w ih => simp only [coordWord, RightFrame.PullbackWords.directionalWord, ih]
  rw [← he]
  exact scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g x hx

end PositiveChart

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℂ S] [FiniteDimensional ℂ S] (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S)

theorem actual_parameterTerm_word_flow (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V)
    (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) :
    HasDerivAt (fun t : ℝ => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := PositiveChart.rightWord_hasDerivAt_of_chart_smooth F ζ hζ
    (mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s)
    (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q k s hs) w b g

theorem actual_term_mixed_flow (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) :
    Continuous (mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s) ∧
    ∀ (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ),
      HasDerivAt
        (fun t : ℝ => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
          (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := by
  constructor
  · exact PositiveChart.rightWord_continuous_of_chart_smooth F ζ hζ U
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s)
      (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q k s hs)
      (actual_parameterTerm_level F ζ hζ U ι f hf q k s hs) w
  · exact actual_parameterTerm_word_flow F ζ hζ U ι f hf q k w s hs

end DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

end
