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
  have hc := hleft.comp hq hqO
  apply (hc.congr (fun x hx => congrArg
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
  · have he : KPContFlatSourceRecipe.alpha F ζ hζ (g*u.val) =
        KPContFlatSourceRecipe.alpha F ζ hζ g := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp ha)
    rw [he]
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
open KPGlobalResidualConstruction KPGlobalResidualConstruction.RightFlowChart
open KPContinuation.ChamberFlatSource (word_eq_green)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem rightWord_eq (w : Word F) (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ) :
    rightWord F ζ hζ w u = word F ζ hζ w u :=
  (word_eq_green F ζ hζ w u).symm

theorem rightWord_hasDerivAt_of_chart_smooth
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : Word F) (b : KPSmoothActualFlowData.B F) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    HasDerivAt (fun t : ℝ => rightWord F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (rightWord F ζ hζ (b :: w) u g) 0 := by
  simpa only [rightWord_eq] using RightFlowChart.rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu w b g

theorem rightWord_continuous_of_chart_smooth
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hlevel : ∀ g, ∀ a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      u (g*a.val) = u g) (w : Word F) :
    Continuous (rightWord F ζ hζ w u) := by
  simpa only [rightWord_eq] using RightFlowChart.rightWord_continuous_of_chart_smooth F ζ hζ U u hu hlevel w

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
  obtain ⟨O, hOo, hb, hOD, hμ, _, hprod, _, _⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  refine ⟨O, field F, hOo, hb, hOD, fun b => field_smooth F b O hOo hb hμ, ?_⟩
  intro u hu w g x hx
  rw [rightWord_eq]
  exact word_in_chart F ζ hζ u O hOo hb hμ hprod w g ((hu g).mono hOD) x hx

end PositiveChart

theorem actual_parameterTerm_word_flow
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V)
    (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) :
    HasDerivAt (fun t : ℝ => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := by
  exact PositiveChart.rightWord_hasDerivAt_of_chart_smooth F ζ hζ
    (mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s)
    (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q k s hs) w b g

theorem actual_term_mixed_flow
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
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
