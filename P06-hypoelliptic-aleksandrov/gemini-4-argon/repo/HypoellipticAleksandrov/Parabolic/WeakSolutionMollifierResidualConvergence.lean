module

public import HypoellipticAleksandrov.Parabolic.WeakEquationMollificationResidualDecay
public import HypoellipticAleksandrov.Parabolic.WeakSolutionMollifierConvergence
import HypoellipticAleksandrov.Parabolic.ParabolicConvolutionCommutator
import HypoellipticAleksandrov.Parabolic.WeakEquationMollification
import HypoellipticAleksandrov.Parabolic.Geometry
import HypoellipticAleksandrov.Parabolic.ParabolicMollifierUniformLimit
import HypoellipticAleksandrov.Parabolic.WeakJetExtension
import HypoellipticAleksandrov.Parabolic.WeakRepresentativeLocalization
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Separation.Regular
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
import HypoellipticAleksandrov.Parabolic.Operator
import HypoellipticAleksandrov.Parabolic.ParabolicMollifierLocalization

/-!
# Aligned residual-bearing weak-solution mollifications

This module selects one concrete localized parabolic jet and proves the
simultaneous compact approximation, residual, coefficient, and positivity
properties of that same jet's literal right mollifications.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LocalizedParabolicJet
open ParabolicW12Loc

/- The concrete localized jet selected for a weak solution has an eventual
pointwise mollified residual equation on its compact carrier. -/
theorem eventually_residual_equation_on
    {d : Nat} {A Aext : CoefficientField d}
    {U K : Set (TimeVelocity d)} {u : TimeVelocity d → Real}
    (J : LocalizedParabolicJet d U K u)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue J.g n) z =
        weakEquationMollificationResidual Aext J.g n z := by
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]
  have hWeq :=
    hWeak.equationOn J.W_open J.W_closure_compact J.closure_W_subset_U hp J.w J.w_ae_eq_u
  have hWeq' : J.w.timeDeriv =ᵐ[timeVelocityVolumeOn J.W]
      fun z => matrixContraction (coefficientAt A z) (J.w.velocityHessian z) := by
    filter_upwards [hWeq] with z hz
    exact sub_eq_zero.mp (by simpa only [weakParabolicOperator, Pi.zero_apply] using hz)
  obtain ⟨O, hO, hclosureVO, hOW, _hvalue, htime, _hgrad, hhessian⟩ :=
    J.exists_open_plateau
  have hOU :=
    hOW.trans (subset_closure.trans J.closure_W_subset_U)
  have hWeqO :=
    hWeq'.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW
  have hExtAEO :=
    hExtAE.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOU
  have hEqO : J.g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt Aext z) (J.g.velocityHessian z) := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    filter_upwards [((ae_restrict_iff' hO.measurableSet).mp hWeqO), ((ae_restrict_iff' hO.measurableSet).mp hExtAEO)] with z hweq hAext hzO
    calc
      J.g.timeDeriv z = J.w.timeDeriv z := htime hzO
      _ = matrixContraction (coefficientAt A z) (J.w.velocityHessian z) := hweq hzO
      _ = matrixContraction (coefficientAt Aext z) (J.g.velocityHessian z) := by
        rw [hAext hzO, hhessian hzO]
  filter_upwards [(eventually_residual_equation_of_ae_on J.V_closure_compact hO hclosureVO J.g hp hEqO)] with n hn
  intro z hz
  exact hn z (subset_closure (J.K_subset_V hz))

end LocalizedParabolicJet

/- A nonnegative local weak solution admits one selected localized jet whose
literal mollifications converge uniformly to the supplied representative,
have decaying residuals, and eventually satisfy all stated smooth classical
approximation properties on the same compact carrier. -/
theorem exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto
    (d : Nat) (hd : 1 ≤ d) (lam Lam : Real)
    (A Aext : CoefficientField d)
    (U K : Set (TimeVelocity d))
    (u q : TimeVelocity d → Real)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u)
    (huNonneg : ∀ᵐ z ∂timeVelocityVolumeOn U, 0 ≤ u z)
    (hq : ContinuousOn q U)
    (hqu : q =ᵐ[timeVelocityVolumeOn U] u) :
    ∃ J : LocalizedParabolicJet d U K u,
      TendstoUniformlyOn
        (fun n z => parabolicMollifiedValue J.g n z) q atTop K ∧
      Tendsto (fun n => eLpNorm
        (weakEquationMollificationResidual Aext J.g n)
        (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) ∧
      ∀ᶠ n in atTop,
        IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
        IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
        HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
        HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) ∧
        ContDiff Real (↑(⊤ : ℕ∞)) (parabolicMollifiedValue J.g n) ∧
        (∀ z ∈ K, 0 ≤ parabolicMollifiedValue J.g n z) ∧
        (∀ z ∈ K,
          parabolicOperator (parabolicMollifyCoefficient Aext n)
              (parabolicMollifiedValue J.g n) z =
            weakEquationMollificationResidual Aext J.g n z) := by
  obtain ⟨J, hUniform⟩ : ∃ J : LocalizedParabolicJet d U K u,
      TendstoUniformlyOn
        (fun n z =>
          parabolicConvolution J.g.toFun (parabolicMollifier d n) z)
        q atTop K := by
    have hu := hWeak.parabolicW12Loc
    obtain ⟨V, hVOpen, hKV, hclosureVU, hVCompact⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨W, hWOpen, hWCompact, hclosureVW, hclosureWU⟩ : ∃ W : Set (TimeVelocity d),
        IsOpen W ∧ IsCompact (closure W) ∧
        closure V ⊆ W ∧ closure W ⊆ U := by
      obtain ⟨L, hLcompact, hLclosed, hVinterior, hLU⟩ :=
        exists_compact_closed_between hVCompact hU hclosureVU
      have hVsubset := subset_closure.trans hVinterior
      have hW : interior L ∪ V = interior L := union_eq_left.mpr hVsubset
      have hclosure :=
        closure_minimal interior_subset hLclosed
      have hWcompact : IsCompact (closure (interior L ∪ V)) := by
        rw [hW]
        exact IsCompact.of_isClosed_subset hLcompact isClosed_closure hclosure
      have hVclosureW : closure V ⊆ interior L ∪ V := by
        rw [hW]
        exact hVinterior
      have hWclosureU : closure (interior L ∪ V) ⊆ U := by
        rw [hW]
        exact hclosure.trans hLU
      exact ⟨interior L ∪ V, isOpen_interior.union hVOpen, hWcompact,
        hVclosureW, hWclosureU⟩
    obtain ⟨w, hwu⟩ :=
      hu.exists_parabolicW12Function hWOpen hWCompact hclosureWU
    have hp : (1 : ENNReal) ≤ parabolicExponent d := by
      simp [parabolicExponent]
    obtain ⟨b, hbSmooth, hbCompact, hbOne, hbW, htoFun, htime, hgrad, hhessian⟩ :=
      exists_smooth_compact_cutoff_mul_eventuallyEq_jet hVCompact hWOpen hWCompact
        hclosureVW w hp
    let J : LocalizedParabolicJet d U K u :=
      { V := V
        W := W
        w := w
        b := b
        g := w.mulContDiffHasCompactSupport_univ
          (by simp [parabolicExponent]) hbSmooth hbCompact hWOpen hbW
        V_open := hVOpen
        V_closure_compact := hVCompact
        K_subset_V := hKV
        W_open := hWOpen
        W_closure_compact := hWCompact
        closure_V_subset_W := hclosureVW
        closure_W_subset_U := hclosureWU
        w_ae_eq_u := hwu
        b_smooth := hbSmooth
        b_compact := hbCompact
        b_tsupport_subset_W := hbW
        b_one_near_closure_V := hbOne
        g_is_cutoff := by rfl
        g_toFun_eq_near_closure_V := by
          simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! htoFun
        g_timeDeriv_eq_near_closure_V := by
          simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! htime
        g_velocityGrad_eq_near_closure_V := by
          simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! hgrad
        g_velocityHessian_eq_near_closure_V := by
          simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ] using! hhessian }
    have hJCompact : HasCompactSupport J.g.toFun := by
      change IsCompact (tsupport J.g.toFun)
      refine IsCompact.of_isClosed_subset J.b_compact (isClosed_tsupport (f := J.g.toFun)) ?_
      rw [J.g_is_cutoff]
      simpa only [ParabolicW12Function.mulContDiffHasCompactSupport_univ_toFun] using
        (tsupport_mul_subset_left (f := J.b) (g := J.w.toFun))
    obtain ⟨r, hrContinuous, hrUniform, hrg⟩ :=
      J.g.exists_continuousOn_tendstoUniformlyOn_ae_eq_toFun_parabolicConvolution
        hd hJCompact (closure J.V) J.V_closure_compact
    obtain ⟨O, hOOpen, hclosureVO, hOW, hgwo, -, -, -⟩ := J.exists_open_plateau
    have hrgV :=
      hrg.filter_mono <| ae_mono <|
        Measure.restrict_mono_set volume subset_closure
    have hgwV : J.g.toFun =ᵐ[timeVelocityVolumeOn J.V] J.w.toFun := by
      filter_upwards [ae_restrict_mem J.V_open.measurableSet] with z hzV
      exact hgwo (hclosureVO (subset_closure hzV))
    have hVW := subset_closure.trans J.closure_V_subset_W
    have hwuV :=
      J.w_ae_eq_u.filter_mono <| ae_mono <|
        Measure.restrict_mono_set volume hVW
    have hVU :=
      subset_closure.trans (J.closure_V_subset_W.trans
        (subset_closure.trans J.closure_W_subset_U))
    have hquV :=
      hqu.filter_mono <| ae_mono <|
        Measure.restrict_mono_set volume hVU
    have hrquV : r =ᵐ[timeVelocityVolumeOn J.V] q :=
      (hrgV.trans hgwV).trans (hwuV.trans hquV.symm)
    have hrq :=
      Measure.eqOn_open_of_ae_eq hrquV J.V_open
        (hrContinuous.mono subset_closure) (hq.mono hVU)
    refine ⟨J, ?_⟩
    exact (hrUniform.mono (J.K_subset_V.trans subset_closure)).congr_right
      fun z hzK => hrq (J.K_subset_V hzK)
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]
  have hResidual : Tendsto (fun n => eLpNorm
      (weakEquationMollificationResidual Aext J.g n)
      (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) := by
    let g := J.g
    simpa only [weakEquationMollificationResidual_eq_parabolicConvolutionCommutator] using
      tendsto_eLpNorm_parabolicConvolutionCommutator_on_compact
        Aext g.velocityHessian K hK (3 * (|lam| + |Lam|))
        (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        (fun i j =>
          (measurable_pi_iff.mp (measurable_pi_iff.mp hExtBorel i) j).aestronglyMeasurable)
        (fun i j =>
          locallyIntegrable_coefficientAt_entry_of_ellipticity
            hExtBorel hExtLower hExtUpper i j)
        (fun i j z =>
          coefficient_entry_abs_le_of_ellipticity
            (hExtLower z.1 z.2) (hExtUpper z.1 z.2) i j)
        (fun i j => by
          have h := g.velocityHessian_memLp i j
          change MemLp (fun z => g.velocityHessian z i j) (parabolicExponent d)
            ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
          simpa only [Measure.restrict_univ] using h)
  have hSymm : IsSymmetricCoefficient Aext :=
    isSymmetricCoefficient_of_hasLowerEllipticity hExtLower
  have hCoefficient : ∀ᶠ n in atTop,
      IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
      IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
      HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
      HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) :=
    Filter.Eventually.of_forall fun n =>
      ⟨isSmoothCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtLower
          hExtUpper n,
        isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam Aext hSymm n,
        hasLowerEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n,
        hasUpperEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n⟩
  obtain ⟨O, hO, hclosureVO, hOW, hvalue, _htime, _hgrad, _hhessian⟩ :=
    J.exists_open_plateau
  have hKO :=
    J.K_subset_V.trans (subset_closure.trans hclosureVO)
  have hOU :=
    hOW.trans (subset_closure.trans J.closure_W_subset_U)
  have hValueO : J.g.toFun =ᵐ[timeVelocityVolumeOn O] J.w.toFun := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hzO
    exact hvalue hzO
  have hWValueO :=
    J.w_ae_eq_u.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW
  have huNonnegO :=
    huNonneg.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOU
  have hNonnegO : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ J.g.toFun z := by
    filter_upwards [hValueO.trans hWValueO, huNonnegO] with z hgu hnonneg
    rw [hgu]
    exact hnonneg
  have hNonnegative :=
    eventually_nonnegative_parabolicMollifiedValue_of_ae_nonnegative_on hK hO hKO J.g hNonnegO
  have hEquation := J.eventually_residual_equation_on hExtAE hWeak
  refine ⟨J, ?_, hResidual, ?_⟩
  · simpa only [parabolicMollifiedValue] using hUniform
  · filter_upwards [hCoefficient, hNonnegative, hEquation] with n hcoefficient hnonnegative
      hequation
    have _h_xinl_0 : ContDiff Real (↑(⊤ : ℕ∞)) (parabolicMollifiedValue J.g n) := by
      let g := J.g
      simpa only [parabolicMollifiedValue] using
        g.contDiff_convolution hp (parabolicMollifier d n)
          (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
    exact ⟨hcoefficient.1, hcoefficient.2.1, hcoefficient.2.2.1, hcoefficient.2.2.2,
      _h_xinl_0, hnonnegative, hequation⟩

end HypoellipticAleksandrov.Parabolic
