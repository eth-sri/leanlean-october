module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowCanonical
public import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow IdealMobiusDivisorSum

variable {ι:Type*}[Fintype ι]


def commonEnergy (s:OriginalData ι)(C)(hC:Supported C)(τ:Character)
    (t:ℝ)(L:Ideal ActualEisensteinCubic.O)(U:𝓢(ℝ,ℂ))(K:ℝ):=
  let Q:=residualPool C hC.1 s.columns
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal ActualEisensteinCubic.O) ∧ L∣(I:Ideal ActualEisensteinCubic.O)
      then s.beta (C*I) else 0)*heightCoeff τ t I) U K

section
variable (s:OriginalData ι) (Q C:Ideal ActualEisensteinCubic.O) (hQ:Q≠0) (hC:Supported C) (hQC:primeSupport Q=primeSupport C) (τ:Character)
include s Q C hQ hC hQC τ

section
variable (t:ℝ) (L:Ideal ActualEisensteinCubic.O)
include t L

lemma column_unwindowed_common     
         z :
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (C*I) else 0)*heightCoeff τ t I) z=
      commonGauss s C hC τ t L z:=by
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I) z]
  unfold commonGauss
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal ActualEisensteinCubic.O) <;> by_cases hl:L∣(I:Ideal ActualEisensteinCubic.O) <;> simp [hc,hl]

theorem column_unwindowed_energy     
         U  K :
    gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (C*I) else 0)*heightCoeff τ t I) U K=
      commonEnergy s C hC τ t L U K:=by
  unfold gaussEnergy commonEnergy
  apply tsum_congr
  intro z
  rw [column_unwindowed_common s Q C hQ hC hQC τ t L z]
  rfl

end

theorem column_window_energy     
      (t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal ActualEisensteinCubic.O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (C*I) else 0)*heightCoeff τ t I)
     U  K (hK:0<K)(hU:∀z:ActualEisensteinCubic.O,0≤(U (‖eisEmbedding z‖^2/K)).re)
     J  E (hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2:=by
  have hh:=smoothed_window_energy_from_height V hVc hVs J Finset.univ
    (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
    (fun I:columns Q C hC.1 s.columns=>if L∣(I:Ideal ActualEisensteinCubic.O) then s.beta (C*I) else 0)
    τ t θ X hX U K hK hU E hE (fun v=>by
      simp only [element_span]
      rw [column_unwindowed_energy s Q C hQ hC hQC]
      exact henergy v)
  simpa only [ha,element_span,element_norm] using hh

end

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
