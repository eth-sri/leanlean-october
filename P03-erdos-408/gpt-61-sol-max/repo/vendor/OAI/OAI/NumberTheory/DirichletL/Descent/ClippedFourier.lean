module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
public import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier SecondPassIntegration JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels CompletedGauss


section
variable (W:ℝ→ℂ)
include W

theorem clipped_fixed_window   (lo hi b:ℝ) (hlo:0<lo) (hb:1≤b)
    (hW:Function.support W⊆Set.Icc lo hi):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀c,1≤c→c≤b→∀y,0<y→wFresh y*W (c*y)=W (c*y):=by
  have hb0:0<b:=zero_lt_one.trans_le hb
  let a:=lo/b
  let B:=a+|hi|+1
  have ha:0<a:=div_pos hlo hb0
  obtain ⟨wFresh,hc,hone,hs⟩:=InverseSecondChildWindows.positive_cutoff a B ha (by dsimp [B];linarith [abs_nonneg hi])
  refine ⟨wFresh,a/2,B+1,half_pos ha,by dsimp [B];linarith [abs_nonneg hi],hc,hs,?_⟩
  intro c hc hcb y hy
  by_cases hz:W (c*y)=0
  · simp only [hz,mul_zero]
  have hw:=hW hz
  have hay:a≤y:=by
    apply (div_le_iff₀ hb0).mpr
    calc
      lo≤c*y:=hw.1
      _≤y*b:=by nlinarith
  have hyhi:y≤hi:=le_trans (by nlinarith) hw.2
  grind

theorem clipped_test_fourier    lo hi   hlo 
     hs   hW 
     wFresh  c θ y (hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*logPhase t (Real.log c+Real.log y))*(wFresh y*logPhase θ (Real.log y)):=by
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*logPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,logPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_logPhase_inversion g _).symm
      _= _:=by
        simp only [g,CubicReflectionKernel.logSchwartz_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  grind

end

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

section
variable (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1) (pool:Finset ι) (Ψ:ActualEisensteinCubic.O→*ℂ) (m f k:ActualEisensteinCubic.O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
include hpr pool Ψ m f k slots lists a

theorem canonical_clipped_mode_integrable
     
          
     g  wFresh  c θ X :
    Integrable (fun t:ℝ=>density g (Real.log c) t*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X):=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
      primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
  funext t
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem canonical_clipped_fourier
     
          
     W  lo hi  hlo  hs  hW 
     wFresh  c θ X (hc:0<c)(hX:0<X)(hwFresh:∀y,0<y→wFresh y*W (c*y)=W (c*y)):
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (clippedTest W c θ) X=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X:=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  have hints (U:Finset ι):Integrable (fun t:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t*
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        (primeMark slots lists a U*childLogTest wFresh (θ+t) (primeProductNorm p U/X)))):=by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
    funext t
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun U _=>hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX) (hwFresh _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX))]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end

end SevenEighths.InverseMoment



end OAI
