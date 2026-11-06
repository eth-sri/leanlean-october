module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstActiveRadicalBudget

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstNonexceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic CenteredMomentRankinRadical CenteredMomentExceptionalAmplitudePair CenteredMomentSupportedCorrelation

lemma pair_conductor_root (q₁ q₂ B:ℝ)(_h₁:0≤q₁)(h₂:0≤q₂)
    (hB:0≤B)(hb₁:q₁≤B)(hb₂:q₂≤B):Real.sqrt (q₁*q₂)≤B := by
  have hh:=mul_le_mul hb₁ hb₂ h₂ hB
  have hs:=Real.sqrt_le_sqrt hh
  simpa only [←pow_two,Real.sqrt_sq hB] using hs

lemma scalar_conductor_algebra (s μ K T N E r C F q q₁ q₂:ℝ)
    (_hs:0≤s)(hμ:0≤μ)(hK:0≤K)(_hT:0<T)(hN:0<N)(hE:0<E)(hr:0<r)
    (hC:0≤C)(hF:0≤F)(hq:0≤q)(h₁:0≤q₁)(h₂:0≤q₂)
    (hscalar:s*T≤μ*C*K*Real.sqrt N/(E*r))
    (hc₁:q₁≤F*q*E*r^2)(hc₂:q₂≤F*q*E*r^2):
    s*T/N*Real.sqrt (q₁*q₂)≤μ*C*F*K*q*(r/Real.sqrt N) := by
  have hroot:=pair_conductor_root q₁ q₂ (F*q*E*r^2) h₁ h₂ (by positivity) hc₁ hc₂
  calc
    _≤(μ*C*K*Real.sqrt N/(E*r))/N*(F*q*E*r^2):=
      mul_le_mul (div_le_div_of_nonneg_right hscalar hN.le) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _=μ*C*F*K*q*(r/Real.sqrt N):=by
      have hn:Real.sqrt N≠0:=ne_of_gt (Real.sqrt_pos.mpr hN)
      have hn2:=Real.sq_sqrt hN.le
      field_simp
      linear_combination μ*C*K*F*q*hn2

theorem weighted_scalar_volume (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha.le hT.le hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:T/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a:=by
    apply (div_le_div_iff₀ hden ha).mpr
    nlinarith [hs]
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(T/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _=_:=by ring
