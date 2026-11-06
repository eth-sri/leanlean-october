module

public import OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open Set
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical

section
open scoped Classical

open CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem thetaFullFrequency_tsum (c w : Eis→ℂ)
    (hsupp : ∀h:Eis,h≠0→c h≠0→∃p:ThetaFullIndex,thetaFullFrequency p=h) :
    (∑'h:{h:Eis // h≠0},w h.val*c h.val)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*c (thetaFullFrequency p) := by
  let phi : ThetaFullIndex→{h:Eis // h≠0} := fun p=>⟨thetaFullFrequency p,thetaFullFrequency_ne_zero p⟩
  let f : {h:Eis // h≠0}→ℂ := fun h=>w h.val*c h.val
  have hinj : Function.Injective phi := by
    intro p q hpq
    exact thetaFullFrequency_injective (by grind)
  change (∑'h:{h:Eis // h≠0},f h)=∑'p:ThetaFullIndex,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:ThetaFullIndex=>f (phi p))=>phi p.val)
  · exact hinj.comp Subtype.val_injective
  · intro h hh
    have hc : c h.val≠0 := by
      intro hz
      exact hh (by grind)
    obtain ⟨p,hp⟩:=hsupp h.val h.property hc
    have hphi : phi p=h := Subtype.ext hp
    have hfp : f (phi p)≠0 := by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  simp

end

section
open Filter MeasureTheory
open scoped Classical MatrixGroups

section
open CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma squarefreeCube_scale_le_norm_third (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (u:Eisˣ) (m:ℕ) :
    (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖≤
      ‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ) := by
  have hn:=cubePrime_norm_ge_one _ hI
  have hn':1≤‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ):=
    Real.one_le_rpow hn (by norm_num)
  have hb:(‖eisEmbedding (primaryGenerator J)‖^3)^(1/3:ℝ)=‖eisEmbedding (primaryGenerator J)‖:=by
    rw [←Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  have he:‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ)=
      (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    rw [map_mul,map_mul,map_pow,norm_mul,norm_mul,norm_pow,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),ramified_norm_third,hb]
  rw [he]
  have hscale:0≤(3:ℝ)^((m:ℝ)/6):=by positivity
  have hbn:0≤‖eisEmbedding (primaryGenerator J)‖:=norm_nonneg _
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hscale hn') hbn

lemma coefficient_polynomial_of_squarefree_cube_support (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hsupport:∀h:Eis,h≠0→F h≠0→∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)
    (hbound:∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→
      ∀(u:Eisˣ) (m:ℕ),
      ‖F ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖)
    (h:Eis) (hh:h≠0) : ‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  by_cases hz:F h=0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨u,m,I,J,hsq,hI,hJ,rfl⟩:=hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  have hb:=mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC
  linarith

theorem three_cusp_coefficients_polynomial_bound :
    ∃C:ℝ,0<C ∧ ∀h:Eis,h≠0→
      ‖sourceResidualFourierCoefficient h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) ∧
      ∀side:Bool,‖ramifiedBesselValue side h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_squarefree_cube_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  constructor
  · exact coefficient_polynomial_of_squarefree_cube_support sourceResidualFourierCoefficient C hC.le
      sourceResidualFourierCoefficient_full_squarefree_cube_support
      (by grind) h hh
  · intro side
    exact coefficient_polynomial_of_squarefree_cube_support (ramifiedBesselValue side) C hC.le
      (ramifiedBesselValue_squarefree_cube_support side)
      (by grind) h hh

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by positivity) _ hs
  intro h
  split_ifs with hh
  · positivity
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (by grind) (by positivity)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        ring
      _=_:=by simp_all

theorem three_cusp_coefficients_weighted_summable :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖sourceResidualFourierCoefficient h‖*‖cuspFrequency h‖^(-4:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖ramifiedBesselValue side h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_polynomial_bound
  constructor
  · exact coefficient_weighted_summable_of_polynomial _ C hC.le (by grind)
  · intro side
    exact coefficient_weighted_summable_of_polynomial _ C hC.le (by grind)

lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    grind

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      linarith
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      linarith

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=by positivity
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by grind
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by simp_all
      _=_:=by rw [←radial_inverse_weight _ hx];ring

end

local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_weighted_summable (j:Fin 3) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖(sourceCuspCoefficients j).value h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  fin_cases j
  · exact three_cusp_coefficients_weighted_summable.1
  · exact three_cusp_coefficients_weighted_summable.2 false
  · exact three_cusp_coefficients_weighted_summable.2 true

theorem sourceCuspRadialCoefficient_weighted_summable (j:Fin 3) (z:ℂ) :
    Summable (fun h:Eis=>‖sourceCuspRadialCoefficient j z h‖*
      (sourceCuspRadialLength h)^(-(3/2):ℝ)) := by
  let A:ℂ:=(-2*Real.pi*Complex.I)/(sourceCuspScale j:ℂ)^2
  have hs:=radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficients j).value A
    (sourceCuspCoefficients_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh:h=0
  · subst h
    simp only [ite_true,sourceCuspRadialCoefficient_zero,norm_zero,zero_mul]
  · rw [ite_eq_right hh,sourceCuspRadialCoefficient_norm,sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength,ite_eq_right hh]
    grind

end

section
open Filter MeasureTheory
open scoped Classical ContDiff MatrixGroups

section
open CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma SourceCuspDatum.cuspBarProfile_mellin_entire (d : SourceCuspDatum) :
    (∀s:ℂ,MellinConvergent (cuspBarProfile cubicSourceConjugateFunction d.point) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction d.point)) :=
  (conjugateSource_levelTwo_three_cusp_mellin_entire d.gamma d.index d.matrix rfl d.lower_ne_zero).1

lemma SourceCuspDatum.reflection_radial (d : SourceCuspDatum) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier*((v:ℂ)^(-2:ℂ)*
        radialBesselProfile sourceCuspRadialLength
          (sourceCuspRadialCoefficient d.index d.dualPoint)
          (sourceCuspRadialScale d.index) ((d.heightScale*v)⁻¹)) := by
  rw [d.reflection v hv,sourceCuspZFamily_eq_radialBesselProfile _ _ _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv)),Complex.cpow_neg,Complex.cpow_ofNat]
  ring

theorem completedBesselProfile_eq_finite_cuspProfiles
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h) (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        (thetaDerivativeScalar⁻¹*
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h)*
        cuspBarProfile cubicSourceConjugateFunction (d h).point v := by
  calc
    _=thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v:=by
      rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv,
        ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
    _=_:=by
      simp only [thetaTwistedCuspProfile,Finset.mul_sum]
      grind

def SourceCuspDatum.smoothedKernel (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.multiplier*(d.heightScale:ℂ)*
      ((thetaBesselScale/sourceCuspRadialScale d.index:ℝ):ℂ)^2)*
    ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
      CubicReflectionKernel.paperKernel (Vstar W)
        (27*thetaBesselScale^2*(sourceCuspRadialScale d.index)^2*X*
          sourceCuspRadialLength n/d.heightScale^2)

end

section
open CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaBesselScale_square : thetaBesselScale^2=(1/27:ℝ) := by
  rw [thetaBesselScale_eq,div_pow,one_pow,Real.sq_sqrt (by norm_num)]

lemma sourceCuspRadialScale_ratio (j:Fin 3) :
    thetaBesselScale/sourceCuspRadialScale j=sourceCuspScale j := by
  rw [sourceCuspRadialScale]
  field_simp [thetaBesselScale_pos.ne']

lemma sourceCuspKernel_argument (j:Fin 3) (X r Q:ℝ) :
    27*thetaBesselScale^2*(sourceCuspRadialScale j)^2*X*r/Q^2=
      X*r/(27*(sourceCuspScale j)^2*Q^2) := by
  rw [sourceCuspRadialScale,div_pow,thetaBesselScale_square]
  ring

lemma SourceCuspDatum.smoothedKernel_eq (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  simp only [SourceCuspDatum.smoothedKernel,sourceCuspRadialScale_ratio,sourceCuspKernel_argument]

end

open CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_finite_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (d h).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  let w:(Eis⧸Ideal.span {c})→ℂ:=fun h=>thetaDerivativeScalar⁻¹*
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h
  have hFG:∀v:ℝ,0<v→completedBesselProfile Ψ thetaBesselScale v=∑h,w h*G h v:=
    completedBesselProfile_eq_finite_cuspProfiles Ψ Q hperiod c hc hcQ d hd
  have hG (h:Eis⧸Ideal.span {c}) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:Eis⧸Ideal.span {c}) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:Eis⧸Ideal.span {c}) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (by grind) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:Eis⧸Ideal.span {c}) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simp_all
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (by grind)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_all
    _=_:=by
      rw [Finset.mul_sum]
      grind

theorem completedT_canonical_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (finiteTwistCusp c hc h).smoothedKernel W X :=
  completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ
    (finiteTwistCusp c hc) (finiteTwistCusp_point c hc) W v0 v1 hv0 hWs hW X hX

end

open scoped Classical MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspReduction : SL(2,Eis) →* SL(2,Eis⧸Ideal.span {(3:Eis)}) :=
  Matrix.SpecialLinearGroup.map (n:=Fin 2) (Ideal.Quotient.mk (Ideal.span {(3:Eis)}))

abbrev FixedCuspSector := fixedCuspReduction.range

instance : Finite FixedCuspSector := by
  let : Finite (Eis⧸Ideal.span {(3:Eis)}) := finite_quotient_span (by norm_num : (3:Eis)≠0)
  infer_instance

end CubicEisenstein

end

end OAI
