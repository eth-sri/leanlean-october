module
public import OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic
open scoped Classical SchwartzMap

open scoped Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection


namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end

section
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end

open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

open scoped Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CubicKubota ConcreteTraceCRT
open LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_right he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_left helig,hz,zero_div,star_zero]

lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) : 0< m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣ramifiedTraceLambda:=by
    change lambda∣paperLambda
    rw [paperLambda_eq]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  pm_423 fixedCuspArrayIndex hm pow_zero mul_one hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.not_isUnit (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)

def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then paperLambdaUnit*w^2*u else -(w^2*u*paperLambdaUnit⁻¹)

def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1

lemma paperLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    paperLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:ramifiedTraceLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change paperLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [paperLambda_eq,pow_succ]
    have hi:(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:ramifiedTraceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:ramifiedTraceLambda≠0:=by
    pm_6471
  apply mul_left_cancel₀ hn
  rw [paperLambdaQuotient_mul _ hd,hp]

theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryGenerator I*(primaryGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    pm_437 sourceCuspPhaseNumerator sourcePhaseUnit sourcePhaseExponent ite_true fixedCuspArrayIndex Units.val_mul Units.val_pow_eq_pow_val
    change paperLambda*w.val^2*((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)=_
    rw [paperLambda_eq,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_eq_right hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [paperLambdaQuotient_succ]
      ring

theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→ Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J *
      (∏i,bracket (actualSextic (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J *
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→ Fin 3,reflectedBranch P hg exponent e (primaryGenerator I) (primaryGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring

end

open ActualEisensteinCubic CompletedGauss CubicKubota ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def phaseUpperUnit : Eisˣ := s.upper_unit.unit

lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec

def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)

theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→ Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→ Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J *
        reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J =
      s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [A4BadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J *
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J *
      (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J *
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→ Fin 3,reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring

end FixedCuspShape

namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→ Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib

def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→ Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring

end ControlledStratumArithmetic

end CubicEisenstein

end

end OAI
