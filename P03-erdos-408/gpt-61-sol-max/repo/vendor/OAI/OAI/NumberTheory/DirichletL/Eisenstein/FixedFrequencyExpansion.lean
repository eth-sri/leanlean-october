module

public import OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 

namespace CubicEisenstein

section
open scoped     MatrixGroups Matrix

open     CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def fixedCusp (a0 c0:Eis) (mode:Bool)  :=
  if mode then lowerCuspMatrix c0 else A3WeylCusp a0

section
variable (D:ControlledStratumArithmetic p N a0 c0 mode) (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
include D hN hr hbase

section
variable (v:∀i,(Eis⧸Ideal.span {p i})ˣ)
include v

lemma relative  
       
     
      :
    D.matrix v*(fixedCusp a0 c0 mode)⁻¹∈levelThree := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact D.unramified_relative h3N hr hbase a0 (by simp) v
  · exact D.ramified_relative h3N hr hbase c0 (by simp) v

def relativeGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelThree :=
  ⟨D.matrix v*(fixedCusp a0 c0 mode)⁻¹,D.relative hN hr hbase v⟩

lemma relativeGamma_mul  
       
     
      :
    (D.relativeGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v := inv_mul_cancel_right (D.matrix v) (fixedCusp a0 c0 mode)

def fixedFactor (D:ControlledStratumArithmetic p N a0 c0 mode)  :=
  if mode then
    eisEmbedding (symbol (-c0) (D.matrix (fun _=>1) 0 0-c0*D.matrix (fun _=>1) 0 1)*
      symbol 1 (D.matrix (fun _=>1) 0 0))
  else eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem relative_character  
       
     
      :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  cases mode
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.false_eq_true,↓reduceIte,
      unramifiedFixedFactor] using D.unramified_character hN hr hbase a0 (by simp) v
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.true_eq,↓reduceIte,
      ramifiedFixedFactor] using D.ramified_character hN hr hbase c0 1 (by simp) (by simp) v

end

theorem fixedFactor_norm  
       
      : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

end

noncomputable def fourierWeight [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
    ((actualSextic (Ideal.span {p i}) (hg i)^j i)) (v i)

noncomputable def multiplierSum (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    fourierWeight hp hg j v*star (complexCharacter (D.relativeGamma hN hr hbase v))*
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))

noncomputable def bracketProduct (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
    bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

end ControlledStratumArithmetic
end

section
open scoped       MatrixGroups Matrix

open     CompletedGauss CompletedDyadic CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def sourceGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelTwo :=
  sourceLevelInclusion (D.relativeGamma hN hr hbase v)

section
variable (D:ControlledStratumArithmetic p N a0 c0 mode) (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
include D hN hr hbase

section
variable (v:∀i,(Eis⧸Ideal.span {p i})ˣ)
include v

lemma sourceGamma_mul  
       
     
      :
    (D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v :=
  D.relativeGamma_mul hN hr hbase v

lemma sourceGamma_character  
       
     
      :
    levelTwoComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  sourceLevelInclusion_character _

end

def datum (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  s.datum (D.sourceGamma hN hr hbase v) (by
    rw [D.sourceGamma_mul,D.denominator]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point  
       
     
     s 
     hp   hc0   v  :
    (D.datum hN hr hbase s hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

end

noncomputable def smoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

end ControlledStratumArithmetic

end

section
open scoped     MatrixGroups

open     CompletedGauss ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

structure FixedFourierGeometry (c:Eis) (h:Eis⧸Ideal.span {c}) where
  a0 : Eis
  c0 : Eis
  denominator_ne_zero : c0≠0
  denominator_dvd : c0∣c
  coprime : IsCoprime a0 c0
  point : eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h
  mode : Bool
  primary : if mode then lambda^2∣a0-1 else lambda^2∣c0-1
  shape : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)

lemma exists_fixedFourierGeometry  c  (hc:c≠0)  h  :
    Nonempty (FixedFourierGeometry c h) := by
  obtain ⟨a0,c0,hc0,hdiv,hcop,hpoint,ha,hcp⟩:=
    ShortDraftCRT.exists_normalized_rational_cusp (-3*Quotient.out h) c hc
  have hp:eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h := by
    rw [hpoint,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
    simp only [map_mul,map_neg,map_ofNat]
  by_cases hl:lambda∣c0
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 true)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,true,ha hl,s⟩⟩
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 false)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,false,hcp hl,s⟩⟩

def fixedFourierGeometry (c) (hc:c≠0) (h) :
    FixedFourierGeometry c h := Classical.choice (exists_fixedFourierGeometry c hc h)

namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

abbrev PhaseResidue := Eis⧸Ideal.span {ramifiedTraceLambda^3*G.c0}



end FixedFourierGeometry







end

 
open scoped         MatrixGroups

open CompletedGauss  
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

 

namespace CanonicalRowCompletion

section
open   CompletedGauss
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

lemma summand_mul_fixed_twist  φ χ   W   X   I J  :
    summand (φ*χ) W X I J=
      φ (primaryGenerator I*(primaryGenerator J)^3)*summand χ W X I J := by
  have he (η:Eis→*ℂ) : cubeWeight η J=
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        η (primaryGenerator J)^3/(Ideal.absNorm J:ℂ):=rfl
  rw [summand,summand,he,he]
  simp only [columnWeight,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring

end

open   CompletedGauss CanonicalQuadraticSieve
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
