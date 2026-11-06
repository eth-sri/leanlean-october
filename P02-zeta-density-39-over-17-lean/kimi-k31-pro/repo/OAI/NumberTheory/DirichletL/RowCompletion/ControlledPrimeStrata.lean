module
public import OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end CubicEisenstein

end

end OAI
