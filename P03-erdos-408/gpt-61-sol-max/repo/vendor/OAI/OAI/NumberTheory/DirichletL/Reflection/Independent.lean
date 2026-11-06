module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.Coefficient

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance independentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem ramifiedBlock_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})  j   S   u   m  :
    ‖ramifiedBlock hg j S u m‖ = 1 := by
  unfold ramifiedBlock
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact unitArgumentFactor_norm _ _ _ (unit_ramified_quotient_ne_zero _ (hg i) u m)

section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (D : ControlledStratumArithmetic p N a c mode) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (j : ι → ℕ)
include D s hp hg hchar hcop j

theorem sourceRowPhase_norm_le_one  
     
     
       
     
     
       R F  (hd : Disjoint R F)  u   m  :
    ‖sourceRowPhase s hp hg j R F u m‖ ≤ 1 := by
  rw [sourceRowPhase,norm_mul,norm_mul,residualWithFrozen_norm D hp hg hchar hcop R F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

theorem sourceSlotPhase_norm_le_one  
     
     
       
     
     
       S F  (hd : Disjoint S F)  u   m  :
    ‖sourceSlotPhase s hp hg j S F u m‖ ≤ 1 := by
  rw [sourceSlotPhase,norm_mul,norm_mul,markedWithFrozen_norm D hp hg hchar hcop S F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

end

omit [Fintype ι] in
theorem frozenArgument_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j j' : ι → ℕ)  F 
    (hj : ∀ i ∈ F, j i = j' i) : frozenArgument hg j F = frozenArgument hg j' F := by
  unfold frozenArgument
  simp_all

omit [Fintype ι] in
theorem frozenCore_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (c : Eis)
    (j j' : ι → ℕ)  F  (hj : ∀ i ∈ F, j i = j' i) :
    frozenCore hp hg c j F = frozenCore hp hg c j' F := by
  unfold frozenCore
  simp_all

omit [Fintype ι] in
theorem ramifiedBlock_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j j' : ι → ℕ)  F 
    (hj : ∀ i ∈ F, j i = j' i)  u   m  :
    ramifiedBlock hg j F u m = ramifiedBlock hg j' F u m := by
  unfold ramifiedBlock
  simp_all

section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (D : ControlledStratumArithmetic p N a c mode) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
include D s

theorem marked_phases_eq  
     
     
     hp  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
     j   R S F  (hd : Disjoint S F)  u   m  :
    sourceRowPhase s hp hg (markedActiveExponent S j) R F u m = sourceRowPhase s hp hg j R F u m ∧
    sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m = sourceSlotPhase s hp hg j S F u m ∧
    sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m = sourceFrozenPhase D s hp hg j F u m := by
  have hj : ∀ i ∈ F, markedActiveExponent S j i = j i := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
    simp only [markedActiveExponent,hn,ite_false]
  simp only [sourceRowPhase,sourceSlotPhase,sourceFrozenPhase,
    frozenArgument_congr hg _ _ F hj,frozenCore_congr hp hg c _ _ F hj,
    ramifiedBlock_congr hg _ _ F hj]
  simp

theorem marked_sourceColumn_eq  
     
       hc 
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})  j   S F  (hd : Disjoint S F)
     u   m   n b  :
    sourceColumn D s hc hg (markedActiveExponent S j) F u m n b =
      sourceColumn D s hc hg j F u m n b := by
  unfold sourceColumn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
  simp only [markedActiveExponent,hn,ite_false]

theorem mixed_coefficient_hybrid_original_exponents  
     
     
     hp   hc  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)  R S F 
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
     j  (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
     u   m   n b  (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      sourceColumn D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hd : Disjoint S F := hF.mono_left Finset.subset_union_right
  have he := mixed_coefficient_hybrid D s hp hc hg hcop hprimary R S F hRS hF hu j hRj hR u m n b hb
  obtain ⟨hr,hs,hf⟩ := marked_phases_eq D s hp hg j R S F hd u m
  rw [hr,hs,hf,marked_sourceColumn_eq D s hc hg j S F hd u m n b] at he
  exact he

end

end
end SevenEighths.InverseReflectedPhase

end OAI
