module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildState
public import OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale
public import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

section
variable (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)


include hs hk in
theorem actual_cell_row_decrease  
       
       
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : cutoff≤ell+V) (hsmall : eta≤cutoff/16)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

include hpr hs in
theorem actual_cell_triple_puncture_nonzero
     
       
        (m : ActualEisensteinCubic.O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end

end SevenEighths.InverseMoment


end OAI
