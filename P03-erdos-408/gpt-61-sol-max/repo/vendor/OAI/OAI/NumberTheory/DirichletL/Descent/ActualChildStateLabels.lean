module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildState

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn } (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex)  :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

section
variable (hp : ∀i,p i≠0) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta)) (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta))

lemma actual_cell_labels_cover    
      (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp hk hZ hbin hC hJ in
theorem actual_cell_labels_bound    
       
           
     
      :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

include hp hk hZ hbin hC hJ in
theorem actual_cell_squarefree_labels    
       
           
     
      :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

end

end SevenEighths.InverseMoment
end

end OAI
