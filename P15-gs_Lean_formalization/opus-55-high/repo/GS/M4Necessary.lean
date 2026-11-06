module

public import GS.Unitary.FourFactorCounterexample

@[expose] public section

noncomputable section
namespace GS.M4
open GS.UnitaryGeometry

/-- Unconditional counterexample for the specified four-factor class. -/
theorem counterexample : InA4 2 2 2 2 P P P Q ∧ Orthogonal Q ∧
    ¬ InA4Orth 2 2 2 2 P P P Q :=
  ⟨Q_mem_A4,Q_orthogonal,fun ⟨_,_,_,_,hb₁,hb₂,hb₃,hb₄,ho₁,ho₂,ho₃,ho₄,he⟩ => UnitaryFour.Q_not_mem_A4Unitary ⟨_,_,_,_,
    ofRealMatrix_blockDiagonal hb₁,ofRealMatrix_blockDiagonal hb₂,ofRealMatrix_blockDiagonal hb₃,ofRealMatrix_blockDiagonal hb₄,
    ofRealMatrix_unitary ho₁,ofRealMatrix_unitary ho₂,ofRealMatrix_unitary ho₃,ofRealMatrix_unitary ho₄,
    by have := congrArg ofRealMatrix he; simp only [GS.product4, ofRealMatrix_mul] at this; tauto⟩⟩

end GS.M4
