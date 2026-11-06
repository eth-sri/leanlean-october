module

public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCellEnergy
public import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps  pool   Q   k  :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

end SevenEighths.InverseMomentFirstOriginalProfile


end OAI
