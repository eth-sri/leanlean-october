module

public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
public import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma conjugate_source_support (F:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simp_all)

end SevenEighths.CenteredMomentDetectorPlainSlotProfile

end

end OAI
