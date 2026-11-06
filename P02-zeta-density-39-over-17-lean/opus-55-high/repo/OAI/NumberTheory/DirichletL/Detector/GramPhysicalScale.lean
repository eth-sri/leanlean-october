module
public import OAI.NumberTheory.DirichletL.Detector.GramMobiusLattice
public import OAI.NumberTheory.DirichletL.Detector.GramNonexceptionalBlock
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)

section
variable (N : ℝ) (hN : 0<N) (m : O×O)
include N hN m
lemma physicalPoint_first_norm :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  pm_820

lemma physicalPoint_second_norm :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  pm_820
end

end SevenEighths.ProbeGramCommon
end

end OAI
