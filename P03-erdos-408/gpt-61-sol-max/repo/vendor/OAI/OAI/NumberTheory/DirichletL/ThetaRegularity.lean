module

public import OAI.NumberTheory.DirichletL.GaussianTheta
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem lattice_gap  z  (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

variable (c : O) [NeZero c]




end SevenEighths.ThetaRegularity

end

end OAI
