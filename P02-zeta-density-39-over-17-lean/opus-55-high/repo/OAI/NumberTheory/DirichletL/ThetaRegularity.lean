module
public import OAI.NumberTheory.DirichletL.GaussianTheta
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

export OAI.EisensteinSchwartzPoisson (O)

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    simp_all)

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

end SevenEighths.ThetaRegularity

end

end OAI
