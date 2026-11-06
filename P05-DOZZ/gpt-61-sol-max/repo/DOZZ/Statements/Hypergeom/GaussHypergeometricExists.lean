/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import Batteries.Tactic.Alias

/-! The statement `DOZZ.gauss_hypergeometric_exists`,
proved by `DOZZ.Proofs.gauss_hypergeometric_exists`. -/

public section


namespace DOZZ

/-- Existence of the principal continuation of the Gauss hypergeometric function [KRV, (Fpmdef)]. No
arbitrary choice-defined Gauss function is exported; the witnesses are used only through their
characterization. -/
alias gauss_hypergeometric_exists := DOZZ.Proofs.gauss_hypergeometric_exists

end DOZZ
