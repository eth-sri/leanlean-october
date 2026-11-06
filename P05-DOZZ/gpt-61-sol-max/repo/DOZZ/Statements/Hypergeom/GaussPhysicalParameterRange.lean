/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Hypergeom.PhysicalRange
import Batteries.Tactic.Alias

/-! The statement `DOZZ.gauss_physical_parameter_range`,
proved by `DOZZ.Proofs.gauss_physical_parameter_range`. -/

public section


namespace DOZZ

/-- The strict four-point Seiberg range of [KRV, §4.3]. In this range [KRV, (Fundrelation)] has no
junk Gamma factors and both undivided coefficients are positive. -/
alias gauss_physical_parameter_range := DOZZ.Proofs.gauss_physical_parameter_range

end DOZZ
