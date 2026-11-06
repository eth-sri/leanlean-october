/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Lateral.ReflectionJointLaw
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_lateral_GMC_decomposition`,
proved by `DOZZ.Proofs.equatorGFF_lateral_GMC_decomposition`. -/

public section


namespace DOZZ

/-- The equator field and its GMC admit the two-sided radial/lateral decomposition. The lateral
projection is defined by `lateralProjectedGMC`, so this theorem supplies the independence,
stationarity, and intensity interface from the `IsGMCOf` carrier. See [KRV, §3.1]. -/
alias equatorGFF_lateral_GMC_decomposition := DOZZ.Proofs.equatorGFF_lateral_GMC_decomposition

end DOZZ
