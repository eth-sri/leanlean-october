/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.GMC.CoulombMass
import DOZZ.Statements.GMC.GmcRootedMeasure
import DOZZ.Statements.Defs.ConformalWeight
import DOZZ.Statements.Defs.LFun
import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Statements.Brownian.IsSourceLateralProjection
import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
import DOZZ.Statements.Hypergeom.GaussCutPlane
import DOZZ.Statements.Hypergeom.GaussFMinus
import DOZZ.Statements.Hypergeom.GaussFPlus
import DOZZ.Statements.Hypergeom.IsRealGaussSolution
import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Statements.Hypergeom.GaussParameterA
import DOZZ.Statements.Hypergeom.GaussParameterB
import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Statements.Hypergeom.PlanarGaussConstant

/-! The definition `DOZZ.fourPointSExp`. -/


open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The zero-mode exponent for the four-point function `T`, [KRV, (Tdefi0)]. -/
noncomputable def fourPointSExp (γ α₀ α₁ α₂ α₃ : ℝ) : ℝ :=
  (α₀ + α₁ + α₂ + α₃ - 2 * Q γ) / γ

end DOZZ
