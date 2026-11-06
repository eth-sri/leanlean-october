/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Correlations.NPointSExp
import DOZZ.Statements.Correlations.ExtendedSeibergN
import DOZZ.Statements.Correlations.NPointCoulombPrefactor
import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation
import DOZZ.Statements.Correlations.OneInsertionMomentCeiling
import DOZZ.Statements.Correlations.OneInsertionErrorCeiling
import DOZZ.Statements.Correlations.TwoInsertionPointLoss
import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
import DOZZ.Statements.FourPoint.DualCrossingMultiplier
import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.GMC.CoulombMass
import DOZZ.Statements.Defs.ReflectionDOZZ
import DOZZ.Statements.Defs.ConformalWeight
import DOZZ.Statements.Defs.LFun
import DOZZ.Statements.Defs.DualMu
import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Statements.Brownian.IsSourceLateralProjection
import DOZZ.Statements.Brownian.ReflectionBarR
import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Statements.Brownian.ReflectionExponent
import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.Statements.Hypergeom.GaussParameterA
import DOZZ.Statements.Hypergeom.GaussParameterB
import DOZZ.Statements.Hypergeom.GaussParameterC
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset

/-! The definition `DOZZ.MobiusChart`. -/


open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Finite Möbius charts, with their coefficients kept explicit. -/
structure MobiusChart where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  determinant_ne : a * d - b * c ≠ 0

end DOZZ
