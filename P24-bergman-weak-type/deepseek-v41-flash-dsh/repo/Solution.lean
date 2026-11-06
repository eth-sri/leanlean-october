/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
import BergmanWeakType.Boundary.CapMass
import BergmanWeakType.Boundary.ColumnBound
import BergmanWeakType.Boundary.HalfDiskIntegral
import BergmanWeakType.Boundary.Sharpness
import BergmanWeakType.CompactGap
import BergmanWeakType.Comparison
import BergmanWeakType.Definitions
import BergmanWeakType.DiskSharp
import BergmanWeakType.Domain
import BergmanWeakType.DomainLowerBound
import BergmanWeakType.Kernel
import BergmanWeakType.KernelIntegrability
import BergmanWeakType.Measure
import BergmanWeakType.Notation
import BergmanWeakType.Reproduction
import BergmanWeakType.Rigidity.AnalyticInverse
import BergmanWeakType.Rigidity.BoundedRigidity
import BergmanWeakType.Rigidity.ChangeOfVariables
import BergmanWeakType.Rigidity.CoreGap
import BergmanWeakType.Rigidity.DiskReproducing
import BergmanWeakType.Rigidity.DiskSimilarity
import BergmanWeakType.Rigidity.DomainGap
import BergmanWeakType.Rigidity.IntegralPhase
import BergmanWeakType.Rigidity.KernelTransform
import BergmanWeakType.Rigidity.MobiusGeometry
import BergmanWeakType.Rigidity.Perturbation
import BergmanWeakType.Rigidity.PhaseRigidity
import BergmanWeakType.Rigidity.PolarIntegral
import BergmanWeakType.Rigidity.RiemannMapping
import BergmanWeakType.Rigidity.UnitDiscShift
import BergmanWeakType.RigidityWitness
import BergmanWeakType.WeakType
import BergmanWeakType.Weighted.AngularMean
import BergmanWeakType.Weighted.AnnularSharpness
import BergmanWeakType.Weighted.AnnulusMeasure
import BergmanWeakType.Weighted.BetaIntegral
import BergmanWeakType.Weighted.CircleMobius
import BergmanWeakType.Weighted.CompactIntegral
import BergmanWeakType.Weighted.DiskCap
import BergmanWeakType.Weighted.DiskSupermean
import BergmanWeakType.Weighted.KernelPDE
import BergmanWeakType.Weighted.KernelPotential
import BergmanWeakType.Weighted.MassCoordinate
import BergmanWeakType.Weighted.MovingCap
import BergmanWeakType.Weighted.Normalizer
import BergmanWeakType.Weighted.NormalizerEndpoint
import BergmanWeakType.Weighted.NormalizerRadial
import BergmanWeakType.Weighted.PoissonCap
import BergmanWeakType.Weighted.PolarCap
import BergmanWeakType.Weighted.PolarIntegral
import BergmanWeakType.Weighted.PolarKernel
import BergmanWeakType.Weighted.PolarPotential
import BergmanWeakType.Weighted.QuotientCap
import BergmanWeakType.Weighted.RadialFlux
import BergmanWeakType.Weighted.RadialKernel
import BergmanWeakType.Weighted.SmoothCap
import BergmanWeakType.Weighted.WeightedPotential
import BergmanWeakType.WeightedSharp

/-! # Completed proof development

All seven declarations listed in comparator.json are implemented with the exact Challenge
statements. The proofs use only the permitted standard Lean axioms.
-/
