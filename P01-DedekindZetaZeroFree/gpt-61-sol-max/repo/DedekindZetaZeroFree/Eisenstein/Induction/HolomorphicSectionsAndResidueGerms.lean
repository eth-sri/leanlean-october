module

public import DedekindZetaZeroFree.Theta.Whittaker.RotatedFirstRootRapidDecay
public import DedekindZetaZeroFree.Theta.Profiles.InducedAmplitudeDerivativeBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.EquivariantSmoothSections

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalEisensteinData

open MeasureTheory
open scoped Topology NNReal

section Core

variable {K Gfin H : Type*} [Group K] [Group Gfin] [TopologicalSpace Gfin]
    [AddCommGroup H] [Module ℂ H]

structure CompactTypeStage (ρK : Representation ℂ K H) where
  space : Submodule ℂ H
  finiteDimensional : FiniteDimensional ℂ space
  invariant : CompactProjectors.IsStable ρK space

section
variable (ρK : Representation ℂ K H)
    (ρfin : Representation ℂ Gfin H) (smoothSpace : Submodule ℂ H)
include ρK ρfin smoothSpace
def finiteLevelTypeStage  
    (U : CompactOpenLevel Gfin) (T : CompactTypeStage ρK) : Submodule ℂ H :=
  smoothSpace ⊓ fixedSubmodule ρfin U.toOpenSubgroup.toSubgroup ⊓ T.space

def hcHeckeCore   : Submodule ℂ H :=
  ⨆ U : CompactOpenLevel Gfin, ⨆ T : CompactTypeStage ρK,
    finiteLevelTypeStage ρK ρfin smoothSpace U T
end


end Core

section ScalarOperators

variable {G Q A Y : Type*} [Group G] [MeasurableSpace A] [MeasurableSpace Y]

def EisensteinSummable (rationalLift : Q → G) (fR : G → ℂ) (g : G) : Prop :=
  Summable (fun γ : Q => ‖fR (rationalLift γ * g)‖)

def eisenstein (rationalLift : Q → G) (fR : G → ℂ) (g : G)
    (_h : EisensteinSummable rationalLift fR g) : ℂ :=
  ∑' γ : Q, fR (rationalLift γ * g)

end ScalarOperators

section SmoothTopology

variable {G H : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]

structure DifferentialCompact (G J : Type*) [TopologicalSpace G] where
  compact : Set G
  isCompact : IsCompact compact
  operator : J

instance {J : Type*} (i : DifferentialCompact G J) : CompactSpace i.compact :=
  isCompact_iff_compactSpace.mp i.isCompact

section
variable {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
include J D
def derivativeRestriction  
    (i : DifferentialCompact G J) : H →ₗ[ℂ] C(i.compact, ℂ) where
  toFun h := (D i.operator h).restrict i.compact
  map_add' := by intro x y; ext g; simp
  map_smul' := by intro c x; ext g; simp

def smoothSeminorm  
    (i : DifferentialCompact G J) : Seminorm ℂ H :=
  (normSeminorm ℂ C(i.compact, ℂ)).comp (derivativeRestriction D i)

def SmoothPowerSeriesOn  
    (z₀ : ℂ) (ρ : ℝ) (a : ℕ → H) (f : ℂ → H) : Prop :=
  ∀ i : DifferentialCompact G J, ∀ r : ℝ, 0 ≤ r → r < ρ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
      smoothSeminorm D i ((∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z) < ε

def SmoothHolomorphicOn  
    (f : ℂ → H) (O : Set ℂ) : Prop :=
  ∀ z₀ ∈ O, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    ∃ a : ℕ → H, SmoothPowerSeriesOn D z₀ ρ a f
end









end SmoothTopology

end DedekindZetaZeroFree.KPGlobalEisensteinData

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalEisensteinData

open MeasureTheory
open scoped Topology NNReal

section Induction

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]




































end Induction

section Core

variable {K Gfin H : Type*} [Group K] [Group Gfin] [TopologicalSpace Gfin]
    [AddCommGroup H] [Module ℂ H]

end Core

section ScalarOperators

variable {G Q A Y : Type*} [Group G] [MeasurableSpace A] [MeasurableSpace Y]

section
variable (μ : Measure A) (w : G) (n : A → G)
    (fR : G → ℂ) (g : G)
include μ w n fR g
def IntertwinerIntegrable   : Prop :=
  Integrable (fun x => fR (w * n x * g)) μ

def intertwiner   (_h : IntertwinerIntegrable μ w n fR g) : ℂ :=
  ∫ x, fR (w * n x * g) ∂μ
end








end ScalarOperators

section SmoothTopology

variable {G H : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]










end SmoothTopology

end DedekindZetaZeroFree.KPGlobalEisensteinData

end
end
