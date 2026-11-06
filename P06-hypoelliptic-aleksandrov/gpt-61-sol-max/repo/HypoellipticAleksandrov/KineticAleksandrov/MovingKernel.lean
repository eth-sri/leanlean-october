module

public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import HypoellipticAleksandrov.Ambient.Basic

/-!
# Moving-fiber kernels

This module fixes the carrier for the terminal evolution kernel.  Invalid
time pairs and off-domain source states have no values: the master kernel is
defined only on the corresponding valid-query subtype.  Fixed-time kernels
are obtained from that one master kernel by `Kernel.comap` and
`Kernel.comapRight`.
-/

@[expose] public section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The ambient fixed-time state `(y, z)`. -/
abbrev EvolutionAmbientState (n : ℕ) := PDE.Vec n × PDE.Vec n

variable {n : ℕ} (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (σ : ℝ)

/-- The moving spatial domain obtained by translating the base domain. -/
def movingDomain  :
    PDE.VelocityRegion n :=
  PDE.translateSet (γ σ) Ω

/-- The open ambient state fiber at a fixed time. -/
def evolutionStateSet  : Set (EvolutionAmbientState n) :=
  movingDomain Ω γ σ ×ˢ Set.univ

/-- A state whose diffused coordinate lies in the moving spatial domain. -/
abbrev EvolutionState {n : ℕ} (Ω : PDE.VelocityRegion n)
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :=
  {p : EvolutionAmbientState n // p ∈ evolutionStateSet Ω γ σ}

/-- The diffused-coordinate subtype in a moving spatial fiber. -/
abbrev EvolutionPosition {n : ℕ} (Ω : PDE.VelocityRegion n)
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :=
  {y : PDE.Vec n // y ∈ movingDomain Ω γ σ}

/-- The raw `(sigma, (tau, (y, z)))` query carrier. -/
abbrev RawEvolutionQuery (n : ℕ) :=
  ℝ × (ℝ × EvolutionAmbientState n)

/-- A query with valid time order and a source state in the moving fiber. -/
abbrev EvolutionQuery {n : ℕ} (Ω : PDE.VelocityRegion n)
    (γ : ℝ → PDE.Vec n) :=
  {q : RawEvolutionQuery n //
    q.1 ≤ q.2.1 ∧ q.2.2 ∈ evolutionStateSet Ω γ q.1}

variable {n : ℕ}

variable {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n}

/-- Measurability of the translated moving spatial domain. -/
theorem measurableSet_movingDomain   (hΩ : MeasurableSet Ω) (σ : ℝ) :
    MeasurableSet (movingDomain Ω γ σ) := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact hΩ.preimage (measurable_id.sub measurable_const)

/-- Openness of the translated moving spatial domain. -/
theorem isOpen_movingDomain   (hΩ : IsOpen Ω) (σ : ℝ) :
    IsOpen (movingDomain Ω γ σ) := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact hΩ.preimage (continuous_id.sub continuous_const)

/-- Measurability of the ambient moving state fiber. -/
theorem measurableSet_evolutionStateSet   (hΩ : MeasurableSet Ω) (σ : ℝ) :
    MeasurableSet (evolutionStateSet Ω γ σ) := (measurableSet_movingDomain hΩ σ).prod MeasurableSet.univ

variable (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (σ τ : ℝ) (hστ : σ ≤ τ)

/-- The canonical valid query associated with a fixed-time source state. -/
def evolutionQueryOfState
    (p : EvolutionState Ω γ σ) : EvolutionQuery Ω γ :=
  ⟨(σ, (τ, p.1)), hστ, p.2⟩

/-- The canonical query lift is measurable on its subtype source. -/
theorem measurable_evolutionQueryOfState   :
    Measurable (evolutionQueryOfState Ω γ σ τ hστ) := by
  apply Measurable.subtype_mk
  fun_prop

/-- One master kernel on all valid source/time queries. -/
structure MovingFiberKernel {n : ℕ} (Ω : PDE.VelocityRegion n)
    (γ : ℝ → PDE.Vec n) where
  master : ProbabilityTheory.Kernel
    (EvolutionQuery Ω γ) (EvolutionAmbientState n)
  /-- Every master output is supported on the open terminal state fiber. -/
  terminal_support : ∀ q : EvolutionQuery Ω γ,
    (master q).restrict (evolutionStateSet Ω γ q.1.2.1) = master q
  /-- The master kernel has sub-Markov mass. -/
  mass_le_one : ∀ q : EvolutionQuery Ω γ, master q Set.univ ≤ 1

namespace MovingFiberKernel

/-- Evaluation on a measurable target is jointly measurable in the query. -/
theorem jointlyMeasurable_apply {n : ℕ}
    {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (E : Set (EvolutionAmbientState n))
    (hE : MeasurableSet E) : type_of% (K.master.measurable_coe hE) := K.master.measurable_coe hE

variable {n : ℕ}

variable {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (σ τ : ℝ) (hστ : σ ≤ τ)

/-- Derive the fixed-time kernel from the one ambient master kernel. -/
noncomputable def fiberKernel
     :
    ProbabilityTheory.Kernel
      (EvolutionState Ω γ σ) (EvolutionState Ω γ τ) :=
  ProbabilityTheory.Kernel.comapRight
    (ProbabilityTheory.Kernel.comap K.master
      _
      (measurable_evolutionQueryOfState Ω γ σ τ hστ))
    (MeasurableEmbedding.subtype_coe
      (measurableSet_evolutionStateSet hΩ τ))

variable (p : EvolutionState Ω γ σ)

/-- The derived fiber is the right-measure comap of the master output. -/
theorem fiberKernel_apply
      :
    K.fiberKernel hΩ σ τ hστ p =
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) := by
  rfl

/-- Mapping a derived fiber measure back to the ambient state recovers master. -/
theorem map_fiberKernel_eq_master
      :
    Measure.map
        ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (K.fiberKernel hΩ σ τ hστ p) =
      K.master (evolutionQueryOfState Ω γ σ τ hστ p) := by
  let sharedTerm_2e64ab87b2 := (((↑) : { x : EvolutionAmbientState n // x ∈ evolutionStateSet Ω γ τ } → EvolutionAmbientState n))
  let sharedTerm_cfc94627c2 := ((K.master (evolutionQueryOfState Ω γ σ τ hστ p)))
  rw [MovingFiberKernel.fiberKernel_apply]
  have hmap :
      Measure.map
          sharedTerm_2e64ab87b2
          (Measure.comap
            sharedTerm_2e64ab87b2
            sharedTerm_cfc94627c2) =
        sharedTerm_cfc94627c2.restrict
          (evolutionStateSet Ω γ τ) := by
    simpa only [Subtype.range_coe] using
      (MeasurableEmbedding.subtype_coe
        (measurableSet_evolutionStateSet hΩ τ)).map_comap
        sharedTerm_cfc94627c2
  change Measure.map
      sharedTerm_2e64ab87b2
      (Measure.comap
        sharedTerm_2e64ab87b2
        sharedTerm_cfc94627c2) =
    sharedTerm_cfc94627c2
  exact hmap.trans
    (K.terminal_support (evolutionQueryOfState Ω γ σ τ hστ p))

/-- Every derived fiber measure is sub-Markov. -/
theorem fiberKernel_mass_le_one
      :
    K.fiberKernel hΩ σ τ hστ p Set.univ ≤ 1 := (Eq.mpr (id (congrArg (fun _a => _a univ ≤ 1) (fiberKernel_apply K hΩ σ τ hστ p)))
  (Trans.trans
    (Trans.trans
      (MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe (measurableSet_evolutionStateSet hΩ τ))
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) univ)
      (measure_mono (subset_univ (Subtype.val '' univ))))
    (K.mass_le_one (evolutionQueryOfState Ω γ σ τ hστ p))))

variable (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (τ : ℝ)

/-- The first coordinate of a terminal ambient state, with its domain proof. -/
def firstPosition   : EvolutionState Ω γ τ → EvolutionPosition Ω γ τ :=
  fun p => ⟨p.1.1, p.2.1⟩

/-- Measurability of the first-coordinate map between moving fibers. -/
theorem measurable_firstPosition   :
    Measurable (firstPosition Ω γ τ) := by
  apply Measurable.subtype_mk
  fun_prop

variable {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n} (K : MovingFiberKernel Ω γ)

/-- The master first marginal, defined by Mathlib's `Kernel.fst`. -/
noncomputable def firstMarginal
     :
    ProbabilityTheory.Kernel (EvolutionQuery Ω γ) (PDE.Vec n) :=
  K.master.fst

/-- Application of the first marginal is the first-coordinate projection. -/
theorem firstMarginal_apply
     (q : EvolutionQuery Ω γ)
    (E : PDE.VelocityRegion n) (hE : MeasurableSet E) :
    K.firstMarginal q E = K.master q {p | p.1 ∈ E} := ProbabilityTheory.Kernel.fst_apply' K.master q hE

variable (hΩ : MeasurableSet Ω)

variable (σ τ : ℝ) (hστ : σ ≤ τ)

/-- The fixed-time first marginal derived from the same fiber kernel. -/
noncomputable def fiberFirstMarginal

     :
    ProbabilityTheory.Kernel
      (EvolutionState Ω γ σ) (EvolutionPosition Ω γ τ) :=
  ProbabilityTheory.Kernel.map
    (K.fiberKernel hΩ σ τ hστ) (firstPosition Ω γ τ)

/-- Mapping the fixed-time first marginal back gives the master first marginal. -/
theorem map_fiberFirstMarginal_eq_firstMarginal

     (p : EvolutionState Ω γ σ) :
    Measure.map
        ((↑) : EvolutionPosition Ω γ τ → PDE.Vec n)
        (K.fiberFirstMarginal hΩ σ τ hστ p) =
      K.firstMarginal (evolutionQueryOfState Ω γ σ τ hστ p) := by
  rw [MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _
      (measurable_firstPosition Ω γ τ) p]
  calc
    Measure.map Subtype.val
        (Measure.map (firstPosition Ω γ τ)
          (K.fiberKernel hΩ σ τ hστ p)) =
        Measure.map Prod.fst
          (Measure.map ((↑) : EvolutionState Ω γ τ →
            EvolutionAmbientState n) (K.fiberKernel hΩ σ τ hστ p)) := by
      rw [Measure.map_map measurable_subtype_coe
        (measurable_firstPosition Ω γ τ),
        Measure.map_map measurable_fst measurable_subtype_coe]
      rfl
    _ = Measure.map Prod.fst
          (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) := by
      simp_all [MovingFiberKernel.map_fiberKernel_eq_master]
    _ = K.firstMarginal (evolutionQueryOfState Ω γ σ τ hστ p) := by
      rfl

/-- Endpoint identity for the derived fixed-time kernel. -/
def HasEndpoint
      : Prop :=
  ∀ σ : ℝ,
    K.fiberKernel hΩ σ σ le_rfl =
      (ProbabilityTheory.Kernel.id :
        ProbabilityTheory.Kernel (EvolutionState Ω γ σ) (EvolutionState Ω γ σ))

/-- Chapman--Kolmogorov equality for the same derived kernel family. -/
def HasComposition
      : Prop :=
  ∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
    K.fiberKernel hΩ σ τ (hσr.trans hrτ) =
      K.fiberKernel hΩ r τ hrτ ∘ₖ K.fiberKernel hΩ σ r hσr

end MovingFiberKernel

/-- Lift a small-domain query to the corresponding large-domain query. -/
def largeQueryOfSmall {n : ℕ}
    {Ωsmall Ωlarge : PDE.VelocityRegion n}
    {γsmall γlarge : ℝ → PDE.Vec n}
    (hsub : ∀ σ, movingDomain Ωsmall γsmall σ ⊆
      movingDomain Ωlarge γlarge σ)
    (q : EvolutionQuery Ωsmall γsmall) : EvolutionQuery Ωlarge γlarge :=
  ⟨q.1, q.2.1, ⟨hsub q.1.1 q.2.2.1, q.2.2.2⟩⟩

namespace MovingFiberKernel

/-- Ambient measure domination after zero extension outside the small fiber. -/
def IsZeroExtensionDominatedBy {n : ℕ}
    {Ωsmall Ωlarge : PDE.VelocityRegion n}
    {γsmall γlarge : ℝ → PDE.Vec n}
    (Ksmall : MovingFiberKernel Ωsmall γsmall)
    (Klarge : MovingFiberKernel Ωlarge γlarge)
    (hsub : ∀ σ, movingDomain Ωsmall γsmall σ ⊆
      movingDomain Ωlarge γlarge σ) : Prop :=
  ∀ q : EvolutionQuery Ωsmall γsmall,
    Ksmall.master q ≤ Klarge.master (largeQueryOfSmall hsub q)

end MovingFiberKernel

end HypoellipticAleksandrov.KineticAleksandrov
