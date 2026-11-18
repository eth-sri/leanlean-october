module

public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Cylinders
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling
section

open MeasureTheory ProbabilityTheory

variable {α β γ α' β' γ' : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace α'] [MeasurableSpace β'] [MeasurableSpace γ']

/-- Conjugate a kernel `κ : α' → β'` by measurable equivalences `e : α ≃ᵐ α'`, `f : β ≃ᵐ β'`:
`x ↦ (κ (e x)).map f.symm`. -/
def kernelConj (e : α ≃ᵐ α') (f : β ≃ᵐ β') (κ : Kernel α' β') : Kernel α β :=
  (κ.comap e e.measurable).map f.symm

theorem kernelConj_apply (e : α ≃ᵐ α') (f : β ≃ᵐ β') (κ : Kernel α' β') (a : α) :
    kernelConj e f κ a = (κ (e a)).map f.symm := by
  rw [kernelConj, Kernel.map_apply _ f.symm.measurable, Kernel.comap_apply]

theorem kernelConj_id (e : α ≃ᵐ α') :
    kernelConj e e (Kernel.id : Kernel α' α') = Kernel.id := by
  ext a : 1
  rw [kernelConj_apply, Kernel.id_apply, Kernel.id_apply]
  exact (Measure.map_dirac' e.symm.measurable (e a)).trans (by rw [e.symm_apply_apply])

theorem kernelConj_comp (e : α ≃ᵐ α') (f : β ≃ᵐ β') (g : γ ≃ᵐ γ')
    (κ : Kernel α' β') (η : Kernel β' γ') :
    kernelConj e g (η ∘ₖ κ) = kernelConj f g η ∘ₖ kernelConj e f κ := by
  ext a S hS
  rw [kernelConj_apply, Kernel.comp_apply, Kernel.comp_apply, kernelConj_apply,
    Measure.map_apply g.symm.measurable hS,
    Measure.bind_apply (g.symm.measurable hS) η.measurable.aemeasurable,
    Measure.bind_apply hS (kernelConj f g η).measurable.aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hS) f.symm.measurable]
  refine lintegral_congr fun y => ?_
  rw [kernelConj_apply, f.apply_symm_apply, Measure.map_apply g.symm.measurable hS]

/-- Push a kernel forward by a family of measurable equivalences depending on the source. -/
def depMap (κ : Kernel α β) [IsSFiniteKernel κ] (g : α → β ≃ᵐ β')
    (_hg : Measurable fun p : α × β => g p.1 p.2) : Kernel α β' :=
  (Kernel.id ×ₖ κ).map (fun p : α × β => g p.1 p.2)

theorem depMap_apply (κ : Kernel α β) [IsSFiniteKernel κ] (g : α → β ≃ᵐ β')
    (hg : Measurable fun p : α × β => g p.1 p.2) (a : α) :
    depMap κ g hg a = (κ a).map (g a) := by
  rw [depMap, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hg measurable_prodMk_left]
  rfl

end

open MeasureTheory ProbabilityTheory Set
open HypoellipticAleksandrov
open scoped ENNReal

/-- A measurable equivalence restricts to measurable equivalences of subtypes. -/
def measurableEquivSubtype {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {p : α → Prop} {q : β → Prop} (h : ∀ x, p x ↔ q (e x)) :
    {x // p x} ≃ᵐ {y // q y} where
  toEquiv := e.toEquiv.subtypeEquiv h
  measurable_toFun := (e.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.measurable.comp measurable_subtype_coe).subtype_mk

@[simp] theorem coe_measurableEquivSubtype {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (e x)) (x : {x // p x}) :
    ((measurableEquivSubtype e h x : {y // q y}) : β) = e x := rfl

@[simp] theorem coe_measurableEquivSubtype_symm {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (e x)) (y : {y // q y}) :
    (((measurableEquivSubtype e h).symm y : {x // p x}) : α) = e.symm y := rfl

/-- Every master kernel is a finite kernel, by its sub-Markov bound. -/
instance isFiniteKernel_master {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) : IsFiniteKernel K.master :=
  ⟨1, ENNReal.one_lt_top, fun q => by simpa using K.mass_le_one q⟩

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

/-- The change of variables on raw queries `(σ, (τ, (y, z)))`. -/
def rawQuery (q : RawEvolutionQuery d) : RawEvolutionQuery d :=
  (Φ.time q.1, (Φ.time q.2.1, (Φ.position q.2.2.1, Φ.transport q.1 q.2.2.2)))

theorem continuous_rawQuery : Continuous Φ.rawQuery := by
  unfold rawQuery time position transport
  fun_prop

theorem continuous_ambientSymm :
    Continuous (fun p : ℝ × EvolutionAmbientState d => (Φ.ambientEquiv p.1).symm p.2) := by
  simp only [ambientEquiv_symm_apply]
  unfold positionInv transportInv
  fun_prop

variable {Φ} {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}

/-- The change of variables on queries, rescaled to original. -/
def queryMap (h : Φ.MapsDomain Ω γ Ω' γ') (q : EvolutionQuery Ω' γ') :
    EvolutionQuery Ω γ :=
  ⟨Φ.rawQuery q.1, Φ.time_le_iff.2 q.2.1, (h.stateSet_mem_iff q.1.1 q.1.2.2).1 q.2.2⟩

theorem measurable_queryMap (h : Φ.MapsDomain Ω γ Ω' γ') : Measurable (queryMap h) :=
  Measurable.subtype_mk (Φ.continuous_rawQuery.measurable.comp measurable_subtype_coe)

theorem measurable_outEquiv (Ω' : Set (PDE.Vec d)) (γ' : ℝ → PDE.Vec d) :
    Measurable (fun p : EvolutionQuery Ω' γ' × EvolutionAmbientState d =>
      (Φ.ambientEquiv p.1.1.2.1).symm p.2) :=
  Φ.continuous_ambientSymm.measurable.comp
    ((measurable_fst.comp (measurable_snd.comp (measurable_subtype_coe.comp
      measurable_fst))).prodMk measurable_snd)

/-- The pushed-forward master kernel. -/
def pushMaster (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ) :
    Kernel (EvolutionQuery Ω' γ') (EvolutionAmbientState d) :=
  depMap (K.master.comap (queryMap h) (measurable_queryMap h))
    (fun q => (Φ.ambientEquiv q.1.2.1).symm) (measurable_outEquiv Ω' γ')

theorem pushMaster_apply (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω' γ') :
    pushMaster h K q = (K.master (queryMap h q)).map (Φ.ambientEquiv q.1.2.1).symm := by
  rw [pushMaster, depMap_apply, Kernel.comap_apply]

/-- The pushed-forward moving-fiber kernel
`K̂.master q' = (K.master (Φ q')).map (Φ_{τ'})⁻¹`. -/
def pushKernel (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ) :
    MovingFiberKernel Ω' γ' where
  master := pushMaster h K
  terminal_support := by
    intro q
    rw [pushMaster_apply]
    have hset : (Φ.ambientEquiv q.1.2.1).symm ⁻¹' evolutionStateSet Ω' γ' q.1.2.1 =
        evolutionStateSet Ω γ (Φ.time q.1.2.1) := by
      ext x
      rw [mem_preimage, h.stateSet_mem_iff, MeasurableEquiv.apply_symm_apply]
    rw [(Φ.ambientEquiv q.1.2.1).symm.measurableEmbedding.restrict_map, hset]
    exact congrArg (Measure.map _) (K.terminal_support (queryMap h q))
  mass_le_one := by
    intro q
    rw [pushMaster_apply, Measure.map_apply (Φ.ambientEquiv q.1.2.1).symm.measurable
      MeasurableSet.univ, preimage_univ]
    exact K.mass_le_one (queryMap h q)

@[simp] theorem pushKernel_master (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ) :
    (pushKernel h K).master = pushMaster h K := rfl

/-- **Master pushforward**: `K̂.master q' = (K.master (Φ q')).map (Φ_{τ'})⁻¹`. -/
theorem pushKernel_master_apply (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω' γ') :
    (pushKernel h K).master q =
      (K.master (queryMap h q)).map (Φ.ambientEquiv q.1.2.1).symm :=
  pushMaster_apply h K q

/-- The change of variables on moving fibre states, hat to original. -/
def stateEquiv (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ) :
    EvolutionState Ω' γ' τ ≃ᵐ EvolutionState Ω γ (Φ.time τ) :=
  measurableEquivSubtype (Φ.ambientEquiv τ) (h.stateSet_mem_iff τ)

@[simp] theorem coe_stateEquiv (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ)
    (p : EvolutionState Ω' γ' τ) :
    ((stateEquiv h τ p : EvolutionState Ω γ (Φ.time τ)) : EvolutionAmbientState d) =
      Φ.ambientEquiv τ p.1 := rfl

@[simp] theorem coe_stateEquiv_symm (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ)
    (p : EvolutionState Ω γ (Φ.time τ)) :
    (((stateEquiv h τ).symm p : EvolutionState Ω' γ' τ) : EvolutionAmbientState d) =
      (Φ.ambientEquiv τ).symm p.1 := rfl

theorem queryMap_queryOfState (h : Φ.MapsDomain Ω γ Ω' γ') {τ τ' : ℝ} (hττ' : τ ≤ τ')
    (p : EvolutionState Ω' γ' τ) :
    queryMap h (evolutionQueryOfState Ω' γ' τ τ' hττ' p) =
      evolutionQueryOfState Ω γ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ')
        (stateEquiv h τ p) := rfl

/-- **Fibre pushforward**: the fixed-time fibre kernel of `K̂` is the conjugate of that of
`K` by the state equivalences. -/
theorem fiberKernel_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω') (τ τ' : ℝ) (hττ' : τ ≤ τ')
    (p : EvolutionState Ω' γ' τ) :
    (pushKernel h K).fiberKernel hΩ' τ τ' hττ' p =
      (K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ')
        (stateEquiv h τ p)).map (stateEquiv h τ').symm := by
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_evolutionStateSet (γ := γ') hΩ' τ')
  rw [← hemb.comap_map ((pushKernel h K).fiberKernel hΩ' τ τ' hττ' p),
    ← hemb.comap_map ((K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ')
      (stateEquiv h τ p)).map (stateEquiv h τ').symm)]
  congr 1
  rw [MovingFiberKernel.map_fiberKernel_eq_master, Measure.map_map measurable_subtype_coe
    (stateEquiv h τ').symm.measurable]
  have hcomp : ((↑) : EvolutionState Ω' γ' τ' → EvolutionAmbientState d) ∘
      (stateEquiv h τ').symm =
      (Φ.ambientEquiv τ').symm ∘ ((↑) : EvolutionState Ω γ (Φ.time τ') →
        EvolutionAmbientState d) := rfl
  rw [hcomp, ← Measure.map_map (Φ.ambientEquiv τ').symm.measurable measurable_subtype_coe,
    MovingFiberKernel.map_fiberKernel_eq_master, pushKernel_master_apply,
    queryMap_queryOfState]
  rfl

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling

