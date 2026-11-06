/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.LocalTower

/-!
# The countable local colimit language `L_Γ` (`localColim`) and its cocone

The hinge of the L_Γ pivot. `LocalTower.lean` builds the mutually recursive tower
`Llocal s₀ k` / `Γlocal s₀ k` and proves every *stage* countable; this file assembles the tower
into an actual colimit language and shows countability **survives to the colimit** — the object
the EM term model must be re-based over (the full `skolemColim` is uncountable, so its atom
diagram cannot fit inside the countable family the tail extraction delivers).

Mirrors the `skolemColim` layer of `SkolemColimit.lean` exactly (same `DirectedColim` quotient,
same `Quot.lift` colimit structure, same definitional stage coherence), plus what `skolemColim`
cannot have: countability of the colimit symbol types and of the colimit image `ΓlocalColim` of
the staged families.

* `localColim s₀` — the colimit language `L_Γ = colim_k (Llocal s₀ k)`.
* `LlocalInclusion s₀ k` — the cocone `Llocal s₀ k →ᴸ localColim s₀`, with symbol-level
  cocone-compatibility (`LlocalInclusion_onFunction_step`/`_onRelation_step`).
* `localColim_fun_countable` / `localColim_rel_countable` — **the payoff**: the colimit language
  is countable (via `DirectedColim.countable`, a sequential colimit of countable types).
* `localStageStructure` / `localColimStructure` / `LlocalInclusion_isExpansionOn` /
  `realize_map_LlocalInclusion` — the semantic-transport API on a fixed `s₀.Lang`-model `M`.
* `toLocalColimFormula` / `ΓlocalColim` / `ΓlocalColim_countable` — the (countable) colimit image
  of the staged families, the family the truth lemma will consume.
* Formula-level cocone coherence for the EM rebase: `LlocalInclusion_comp_LlocalHom`,
  `toLocalColimFormula_step`, `toLocalColimFormula_lift_mem_ΓlocalColim`, and
  `localSkolemWitnessFormula_mem_ΓlocalColim` (the `skolemNeed` witness body of every family
  universal lands in `ΓlocalColim`).

Next chunks (not here): the local atom/deForm seed and its countability, then the `EMContext`
re-base over `localColim`.
-/

@[expose] public section

namespace FirstOrder.Language

/-- A sequential colimit of countable types is countable: the colimit is a quotient of the
countable total space `Σ k, F k`. (Generic companion to `DirectedColim`; the reason the *local*
colimit stays countable while `skolemColim` does not.) -/
theorem DirectedColim.countable {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)}
    (h : ∀ k, Countable (F k)) : Countable (DirectedColim F φ) := by
  have : ∀ k, Countable (F k) := h
  exact inferInstanceAs (Countable (Quot _))

variable (s₀ : LocalStage)

/-! ### The colimit language `L_Γ` and the stage cocone -/

/-- The **local colimit language** `L_Γ = colim_k (Llocal s₀ k)`: function/relation symbols at
each arity are the sequential colimits of the staged symbol types along `LlocalHom`. Every
`L_Γ`-symbol lives at a finite stage; in particular every family formula's existential acquires
its local Skolem function at the next stage, so `L_Γ` is Skolem-complete *for the family*. -/
def localColim : Language.{0, 0} where
  Functions m :=
    DirectedColim (fun k => (Llocal s₀ k).Functions m)
      (fun k x => (LlocalHom s₀ k).onFunction x)
  Relations m :=
    DirectedColim (fun k => (Llocal s₀ k).Relations m)
      (fun k x => (LlocalHom s₀ k).onRelation x)

/-! ### Countability of the colimit language — the payoff of the pivot -/

/-! ### Stage structures on a fixed model and the colimit structure -/

section Structures

variable {M : Type} [s₀.Lang.Structure M] [Nonempty M]

/-- The **stage-`k` structure** on a fixed `s₀.Lang`-model `M`: stage `0` is `M`'s own structure,
and each successor stage adds the Hilbert-choice interpretation of the new *local* Skolem symbols
(`localSkolemStructure`) on top of the previous stage, via the sum structure. -/
@[implicit_reducible] noncomputable def localStageStructure :
    (k : ℕ) → (Llocal s₀ k).Structure M
  | 0 => ‹s₀.Lang.Structure M›
  | k + 1 =>
      letI := localStageStructure k
      inferInstanceAs
        (((Llocal s₀ k).sum
          (localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))).Structure M)

/-- Stage coherence (functions): a stage-`k` symbol pushed to stage `k+1` interprets the same
way. This is the cocone-compatibility witnessing the colimit interpretation is well-defined. -/
theorem localStageStructure_funMap_succ {k m : ℕ}
    (f : (Llocal s₀ k).Functions m) (x : Fin m → M) :
    @Structure.funMap (Llocal s₀ (k + 1)) M (localStageStructure s₀ (k + 1)) m
        ((LlocalHom s₀ k).onFunction f) x
      = @Structure.funMap (Llocal s₀ k) M (localStageStructure s₀ k) m f x :=
  rfl

/-- Stage coherence (relations). -/
theorem localStageStructure_relMap_succ {k m : ℕ}
    (r : (Llocal s₀ k).Relations m) (x : Fin m → M) :
    @Structure.RelMap (Llocal s₀ (k + 1)) M (localStageStructure s₀ (k + 1)) m
        ((LlocalHom s₀ k).onRelation r) x
      = @Structure.RelMap (Llocal s₀ k) M (localStageStructure s₀ k) m r x :=
  rfl

/-- The **colimit structure**: an `L_Γ`-symbol is interpreted through any stage representative,
well-defined by the (definitional) stage coherence above. -/
@[implicit_reducible] noncomputable def localColimStructure : (localColim s₀).Structure M where
  funMap {m} f x :=
    Quot.lift
      (fun p => @Structure.funMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_funMap_succ s₀ a.2 x).symm) f
  RelMap {m} r x :=
    Quot.lift
      (fun p => @Structure.RelMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_relMap_succ s₀ a.2 x).symm) r

end Structures

/-! ### The colimit image of the staged families -/

/-! ### Formula-level cocone coherence

The wrappers the EM rebase will consume, so its proofs never touch raw `mapLanguage` equalities. -/

end FirstOrder.Language
