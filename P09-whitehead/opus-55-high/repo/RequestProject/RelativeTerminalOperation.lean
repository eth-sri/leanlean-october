import RequestProject.RelativeStructuralOperation
import RequestProject.GenusTerminalSpineFinsupp


/-! The actual fixed-core T/Q terminal step. Original extra words need not
already be products of commutators: normalization supplies them. No assumed
terminal Cockcroftness, generation, or pi1-killing conclusion remains.
Unverified proof source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm
open Davis.Genus

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

/-- The original relative group maps to its actual normalized group by
the prescribed pair substitution. -/
def rawToNormalizedGroup : PresGroup (rawPresentation core extra) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [relSub_normalizedPresentation]
    cases j with
    | inl c =>
        change pairSubstitution (FreeGroup.map Sum.inl (core c)) ∈ _
        rw [pairSubstitution_map_core]
        exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    | inr s => exact Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩)

theorem normalized_core_trivial
    (htriv : ∀ a,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    a :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (normalizedPresentation core hcore extra)) = 1 := by
  have h := congrArg (rawToNormalizedGroup core hcore extra) (htriv a)
  tauto

def terminalPresentation :=
  addRels (blockPresentation core hcore extra)
    (terminalSpineCaps (A := A) (K := Z × Bool) _)

def relativeTerminalMap : PresMorFS (blockPresentation core hcore extra)
    (terminalPresentation core hcore extra) :=
  actualTerminalSpineMorFS _
    _ _

/-- A genuine fixed-core terminal step for an arbitrary relative source.
The source need only be Cockcroft with trivial core image. -/
theorem relativeTerminal_conclusions
    (hcoreInjective : Function.Injective (expMatrix core))
    (hP : FSIsCockcroft (rawPresentation core extra))
    (htriv : ∀ a,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    FSIsCockcroft (terminalPresentation core hcore extra) ∧
      (∀ v, FSIsFoxCycle (blockPresentation core hcore extra) v →
        (relativeTerminalMap core hcore extra).cells v = 0) :=
  actualTerminalSpineFS_conclusions core _
    _ _
    (normalizedPresentation_surface core hcore extra) (by aesop)
    hcoreInjective (normalizedPresentation_cockcroft core hcore extra hP)
    (normalized_core_trivial core hcore extra htriv)
