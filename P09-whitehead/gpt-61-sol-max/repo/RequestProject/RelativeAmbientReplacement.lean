import Mathlib.Tactic

import RequestProject.RelativeSlideNaturality
import RequestProject.RelativeTerminalOperation
import RequestProject.PresentationInclusionCalculus

/-! One simultaneous replacement, returned in the same ambient-label
format as its input. The core labels are fixed. Earlier stages select
whole genus blocks and the new terminal stage adds the pair caps.
All algebraic chain assertions retain finite support. Unverified source. -/

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def NextExtraGen := (Z × Bool) ⊕
  (Σ s, SpinePresentationGen (normalizedGenus core hcore extra s))

instance nextExtraGenDecidableEq : DecidableEq (NextExtraGen core hcore extra) :=
  Classical.decEq _

instance nextExtraGenFinite [Finite Z] [Finite S] : Finite (NextExtraGen core hcore extra) := by
  unfold NextExtraGen
  infer_instance

abbrev NextExtraCell :=
  (Σ s, NamedSpineRel (normalizedGenus core hcore extra s)) ⊕ (Z × Bool)

def flattenBlockGen :
    (PairGen A Z ⊕ (Σ s, SpinePresentationGen (normalizedGenus core hcore extra s))) ≃
      (A ⊕ NextExtraGen core hcore extra) := Equiv.sumAssoc _ _ _

def nextExtra : NextExtraCell core hcore extra → FreeGroup (A ⊕ NextExtraGen core hcore extra)
  | Sum.inl m => FreeGroup.map (flattenBlockGen core hcore extra)
      (blockPresentation core hcore extra (Sum.inr m))
  | Sum.inr k => FreeGroup.of (Sum.inr (Sum.inl k))

variable (p : S → Prop)
def nextPredicate  : NextExtraCell core hcore extra → Prop
  | Sum.inl m => p m.1
  | Sum.inr _ => False

theorem nextPredicate_mono {p t : S → Prop} (h : ∀ s, p s → t s) :
    ∀ s, nextPredicate core hcore extra p s → nextPredicate core hcore extra t s := by
  aesop

def stageNextGen  :
    (PairGen A Z ⊕ (Σ s : {s // p s}, SpinePresentationGen
      (restrictedGenus core hcore extra p s))) → A ⊕ NextExtraGen core hcore extra
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr z) => Sum.inr (Sum.inl z)
  | Sum.inr s => Sum.inr (Sum.inr ⟨s.1.val, s.2⟩)

theorem stageNextGen_injective  :
    Function.Injective (stageNextGen core hcore extra p) := by
  rintro (a | ⟨s, x⟩) (b | ⟨t, y⟩) h
  · cases a <;> cases b <;> simp_all [stageNextGen, NextExtraGen]
  · cases a <;> simp [stageNextGen] at h <;> cases h
  · cases b <;> simp [stageNextGen] at h <;> cases h
  · have hh  := Sum.inr.inj (Sum.inr.inj h)
    have hs : s = t := Subtype.ext (congrArg Sigma.fst hh)
    subst t
    have hx : x = y := eq_of_heq (Sigma.mk.inj hh).2
    subst y
    rfl

def stageNextCell  :
    (C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) ≃
      (C ⊕ {s // nextPredicate core hcore extra p s}) where
  toFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨s, m⟩ => Sum.inr ⟨Sum.inl ⟨s.val, m⟩, s.property⟩
  invFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨Sum.inl ⟨s, m⟩, hs⟩ => Sum.inr ⟨⟨s, hs⟩, m⟩
    | Sum.inr ⟨Sum.inr _, hs⟩ => hs.elim
  left_inv := by rintro (c | ⟨⟨s, hs⟩, m⟩) <;> rfl
  right_inv := by
    rintro (c | ⟨⟨s, m⟩ | k, hs⟩)
    · rfl
    · rfl
    · exact hs.elim

def nextStage  :=
  rawPresentation core (restrictedExtra (nextExtra core hcore extra)
    (nextPredicate core hcore extra p))

theorem stageNext_rel 
    (j : C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) :
    nextStage core hcore extra p (stageNextCell core hcore extra p j) =
      FreeGroup.map (stageNextGen core hcore extra p)
        (restrictedBlockPresentation core hcore extra p j) := by
  cases j with
  | inl c =>
      
      have hm : ((FreeGroup.map (stageNextGen core hcore extra p)).comp
          (FreeGroup.map Sum.inl)).comp (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro a
        rfl
      exact (DFunLike.congr_fun hm (core c)).symm
  | inr m =>
      have hm : (FreeGroup.map (stageNextGen core hcore extra p)).comp
          (FreeGroup.map (genEmb (α := PairGen A Z)
            (Zt := fun s => SpinePresentationGen (restrictedGenus core hcore extra p s)) m.1)) =
        (FreeGroup.map (flattenBlockGen core hcore extra)).comp
          (FreeGroup.map (genEmb (α := PairGen A Z)
            (Zt := fun s => SpinePresentationGen (normalizedGenus core hcore extra s)) m.1.val)) := by
        apply FreeGroup.ext_hom
        intro x
        cases x with
        | inl x => cases x <;> rfl
        | inr x => rfl
      exact (DFunLike.congr_fun hm
        (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
          (restrictedLoops core hcore extra p) m.1 m.2)).symm

def stageNextMap   :=
  PresInclusionFS.mor _ _ (stageNextGen core hcore extra p) (stageNextCell core hcore extra p)
    (stageNextGen_injective core hcore extra p) (stageNextCell core hcore extra p).injective
    (stageNext_rel core hcore extra p)

abbrev stageNextMap_generates   :=
  PresInclusionFS.paddingRelabel_generates _ _ (stageNextGen core hcore extra p)
    (stageNextGen_injective core hcore extra p) (stageNextCell core hcore extra p)
    (stageNext_rel core hcore extra p)

abbrev nextStage_cockcroft 
    (hp : FSIsCockcroft (rawPresentation core (restrictedExtra extra p)))  :=
  FiniteChains.fsIsCockcroft_of_generates (FiniteChains.RelativeNormalForm.stageNextMap core hcore extra p)
    (FiniteChains.RelativeNormalForm.stageNextMap_generates core hcore extra p)
    (FiniteChains.fsIsCockcroft_of_generates (FiniteChains.RelativeNormalForm.restrictedStructuralMap core hcore extra p)
      (FiniteChains.RelativeNormalForm.restrictedStructuralMap_generates core hcore extra p)
      (FiniteChains.RelativeNormalForm.normalizedPresentation_cockcroft core hcore
        (FiniteChains.RelativeNormalForm.restrictedExtra extra p) hp))

variable {p t : S → Prop} (hpt : ∀ s, p s → t s)

theorem nextStage_square
    (x : (C ⊕ (Σ s : {s // p s}, NamedSpineRel
      (restrictedGenus core hcore extra p s))) →₀
        MonoidAlgebra ℤ (PresGroup (restrictedBlockPresentation core hcore extra p))) :
    (rawInclusion core (nextExtra core hcore extra)
      (nextPredicate_mono core hcore extra hpt)).cells ((stageNextMap core hcore extra p).cells x) =
    (stageNextMap core hcore extra t).cells ((blockInclusion core hcore extra hpt).cells x) := by
  apply PresInclusionFS.square_cells
  · rintro ((a | z) | s) <;> rfl
  · rintro (c | s) <;> rfl

theorem nextStage_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (nextStage core hcore extra p) x) :
    (rawInclusion core (nextExtra core hcore extra)
      (nextPredicate_mono core hcore extra hpt)).cells x = 0 := by
  apply fsCells_eq_zero_of_generates (stageNextMap core hcore extra p)
    (stageNextMap core hcore extra t) (blockInclusion core hcore extra hpt)
    (rawInclusion core (nextExtra core hcore extra) (nextPredicate_mono core hcore extra hpt))
    (nextStage_square core hcore extra hpt) ?_ (stageNextMap_generates core hcore extra p) hx
  intro y hy
  exact relativeReplacement_preserves_zero core hcore extra hpt hzero hy

theorem nextStage_strict (s : S) (hs : t s) (hsp : ¬ p s) :
    ∃ m, nextPredicate core hcore extra t m ∧ ¬ nextPredicate core hcore extra p m := by
  have hq := (surfaceChoice core hcore (extra s)).genus_ge_two
  let m : NamedSpineRel (normalizedGenus core hcore extra s) :=
    Sum.inr (⟨0, by change 0 < (surfaceChoice core hcore (extra s)).genus; omega⟩, false)
  exact ⟨Sum.inl ⟨s, m⟩, hs, hsp⟩

end FiniteChains.RelativeNormalForm
