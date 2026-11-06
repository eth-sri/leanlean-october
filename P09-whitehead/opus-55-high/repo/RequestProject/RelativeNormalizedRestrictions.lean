import RequestProject.RelativeNormalizedWords


/-! Restrictions of the single ambient normalization. No correction or
commutator factorization is re-chosen when a stage is restricted.
The actual genus relators respect the resulting labelled inclusions.

-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def restrictedPresentation (p : S → Prop) : C ⊕ {s // p s} → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => normalizedWord core hcore (extra s.val))

def restrictedGenus (p : S → Prop) (s : {s // p s}) :=
  normalizedGenus core hcore extra s.val

instance restrictedGenus_neZero p s :
    NeZero (restrictedGenus core hcore extra p s) :=
  normalizedGenus_neZero core hcore extra s.val

def restrictedLoops p s :
    Fin (restrictedGenus core hcore extra p s) × Bool → FreeGroup (PairGen A Z) :=
  normalizedLoops core hcore extra s.val

theorem restrictedPresentation_surface p s :
    restrictedPresentation core hcore extra p (Sum.inr s) =
      commWord (restrictedLoops core hcore extra p s)
        (finitePairs (restrictedGenus core hcore extra p s)) :=
  normalizedPresentation_surface core hcore extra s.val

def restrictedBlockPresentation p :=
  substPresF (restrictedPresentation core hcore extra p)
    (familyFiniteSpineWordBlock _
      (restrictedLoops core hcore extra p))

def restrictedStructuralMap p :
    PresMorFS (restrictedPresentation core hcore extra p)
      (restrictedBlockPresentation core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap _
    _ _
    (restrictedPresentation_surface core hcore extra p)) dSrc dTgt

theorem restrictedStructuralMap_generates p :
    FSGenerates (restrictedStructuralMap core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @FSGenerates.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _ _
    (finiteSpineFamilyStructuralMap_generates _
    _ _
    _) dSrc dTgt

variable {p t : S → Prop} (hpt : ∀ s, p s → t s)

def labelIncl (s : {s // p s}) : {s // t s} := ⟨s.val, hpt s.val s.property⟩

theorem labelIncl_injective : Function.Injective (labelIncl hpt) := by
  intro s s' h
  exact Subtype.ext (congrArg (·.val) h)

def oldCellIncl : C ⊕ {s // p s} → C ⊕ {s // t s} := Sum.map id (labelIncl hpt)

theorem oldCellIncl_injective : Function.Injective (oldCellIncl (C := C) hpt) :=
  Function.Injective.sumMap Function.injective_id (labelIncl_injective hpt)

def blockGenIncl :
    (PairGen A Z ⊕ (Σ s : {s // p s}, SpinePresentationGen (restrictedGenus core hcore extra p s))) →
    (PairGen A Z ⊕ (Σ s : {s // t s}, SpinePresentationGen (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun z => ⟨labelIncl hpt z.1, z.2⟩)

def blockCellIncl :
    (C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) →
    (C ⊕ (Σ s : {s // t s}, NamedSpineRel (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun m => ⟨labelIncl hpt m.1, m.2⟩)

theorem sigma_labelIncl_injective {F : S → Type}
    : Function.Injective (fun z : Σ s, F s.val =>
        (⟨labelIncl hpt z.1, z.2⟩ : Σ s, F s.val)) := by
  rintro ⟨s, x⟩ ⟨s', x'⟩ h
  have hs := labelIncl_injective hpt (congrArg Sigma.fst h)
  grind

theorem blockGenIncl_injective :
    Function.Injective (blockGenIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => SpinePresentationGen
      (normalizedGenus core hcore extra s)) hpt)

theorem blockCellIncl_injective :
    Function.Injective (blockCellIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => NamedSpineRel
      (normalizedGenus core hcore extra s)) hpt)

/-- Literal compatibility of the corrected relators, with the core fixed. -/
theorem restrictedPresentation_incl c :
    restrictedPresentation core hcore extra t (oldCellIncl hpt c) =
      restrictedPresentation core hcore extra p c := by
  aesop

theorem blockGenIncl_genEmb s :
    (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
      (FreeGroup.map (genEmb (α := PairGen A Z)
        (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra p r)) s)) =
    FreeGroup.map (genEmb (α := PairGen A Z)
      (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra t r))
      (labelIncl hpt s)) := by
  aesop

/-- Actual genus relators, not an abstract presentation assignment, respect
the same ambient-label inclusion. -/
theorem restrictedBlockPresentation_incl
    m :
    restrictedBlockPresentation core hcore extra t (blockCellIncl core hcore extra hpt m) =
      FreeGroup.map (blockGenIncl core hcore extra hpt)
        (restrictedBlockPresentation core hcore extra p m) := by
  cases m with
  | inl c =>
      have h : (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
          (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        aesop
      exact (congrArg (· (FreeGroup.map Sum.inl (core c))) h).symm
  | inr m =>
      exact (congrArg (fun f => f
        (familyFiniteSpineWordBlock _
          (restrictedLoops core hcore extra p) m.1 m.2))
        (blockGenIncl_genEmb core hcore extra hpt m.1)).symm
