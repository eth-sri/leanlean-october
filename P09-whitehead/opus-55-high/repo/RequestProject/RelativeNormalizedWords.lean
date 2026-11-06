import RequestProject.ExponentCorrection
import RequestProject.GenusStructuralFinsupp
import RequestProject.Tac


/-! A simultaneous labelled relative normal form.

The core relators are retained. Each extra generator is replaced by its own
pair commutator, and each extra relator is corrected using a finite product
of core relators. Correction and surface choices belong to the ambient
relator label, so restricting a stage never repeats a choice.

-/

noncomputable section
open scoped Classical commutatorElement

bwd

namespace FiniteChains

universe v
variable {A J B K : Type v} [dA : DecidableEq A] [dB : DecidableEq B]
  {ρ : J → FreeGroup A} {τ : K → FreeGroup B}

/-- Changing the equality decision procedures preserves the actual group and cell maps. -/
def PresMorFS.redecide (f : PresMorFS ρ τ) dA' dB' :
    @PresMorFS A J B K dA' dB' ρ τ where
  hom := @PresMorFS.hom A J B K dA dB ρ τ f
  cells := @PresMorFS.cells A J B K dA dB ρ τ f
  cells_add := @PresMorFS.cells_add A J B K dA dB ρ τ f
  cells_smul := @PresMorFS.cells_smul A J B K dA dB ρ τ f
  cells_cycle := by
    have hA : dA' = dA := Subsingleton.elim _ _
    have hB : dB' = dB := Subsingleton.elim _ _
    subst dA'
    subst dB'
    exact f.cells_cycle
  cells_aug := @PresMorFS.cells_aug A J B K dA dB ρ τ f

theorem FSGenerates.redecide (hf : FSGenerates f)
    dA' dB' :
    @FSGenerates A J B K dA' dB' ρ τ
      (@PresMorFS.redecide A J B K dA dB ρ τ f dA' dB') := by
  have hA : dA' = dA := Subsingleton.elim _ _
  have hB : dB' = dB := Subsingleton.elim _ _
  aesop

end FiniteChains

namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type}

/-- All positive stages use these shared ambient pairs. -/
abbrev PairGen (A Z : Type) := A ⊕ (Z × Bool)

def forgetExtra : FreeGroup (A ⊕ Z) →* FreeGroup A :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

def pairSubstitution : FreeGroup (A ⊕ Z) →* FreeGroup (PairGen A Z) :=
  FreeGroup.lift (Sum.elim (fun a => FreeGroup.of (Sum.inl a))
    (fun z => ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
      FreeGroup.of (Sum.inr (α := A) (z, true))⁆))

@[simp] theorem forgetExtra_core (a : A) :
    forgetExtra (FreeGroup.of (Sum.inl (β := Z) a)) = FreeGroup.of a := by
  rfl

@[simp] theorem forgetExtra_extra (z : Z) :
    forgetExtra (FreeGroup.of (Sum.inr (α := A) z)) = 1 := by
  rfl

@[simp] theorem pairSubstitution_core (a : A) :
    pairSubstitution (FreeGroup.of (Sum.inl (β := Z) a)) =
      FreeGroup.of (Sum.inl a) := by
  rfl

@[simp] theorem pairSubstitution_extra (z : Z) :
    pairSubstitution (FreeGroup.of (Sum.inr (α := A) z)) =
      ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
        FreeGroup.of (Sum.inr (α := A) (z, true))⁆ := by
  rfl

@[simp] theorem forgetExtra_map_core (w : FreeGroup A) :
    forgetExtra (FreeGroup.map (Sum.inl (β := Z)) w) = w := by
  have h : (forgetExtra (A := A) (Z := Z)).comp (FreeGroup.map Sum.inl) =
      MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg (· w) h

@[simp] theorem pairSubstitution_map_core (w : FreeGroup A) :
    pairSubstitution (FreeGroup.map (Sum.inl (β := Z)) w) =
      FreeGroup.map (Sum.inl (β := Z × Bool)) w := by
  have h : (pairSubstitution (A := A) (Z := Z)).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (Sum.inl (β := Z × Bool)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg (· w) h

/-- Rule 1 leaves the core exponent sums unchanged and annihilates every
extra exponent sum. -/
theorem pairSubstitution_exp_core (w : FreeGroup (A ⊕ Z)) a :
    expSum (Sum.inl a) (pairSubstitution w) = expSum a (forgetExtra w) := by
  have h : (expSum (Sum.inl (β := Z × Bool) a)).comp pairSubstitution =
      (expSum a).comp forgetExtra := by
    aesop
  exact congrArg (· w) h

theorem pairSubstitution_exp_pair (w : FreeGroup (A ⊕ Z)) z :
    expSum (Sum.inr z) (pairSubstitution w) = 1 := by
  have h : (expSum (Sum.inr (α := A) z)).comp pairSubstitution =
      (1) := by
    apply FreeGroup.ext_hom
    intro x
    cases x with
    | inl x => rfl
    | inr x =>
        simp [MonoidHom.comp_apply, pairSubstitution_extra,
          MonoidHom.one_apply, map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  exact congrArg (· w) h

variable (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

/-- The correction is a finite core chain, chosen once for its ambient word. -/
def correctionCoefficients (w : FreeGroup (A ⊕ Z)) :=
  Classical.choose (exists_correction core (forgetExtra w) hcore)

theorem correctionCoefficients_spec (w : FreeGroup (A ⊕ Z)) :
    expVec (forgetExtra w * correctionWord core (correctionCoefficients core hcore w)) = 0 :=
  Classical.choose_spec (exists_correction core _ hcore)

/-- Rule 2 is a product with actual retained core relators. -/
def correctedWord (w : FreeGroup (A ⊕ Z)) :=
  w * FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

/-- The result of simultaneous rules 1 and 2, before genus replacement. -/
def normalizedWord (w : FreeGroup (A ⊕ Z)) :=
  pairSubstitution (correctedWord core hcore w)

theorem normalizedWord_eq (w : FreeGroup (A ⊕ Z)) :
    normalizedWord core hcore w = pairSubstitution w *
      FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w)) := by
  simp [normalizedWord, correctedWord, map_mul, pairSubstitution_map_core]

theorem normalizedWord_exp_zero w (i : PairGen A Z) :
    Multiplicative.toAdd (expSum i (normalizedWord core hcore w)) = 0 := by
  cases i with
  | inl a =>
      rw [normalizedWord, pairSubstitution_exp_core]
      have h := congrArg (· a) (correctionCoefficients_spec core hcore w)
      simp_all [expVec_apply, correctedWord, map_mul, forgetExtra_map_core, Finsupp.zero_apply]
  | inr z =>
      rw [normalizedWord, pairSubstitution_exp_pair]
      rfl

/-- Surface data is constructed from the normalized word; it is not a
hypothesis on the relative presentation. -/
structure SurfaceChoice (w : FreeGroup (PairGen A Z)) where
  genus : ℕ
  genus_ge_two : 2 ≤ genus
  loops : Fin genus × Bool → FreeGroup (PairGen A Z)
  word : w = commWord loops (finitePairs genus)

theorem surfaceChoice_exists (w : FreeGroup (A ⊕ Z)) :
    Nonempty (SurfaceChoice (normalizedWord core hcore w)) := by
  obtain ⟨q, a, b, hq, hword⟩ := exists_commutator_factorization
    _ (normalizedWord_exp_zero core hcore w)
  refine ⟨⟨q, hq, (fun x => if x.2 then b x.1 else a x.1), ?_⟩⟩
  rw [hword]
  simp [commWord, finitePairs, List.map_map, List.ofFn_eq_map,
    commutatorElement_def]
  rfl

def surfaceChoice (w : FreeGroup (A ⊕ Z)) :=
  Classical.choice (surfaceChoice_exists core hcore w)

variable (extra : S → FreeGroup (A ⊕ Z))

def normalizedGenus (s : S) := (surfaceChoice core hcore (extra s)).genus

instance normalizedGenus_neZero s : NeZero (normalizedGenus core hcore extra s) :=
  ⟨by have h := (surfaceChoice core hcore (extra s)).genus_ge_two
      change (surfaceChoice core hcore _).genus ≠ 0
      omega⟩

def normalizedLoops s :
    Fin (normalizedGenus core hcore extra s) × Bool → FreeGroup (PairGen A Z) :=
  (surfaceChoice core hcore _).loops

def beforeCorrection : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => pairSubstitution (extra s))

def normalizedPresentation : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => normalizedWord core hcore (extra s))

theorem normalizedPresentation_surface s :
    normalizedPresentation core hcore extra (Sum.inr s) =
      commWord (normalizedLoops core hcore extra s)
        (finitePairs (normalizedGenus core hcore extra s)) :=
  (surfaceChoice core hcore _).word

/-- Every correction belongs to the normal subgroup of retained core
relators, for arbitrary cardinalities of the core and the extra family. -/
theorem coreCorrection_mem (N : Subgroup (FreeGroup (PairGen A Z)))
    (hN : ∀ c, FreeGroup.map (Sum.inl (β := Z × Bool)) (core c) ∈ N)
    v :
    FreeGroup.map (Sum.inl (β := Z × Bool)) (correctionWord core v) ∈ N := by
  rw [correctionWord, map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ ?_
  aesop

/-- Simultaneous rule 2 does not change the presented group. No ordering
or enumeration of the entire (possibly infinite) extra family is used. -/
theorem relSub_normalizedPresentation :
    relSub (normalizedPresentation core hcore extra) =
      relSub (beforeCorrection core extra) := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · change normalizedWord core hcore (extra s) ∈ _
      rw [normalizedWord_eq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩)
        (coreCorrection_mem core (relSub (beforeCorrection core extra)) (fun c =>
          Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩) _)
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · have hw : normalizedWord core hcore (extra s) ∈
          relSub (normalizedPresentation core hcore extra) :=
          Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩
      have hc := coreCorrection_mem core
        (relSub (normalizedPresentation core hcore extra))
        (fun c => Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩)
        (correctionCoefficients core hcore (extra s))
      rw [normalizedWord_eq] at hw
      exact (Subgroup.mul_mem_cancel_right _ hc).mp hw

/-- The final actual genus replacement of the normalized relative presentation. -/
def blockPresentation :=
  substPresF (normalizedPresentation core hcore extra)
    (familyFiniteSpineWordBlock _
      (normalizedLoops core hcore extra))

/-- The input word equality for the actual B1/B2 construction has been
derived from acyclicity of the core, not assumed of the extra relators. -/
def blockStructuralMap : PresMorFS (normalizedPresentation core hcore extra)
    (blockPresentation core hcore extra) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s, SpinePresentationGen
      (normalizedGenus core hcore extra s))) := inferInstance
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s, SpinePresentationGen
      (normalizedGenus core hcore extra s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap _
    _ _
    (normalizedPresentation_surface core hcore extra)) dSrc dTgt
