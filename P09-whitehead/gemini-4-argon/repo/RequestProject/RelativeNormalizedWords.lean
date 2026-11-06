module

public import RequestProject.ExponentCorrection
public import RequestProject.GenusStructuralFinsupp

@[expose] public section

noncomputable section
open scoped Classical commutatorElement

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

universe v
variable {A J B K : Type v} [dA : DecidableEq A] [dB : DecidableEq B]
  {ρ : J → FreeGroup A} {τ : K → FreeGroup B}

def PresMorFS.redecide (f : PresMorFS ρ τ) (dA' : DecidableEq A) (dB' : DecidableEq B) :
    @PresMorFS A J B K dA' dB' ρ τ where
  hom := @PresMorFS.hom A J B K dA dB ρ τ f
  cells := @PresMorFS.cells A J B K dA dB ρ τ f
  cells_add := @PresMorFS.cells_add A J B K dA dB ρ τ f
  cells_smul := @PresMorFS.cells_smul A J B K dA dB ρ τ f
  cells_cycle := by cases Subsingleton.elim dA' dA; cases Subsingleton.elim dB' dB; exact f.cells_cycle
  cells_aug := @PresMorFS.cells_aug A J B K dA dB ρ τ f

theorem FSGenerates.redecide {f : PresMorFS ρ τ} (hf : FSGenerates f)
    (dA' : DecidableEq A) (dB' : DecidableEq B) :
    @FSGenerates A J B K dA' dB' ρ τ
      (@PresMorFS.redecide A J B K dA dB ρ τ f dA' dB') := by
  cases Subsingleton.elim dA' dA; cases Subsingleton.elim dB' dB; exact hf

end FiniteChains

namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type}

abbrev PairGen (A Z : Type) := A ⊕ (Z × Bool)

def forgetExtra : FreeGroup (A ⊕ Z) →* FreeGroup A :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

def pairSubstitution : FreeGroup (A ⊕ Z) →* FreeGroup (PairGen A Z) :=
  FreeGroup.lift (Sum.elim (fun a => FreeGroup.of (Sum.inl a))
    (fun z => ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
      FreeGroup.of (Sum.inr (α := A) (z, true))⁆))

@[simp] theorem pairSubstitution_core (a : A) :
    pairSubstitution (FreeGroup.of (Sum.inl (β := Z) a)) = FreeGroup.of (Sum.inl a) := by
  simp [pairSubstitution]

@[simp] theorem pairSubstitution_extra (z : Z) :
    pairSubstitution (FreeGroup.of (Sum.inr (α := A) z)) =
      ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
        FreeGroup.of (Sum.inr (α := A) (z, true))⁆ := by
  simp [pairSubstitution]

@[simp] theorem pairSubstitution_map_core (w : FreeGroup A) :
    pairSubstitution (FreeGroup.map (Sum.inl (β := Z)) w) =
      FreeGroup.map (Sum.inl (β := Z × Bool)) w :=
  DFunLike.congr_fun
    (FreeGroup.ext_hom ((pairSubstitution (A := A) (Z := Z)).comp (FreeGroup.map Sum.inl))
      (FreeGroup.map (Sum.inl (β := Z × Bool))) (by intro a; simp)) w

theorem pairSubstitution_exp_pair (w : FreeGroup (A ⊕ Z)) (z : Z × Bool) :
    expSum (Sum.inr z) (pairSubstitution w) = 1 :=
  DFunLike.congr_fun
    (FreeGroup.ext_hom ((expSum (Sum.inr (α := A) z)).comp pairSubstitution)
      (1 : FreeGroup (A ⊕ Z) →* Multiplicative ℤ) (by
        rintro (x | x)
        · simp [expSum]
        · simp only [MonoidHom.comp_apply, pairSubstitution_extra, MonoidHom.one_apply, map_commutatorElement]
          exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _))) w

variable (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

def correctionCoefficients (w : FreeGroup (A ⊕ Z)) : C →₀ ℤ :=
  Classical.choose (exists_correction core (forgetExtra w) hcore)

def correctedWord (w : FreeGroup (A ⊕ Z)) : FreeGroup (A ⊕ Z) :=
  w * FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

def normalizedWord (w : FreeGroup (A ⊕ Z)) : FreeGroup (PairGen A Z) :=
  pairSubstitution (correctedWord core hcore w)

theorem normalizedWord_eq (w : FreeGroup (A ⊕ Z)) :
    normalizedWord core hcore w = pairSubstitution w *
      FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w)) := by
  simp only [normalizedWord, correctedWord, map_mul, pairSubstitution_map_core]

structure SurfaceChoice (w : FreeGroup (PairGen A Z)) where
  genus : ℕ
  genus_ge_two : 2 ≤ genus
  loops : Fin genus × Bool → FreeGroup (PairGen A Z)
  word : w = commWord loops (finitePairs genus)

def surfaceChoice (w : FreeGroup (A ⊕ Z)) : SurfaceChoice (normalizedWord core hcore w) :=
  Classical.choice <| by
    have hexp (i : PairGen A Z) : Multiplicative.toAdd (expSum i (normalizedWord core hcore w)) = 0 := by
      rcases i with a | z
      · have hcore_exp : expSum (Sum.inl a) (normalizedWord core hcore w) =
            expSum a (forgetExtra (correctedWord core hcore w)) :=
          DFunLike.congr_fun
            (FreeGroup.ext_hom ((expSum (Sum.inl (β := Z × Bool) a)).comp pairSubstitution)
              ((expSum a).comp forgetExtra) (by
                rintro (x | z)
                · simp [expSum, forgetExtra]
                · simp only [MonoidHom.comp_apply, pairSubstitution_extra, forgetExtra,
                    FreeGroup.lift_apply_of, Sum.elim_inr, map_one, map_commutatorElement]
                  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)))
            (correctedWord core hcore w)
        rw [hcore_exp]
        have hfmap (u : FreeGroup A) : forgetExtra (FreeGroup.map (Sum.inl (β := Z)) u) = u :=
          DFunLike.congr_fun
            (FreeGroup.ext_hom ((forgetExtra (A := A) (Z := Z)).comp (FreeGroup.map Sum.inl))
              (MonoidHom.id _) (by intro a; simp [forgetExtra])) u
        simpa only [expVec_apply, correctedWord, correctionCoefficients, map_mul, hfmap, Finsupp.zero_apply] using
          congrArg (fun v : A →₀ ℤ => v a) (Classical.choose_spec (exists_correction core (forgetExtra w) hcore))
      · rw [normalizedWord, pairSubstitution_exp_pair]; rfl
    obtain ⟨q, a, b, hq, hword⟩ := exists_commutator_factorization (normalizedWord core hcore w) hexp
    refine ⟨⟨q, hq, fun x => if x.2 then b x.1 else a x.1, ?_⟩⟩
    rw [hword]; simp only [commWord, finitePairs, List.map_map, List.ofFn_eq_map, commutatorElement_def]; rfl

variable (extra : S → FreeGroup (A ⊕ Z))

def normalizedGenus (s : S) : ℕ := (surfaceChoice core hcore (extra s)).genus

instance normalizedGenus_neZero (s : S) : NeZero (normalizedGenus core hcore extra s) :=
  ⟨by have := (surfaceChoice core hcore (extra s)).genus_ge_two
      change (surfaceChoice core hcore (extra s)).genus ≠ 0; omega⟩

def normalizedLoops (s : S) :
    Fin (normalizedGenus core hcore extra s) × Bool → FreeGroup (PairGen A Z) :=
  (surfaceChoice core hcore (extra s)).loops

def beforeCorrection : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c)) (fun s => pairSubstitution (extra s))

def normalizedPresentation : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c)) (fun s => normalizedWord core hcore (extra s))

theorem normalizedPresentation_surface (s : S) :
    normalizedPresentation core hcore extra (Sum.inr s) =
      commWord (normalizedLoops core hcore extra s)
        (finitePairs (normalizedGenus core hcore extra s)) :=
  (surfaceChoice core hcore (extra s)).word

theorem coreCorrection_mem (N : Subgroup (FreeGroup (PairGen A Z)))
    (hN : ∀ c, FreeGroup.map (Sum.inl (β := Z × Bool)) (core c) ∈ N) (v : C →₀ ℤ) :
    FreeGroup.map (Sum.inl (β := Z × Bool)) (correctionWord core v) ∈ N := by
  rw [correctionWord, map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp_apply, map_zpow]
  exact N.zpow_mem (hN c) (v c)

theorem relSub_normalizedPresentation :
    relSub (normalizedPresentation core hcore extra) =
      relSub (beforeCorrection core extra) := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · change normalizedWord core hcore (extra s) ∈ _
      rw [normalizedWord_eq]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩)
        (coreCorrection_mem core (relSub (beforeCorrection core extra))
          (fun c => Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩) _)
  · rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · have hw : normalizedWord core hcore (extra s) ∈ relSub (normalizedPresentation core hcore extra) :=
        Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩
      rw [normalizedWord_eq] at hw
      exact (Subgroup.mul_mem_cancel_right _
        (coreCorrection_mem core (relSub (normalizedPresentation core hcore extra))
          (fun c => Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩) _)).mp hw

def blockPresentation :
    C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s)) →
      FreeGroup (PairGen A Z ⊕ (Σ s, SpinePresentationGen
        (normalizedGenus core hcore extra s))) :=
  substPresF (normalizedPresentation core hcore extra)
    (familyFiniteSpineWordBlock (normalizedGenus core hcore extra)
      (normalizedLoops core hcore extra))

def blockStructuralMap : PresMorFS (normalizedPresentation core hcore extra)
    (blockPresentation core hcore extra) :=
  @PresMorFS.redecide _ _ _ _ (Classical.decEq _)
    (@instDecidableEqSum _ _ (Classical.decEq _) inferInstance) _ _
    (finiteSpineFamilyStructuralMap (normalizedPresentation core hcore extra)
      (normalizedGenus core hcore extra) (normalizedLoops core hcore extra)
      (normalizedPresentation_surface core hcore extra)) inferInstance inferInstance
