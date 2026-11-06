module

public import RequestProject.RelativeAmbientTerminal

@[expose] public section

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C : Type} (core : C → FreeGroup A)

def stageCellEquivFull {S : Type} (p : S → Prop) (hall : ∀ s, p s) :
    (C ⊕ {s // p s}) ≃ (C ⊕ S) where
  toFun := Sum.map id Subtype.val
  invFun := Sum.map id (fun s => ⟨s, hall s⟩)
  left_inv := by rintro (c | ⟨s, hs⟩) <;> rfl
  right_inv := by rintro (c | s) <;> rfl

def fullIntoStage {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) :
    PresMorFS (rawPresentation core extra) (rawPresentation core (restrictedExtra extra p)) :=
  PresInclusionFS.mor _ _ id (stageCellEquivFull (C := C) p hall).symm
    Function.injective_id (stageCellEquivFull (C := C) p hall).symm.injective
    (by rintro (j | j) <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem fullIntoStage_generates {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) : FSGenerates (fullIntoStage core extra p hall) :=
  PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
    (stageCellEquivFull (C := C) p hall).symm
    (by rintro (j | j) <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem rawInclusion_factor_full {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    {p t : S → Prop} (hpt : ∀ s, p s → t s) (hall : ∀ s, t s)
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (rawInclusion core extra hpt).cells x =
      (fullIntoStage core extra t hall).cells ((stageIntoFull core extra p).cells x) := by
  have hg : (rawInclusion core extra hpt).hom =
      (fullIntoStage core extra t hall).hom.comp (stageIntoFull core extra p).hom := by
    apply MonoidHom.ext; intro z
    induction z using QuotientGroup.induction_on with
    | H w => change QuotientGroup.mk (FreeGroup.map id w) =
        QuotientGroup.mk (FreeGroup.map id (FreeGroup.map id w)); simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add, hx, hy]
  | single j a =>
      change PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a) =
        PresInclusionFS.cells _ _ _ _ _ (PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a))
      rw [PresInclusionFS.cells_single, PresInclusionFS.cells_single, PresInclusionFS.cells_single,
        show oldCellIncl hpt j = (stageCellEquivFull (C := C) t hall).symm
          (Sum.map id Subtype.val j) by cases j <;> rfl]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a =
        MonoidAlgebra.mapDomainRingHom ℤ (fullIntoStage core extra t hall).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (stageIntoFull core extra p).hom a)
      rw [BlockMor.mapDomainRingHom_comp', ← hg]

structure AmbientChain (n : ℕ) where
  extraGen : Type
  extraCell : Type
  fresh : extraGen
  rel : extraCell → FreeGroup (A ⊕ extraGen)
  stage : ℕ → extraCell → Prop
  saturated : ∀ i, n ≤ i → ∀ s, stage i s
  mono : ∀ i s, stage i s → stage (i + 1) s
  strict : ∀ i, i < n → ∃ s, stage (i + 1) s ∧ ¬ stage i s
  cockcroft : ∀ i, FSIsCockcroft (rawPresentation core (restrictedExtra rel (stage i)))
  core_trivial : ∀ i a,
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (restrictedExtra rel (stage i)))) = 1
  zero : ∀ i, i < n → ∀ x,
    FSIsFoxCycle (rawPresentation core (restrictedExtra rel (stage i))) x →
      (rawInclusion core rel (mono i)).cells x = 0

namespace AmbientChain
variable {core} {n : ℕ} (c : AmbientChain core n)

theorem full_cockcroft : FSIsCockcroft (rawPresentation core c.rel) :=
  fsIsCockcroft_of_generates (stageIntoFull core c.rel (c.stage n))
    (PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
      (stageCellEquivFull (C := C) (c.stage n) (c.saturated n le_rfl))
      (by rintro (j | j) <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull]))
    (c.cockcroft n)

theorem full_core_trivial (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core c.rel)) = 1 := by
  have h := congrArg (stageIntoFull core c.rel (c.stage n)).hom (c.core_trivial n a)
  change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
    (stageIntoFull core c.rel (c.stage n)).hom 1 at h
  simpa only [FreeGroup.map.id, map_one] using h

def initial {Z S : Type} (z : Z) (extra : S → FreeGroup (A ⊕ Z))
    (hc : FSIsCockcroft (rawPresentation core extra))
    (ht : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    AmbientChain core 0 where
  extraGen := Z
  extraCell := S
  fresh := z
  rel := extra
  stage _ _ := True
  saturated _ _ _ := trivial
  mono _ _ _ := trivial
  strict _ hi := by omega
  cockcroft _ := fsIsCockcroft_of_generates (fullIntoStage core extra _ (fun _ => trivial))
    (fullIntoStage_generates core extra _ (fun _ => trivial)) hc
  core_trivial _ a := by
    have h := congrArg (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom (ht a)
    change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
      (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom 1 at h
    simpa only [FreeGroup.map.id, map_one] using h
  zero _ hi := by omega

variable (hcore : Function.Surjective (expMatrix core))

def stepStage (i : ℕ) : NextExtraCell core hcore c.rel → Prop :=
  if i ≤ n then nextPredicate core hcore c.rel (c.stage i) else fun _ => True

theorem stepStage_mono (i : ℕ) (s : NextExtraCell core hcore c.rel)
    (hs : c.stepStage hcore i s) : c.stepStage hcore (i + 1) s := by
  by_cases hi : i + 1 ≤ n
  · simp only [stepStage, if_pos hi, if_pos (by omega : i ≤ n)] at *
    exact nextPredicate_mono core hcore c.rel (c.mono i) s hs
  · simp only [stepStage, if_neg hi]

def step (hinj : Function.Injective (expMatrix core)) : AmbientChain core (n + 1) where
  extraGen := NextExtraGen core hcore c.rel
  extraCell := NextExtraCell core hcore c.rel
  fresh := Sum.inl (c.fresh, false)
  rel := nextExtra core hcore c.rel
  stage := c.stepStage hcore
  saturated i hi _ := by simp only [stepStage, if_neg (by omega : ¬ i ≤ n)]
  mono := c.stepStage_mono hcore
  strict i hi := by
    by_cases hin : i < n
    · obtain ⟨s, hs, hsp⟩ := c.strict i hin
      simpa only [stepStage, if_pos (by omega : i ≤ n), if_pos (by omega : i + 1 ≤ n)] using
        nextStage_strict core hcore c.rel (p := c.stage i) (t := c.stage (i + 1)) s hs hsp
    · obtain rfl : i = n := by omega
      exact ⟨Sum.inr (c.fresh, false), by simp [stepStage], by simp [stepStage, nextPredicate]⟩
  cockcroft i := by
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      FSIsCockcroft (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [show c.stepStage hcore i = nextPredicate core hcore c.rel (c.stage i) from if_pos hi]
      exact nextStage_cockcroft core hcore c.rel (c.stage i) (c.cockcroft i)
    · rw [show c.stepStage hcore i = fun _ => True from if_neg hi]
      exact fsIsCockcroft_of_generates
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (fullIntoStage_generates core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft c.full_core_trivial).1
  core_trivial i a := by
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))) = 1
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [show c.stepStage hcore i = nextPredicate core hcore c.rel (c.stage i) from if_pos hi]
      exact nextStage_core_trivial core hcore c.rel (c.stage i) (c.core_trivial i) a
    · rw [show c.stepStage hcore i = fun _ => True from if_neg hi]
      have h := congrArg (fullIntoStage core (nextExtra core hcore c.rel)
        (fun _ => True) (fun _ => trivial)).hom
        (nextFull_core_trivial core hcore c.rel c.full_core_trivial a)
      change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial)).hom 1 at h
      exact (show (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) (fun _ => True)))) = 1
        from by simpa only [FreeGroup.map.id, map_one] using h)
  zero i hi x hx := by
    let P (p t : NextExtraCell core hcore c.rel → Prop) : Prop :=
      ∀ (hpt : ∀ s, p s → t s)
        (y : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
          (PresGroup (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p)))),
        FSIsFoxCycle (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p)) y →
          (rawInclusion core (nextExtra core hcore c.rel) hpt).cells y = 0
    have hz : P (c.stepStage hcore i) (c.stepStage hcore (i + 1)) := by
      by_cases hin : i < n
      · rw [show c.stepStage hcore i = nextPredicate core hcore c.rel (c.stage i) from if_pos (by omega),
          show c.stepStage hcore (i + 1) = nextPredicate core hcore c.rel (c.stage (i + 1)) from if_pos (by omega)]
        exact fun _ _ hy => nextStage_preserves_zero core hcore c.rel (c.mono i) (c.zero i hin) hy
      · rw [show i = n by omega,
          show c.stepStage hcore n = nextPredicate core hcore c.rel (c.stage n) from if_pos le_rfl,
          show c.stepStage hcore (n + 1) = fun _ => True from if_neg (by omega),
          show c.stage n = fun _ => True from funext fun s => propext ⟨fun _ => trivial, fun _ => c.saturated n le_rfl s⟩]
        intro hpt y hy
        rw [rawInclusion_factor_full core (nextExtra core hcore c.rel) hpt (fun _ => trivial),
          (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft c.full_core_trivial).2 y hy,
          PresMorFS.cells_zero]
    exact hz (c.stepStage_mono hcore i) x hx

end AmbientChain

def ambientChains (hcore : Function.Bijective (expMatrix core))
    (initial : AmbientChain core 0) : (n : ℕ) → AmbientChain core n
  | 0 => initial
  | n + 1 => (ambientChains hcore initial n).step hcore.2 hcore.1
