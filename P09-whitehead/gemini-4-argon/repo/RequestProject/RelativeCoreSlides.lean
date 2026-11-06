module

public import RequestProject.RelativeNormalizedRestrictions
public import RequestProject.SimultaneousCoreSlidesFinsupp

@[expose] public section

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

def pairCorePresentation : C → FreeGroup (PairGen A Z) :=
  fun c => FreeGroup.map Sum.inl (core c)

def pairCorrection (w : FreeGroup (A ⊕ Z)) : FreeGroup (PairGen A Z) :=
  FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

theorem pairCorrection_filling_exists (w : FreeGroup (A ⊕ Z)) :
    ∃ v : C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)),
      coverSecondBoundary (relSub (pairCorePresentation (Z := Z) core))
        (pairCorePresentation core) v =
      coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
        (pairCorrection core hcore w) := by
  have hmem : pairCorrection core hcore w ∈ relSub (pairCorePresentation (Z := Z) core) :=
    coreCorrection_mem core (relSub (pairCorePresentation (Z := Z) core))
      (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩) _
  exact (coverFoxGradient_mem_range_iff (relSub (pairCorePresentation (Z := Z) core))
    (pairCorePresentation (Z := Z) core)
    (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩) hmem).mpr
    ((le_sup_left : relSub (pairCorePresentation (Z := Z) core) ≤ _) hmem)

def pairCorrectionFilling (w : FreeGroup (A ⊕ Z)) :
    C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)) :=
  Classical.choose (pairCorrection_filling_exists core hcore w)

variable (extra : S → FreeGroup (A ⊕ Z))

def slideGroupHom : PresGroup (beforeCorrection core extra) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _)
    (by rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra])

theorem slideGroupHom_injective :
    Function.Injective (slideGroupHom core hcore extra) :=
  Function.LeftInverse.injective
    (g := QuotientGroup.map _ _ (MonoidHom.id _)
      (by rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra]))
    fun g => by induction g using QuotientGroup.induction_on with | H w => rfl

def pairCoreToNormalized : PresGroup (pairCorePresentation (Z := Z) core) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _)
    (Subgroup.normalClosure_le_normal (by rintro _ ⟨c, rfl⟩; exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩))

theorem gradient_groupMap {G H : Subgroup (FreeGroup (PairGen A Z))}
    [G.Normal] [H.Normal] (f : (FreeGroup (PairGen A Z) ⧸ G) →* (FreeGroup (PairGen A Z) ⧸ H))
    (hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk w)
    (w : FreeGroup (PairGen A Z)) :
    (coverFoxGradient G w).mapRange (MonoidAlgebra.mapDomainRingHom ℤ f) (map_zero _) =
      coverFoxGradient H w := by
  ext i : 1
  change MonoidAlgebra.mapDomainRingHom ℤ f (proj G (fox i w)) = proj H (fox i w)
  generalize fox i w = x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single u a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain f (Finsupp.mapDomain (QuotientGroup.mk' G) (Finsupp.single u a)) =
        Finsupp.mapDomain (QuotientGroup.mk' H) (Finsupp.single u a)
      simp only [Finsupp.mapDomain_single, QuotientGroup.mk'_apply, hf]

def slideCoefficients := MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore extra)

def slideCoreCoefficients :=
  MonoidAlgebra.mapDomainRingHom ℤ (pairCoreToNormalized core hcore extra)

def slideColumns (s : S) :
    C →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra)) :=
  (pairCorrectionFilling core hcore (extra s)).mapRange
    (slideCoreCoefficients core hcore extra) (map_zero _)

def slideOldBoundary :
    ((C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) →ₗ[
      MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))]
      (PairGen A Z →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :=
  fsRingMapBoundary (slideCoefficients core hcore extra)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra)) (beforeCorrection core extra j))

theorem slideOldBoundary_single (k : C ⊕ S)
    (a : MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    slideOldBoundary core hcore extra (Finsupp.single k a) =
      a • coverFoxGradient (relSub (normalizedPresentation core hcore extra))
        (beforeCorrection core extra k) := by
  rw [slideOldBoundary, fsRingMapBoundary, Finsupp.linearCombination_single]; congr 1
  exact gradient_groupMap (slideGroupHom core hcore extra) (fun _ => rfl) _

theorem normalizationSlide_boundary
    (x : (C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    coverSecondBoundary (relSub (normalizedPresentation core hcore extra))
      (normalizedPresentation core hcore extra) x =
    slideOldBoundary core hcore extra (coreSlideReverse (slideColumns core hcore extra) x) := by
  refine coreSlide_boundary (slideColumns core hcore extra)
    (slideOldBoundary core hcore extra) _ (fun c => ?_) (fun s => ?_) x
  · rw [coverSecondBoundary_single, slideOldBoundary_single]; rfl
  · have hm : (slideOldBoundary core hcore extra).comp fsOldOneIncl =
        fsRingMapBoundary (slideCoreCoefficients core hcore extra)
          (fun c => coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
            (pairCorePresentation core c)) := by
      refine Finsupp.lhom_ext fun c a => ?_
      simp only [LinearMap.comp_apply, fsOldOneIncl_single, slideOldBoundary_single,
        fsRingMapBoundary, Finsupp.linearCombination_single]
      exact congrArg (a • ·) (gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _).symm
    have hcol : slideOldBoundary core hcore extra (fsOldOneIncl (slideColumns core hcore extra s)) =
        coverFoxGradient (relSub (normalizedPresentation core hcore extra))
          (pairCorrection core hcore (extra s)) := by
      change ((slideOldBoundary core hcore extra).comp fsOldOneIncl)
        ((pairCorrectionFilling core hcore (extra s)).mapRange
          (slideCoreCoefficients core hcore extra) (map_zero _)) = _
      rw [hm, fsRingMapBoundary_mapRange]
      erw [Classical.choose_spec (pairCorrection_filling_exists core hcore (extra s))]
      exact gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _
    rw [coverSecondBoundary_single, one_smul, slideOldBoundary_single, one_smul, hcol]
    change coverFoxGradient _ (normalizedWord core hcore (extra s)) = _
    rw [normalizedWord_eq]
    exact coverFoxGradient_mul _ (by
      rw [relSub_normalizedPresentation]
      exact Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩) _

def normalizationSlideMap : PresMorFS (beforeCorrection core extra)
    (normalizedPresentation core hcore extra) where
  hom := slideGroupHom core hcore extra
  cells x := coreSlideForward (slideColumns core hcore extra)
    (x.mapRange (slideCoefficients core hcore extra) (map_zero _))
  cells_add x y := by rw [Finsupp.mapRange_add, map_add]; exact map_add _
  cells_smul a x := by
    rw [show (a • x).mapRange (slideCoefficients core hcore extra) (map_zero _) =
        (slideCoefficients core hcore extra a) • x.mapRange (slideCoefficients core hcore extra) (map_zero _) by
      ext k : 1; simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]; exact map_mul _ _ _,
      map_smul]; rfl
  cells_cycle x hx := by
    change coverSecondBoundary _ _ _ = 0
    rw [normalizationSlide_boundary, coreSlideReverse_forward]
    change fsRingMapBoundary (slideCoefficients core hcore extra) _ (x.mapRange _ _) = 0
    rw [fsRingMapBoundary_mapRange]; erw [hx]; simp
  cells_aug x hx k := by
    apply coreSlideForward_aug_zero
    intro j
    exact (augQ_mapDomain (slideGroupHom core hcore extra) (x j)).trans (hx j)

theorem normalizationSlideMap_generates :
    FSGenerates (normalizationSlideMap core hcore extra) := by
  intro x hx
  let y := coreSlideReverse (slideColumns core hcore extra) x
  have hy : slideOldBoundary core hcore extra y = 0 :=
    (normalizationSlide_boundary core hcore extra x).symm.trans hx
  have hspan := fs_cycle_mem_span_groupMap_cycles (slideGroupHom core hcore extra)
    (slideGroupHom_injective core hcore extra)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra))
      (beforeCorrection core extra j)) y hy
  have he : coreSlideForward (slideColumns core hcore extra) y = x := coreSlideForward_reverse _ _
  rw [← he]
  clear hx hy he
  generalize y = z at hspan ⊢
  clear y x
  induction hspan using Submodule.span_induction with
  | mem z hz => obtain ⟨a, ha, rfl⟩ := hz; exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | smul a _ _ hz => rw [map_smul]; exact Submodule.smul_mem _ a hz
