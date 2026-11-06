module

public import RequestProject.CombPi2
public import RequestProject.CombPresPi1
public import RequestProject.UnivCoverIncl

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α)

def uvWord : UV (presComplex ρ) PUnit.unit → PresGroup ρ :=
  Quotient.lift (fun p : PathFrom (presComplex ρ) PUnit.unit => presWord ρ p.1)
    (fun _ _ h => presWord_htpy ρ h)

@[simp] theorem uvWord_mk (p : PathFrom (presComplex ρ) PUnit.unit) :
    uvWord ρ (UV.mk p) = presWord ρ p.1 := rfl

theorem uvWord_bijective : Function.Bijective (uvWord ρ) := by
  refine ⟨fun c d h => ?_, fun g => ?_⟩
  · induction c using UV.ind with | h p =>
    induction d using UV.ind with | h q =>
    exact Quotient.sound (Quotient.exact
      ((pi1PresEquiv ρ).injective (h : pi1ToPres ρ (Pi1.mk ⟨p.1, isPath_of_subsingleton _ _ _ _ _⟩) =
        pi1ToPres ρ (Pi1.mk ⟨q.1, isPath_of_subsingleton _ _ _ _ _⟩))))
  · induction g using QuotientGroup.induction_on with | H w =>
    refine ⟨UV.mk ⟨w.toWord, isPath_of_subsingleton _ _ _ _ _⟩, ?_⟩
    show presWord ρ w.toWord = _
    unfold presWord; rw [FreeGroup.mk_toWord]

theorem uvWord_extend_true (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, true) c) = uvWord ρ c * qof (relSub ρ) i := by
  induction c using UV.ind with | h p =>
  rw [extend_mk, uvWord_mk, extendP_pos (Subsingleton.elim _ _), uvWord_mk, presWord_append]; rfl

theorem uvWord_extend_false (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, false) c) = uvWord ρ c * (qof (relSub ρ) i)⁻¹ := by
  induction c using UV.ind with | h p =>
  rw [extend_mk, uvWord_mk, extendP_pos (Subsingleton.elim _ _), uvWord_mk, presWord_append]
  congr 1

def uvEdge (E : UE (presComplex ρ) PUnit.unit) : (univCover ρ).E := (uvWord ρ E.1.1, E.1.2)
def uvFace (F : UF (presComplex ρ) PUnit.unit) : (univCover ρ).F := (uvWord ρ F.1.1, F.1.2)

theorem map_uLiftPath_pres : ∀ (L : List (α × Bool)) (c : UV (presComplex ρ) PUnit.unit),
    (uLiftPath L c).map (fun Eb => (uvEdge ρ Eb.1, Eb.2)) = liftPath L (uvWord ρ c)
  | [], _ => rfl
  | (i, b) :: t, c => by
      rw [uLiftPath_cons (Subsingleton.elim _ _)]
      cases b
      · rw [liftPath_cons_false, List.map_cons, map_uLiftPath_pres t, uvWord_extend_false]
        exact congrArg (· :: _) (Prod.ext (Prod.ext (uvWord_extend_false ρ i c) rfl) rfl)
      · rw [liftPath_cons_true, List.map_cons, map_uLiftPath_pres t, uvWord_extend_true]; rfl

def presUnivHom : Hom (uCover (presComplex ρ) PUnit.unit) (univCover ρ) where
  onV := uvWord ρ
  onE := uvEdge ρ
  onF := uvFace ρ
  src_onE _ := rfl
  tgt_onE E := (uvWord_extend_true ρ E.1.2 E.1.1).symm
  base_onF _ := rfl
  att_onF _ := (map_uLiftPath_pres ρ _ _).symm

theorem uvPair_bijective {T : Type u} :
    Function.Bijective (fun x : {cp : UV (presComplex ρ) PUnit.unit × T // endV cp.1 = PUnit.unit} =>
      (uvWord ρ x.1.1, x.1.2)) :=
  ⟨fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h => by
    obtain ⟨h1, rfl⟩ := Prod.mk.inj h
    exact Subtype.ext (Prod.ext ((uvWord_bijective ρ).1 h1) rfl),
   fun ⟨q, i⟩ =>
    let ⟨c, hc⟩ := (uvWord_bijective ρ).2 q
    ⟨⟨(c, i), rfl⟩, Prod.ext hc rfl⟩⟩

theorem mem_pi2_iff_bdry2_eq_zero (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    u ∈ Pi2 (presComplex ρ) PUnit.unit ↔ bdry2 (univCover ρ) (chain2 (presUnivHom ρ) u) = 0 := by
  rw [bdry2_chain2]
  exact ⟨fun (hu : bdry2 _ u = 0) => by rw [hu, map_zero],
    fun hu => Finsupp.mapDomain_injective (uvPair_bijective ρ).1 (by rw [Finsupp.mapDomain_zero]; exact hu)⟩

variable {β K : Type u} [DecidableEq β] {σ : K → FreeGroup β}
variable (f : α → β) (hf : Function.Injective f) (g : J → K)
  (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))

theorem chain2_presUnivHom_square (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    chain2 (presUnivHom σ)
        (chain2 (univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit) u)
      = chain2 (univCoverInclHom f hf ρ σ g hg) (chain2 (presUnivHom ρ) u) := by
  show Finsupp.mapDomain (uvFace σ)
      (Finsupp.mapDomain ((univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit).onF) u)
    = Finsupp.mapDomain (univCoverInclHom f hf ρ σ g hg).onF
      (Finsupp.mapDomain (uvFace ρ) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (Finsupp.mapDomain · u) (funext fun ⟨⟨c, _⟩, _⟩ => Prod.ext ?_ rfl)
  induction c using UV.ind with | h p =>
  exact (presInclGroupHom_mk f ρ σ g hg (FreeGroup.mk p.1)).symm

theorem zeroPi2_presInclHom_iff :
    ZeroPi2 (presInclHom f hf ρ σ g hg) ↔
      ∀ v : (univCover ρ).F →₀ ℤ, bdry2 (univCover ρ) v = 0 →
        chain2 (univCoverInclHom f hf ρ σ g hg) v = 0 := by
  classical
  constructor
  · intro hzero v hv
    obtain ⟨u, rfl⟩ : ∃ u, chain2 (presUnivHom ρ) u = v :=
      Finsupp.mapDomain_surjective (M := ℤ) (uvPair_bijective ρ).2 v
    rw [← chain2_presUnivHom_square ρ f hf g hg u,
      hzero PUnit.unit u ((mem_pi2_iff_bdry2_eq_zero ρ u).2 hv), map_zero]
  · intro hzero x₀ u hu
    have hinj : Function.Injective (chain2 (presUnivHom σ)) :=
      Finsupp.mapDomain_injective (uvPair_bijective σ).1
    exact hinj (by rw [map_zero, chain2_presUnivHom_square ρ f hf g hg u,
      hzero _ ((mem_pi2_iff_bdry2_eq_zero ρ u).1 hu)])

theorem pi1Trivial_presInclHom_iff :
    Pi1Trivial (presInclHom f hf ρ σ g hg) ↔
      ∀ w : PresGroup ρ, presInclGroupHom f ρ σ g hg w = 1 := by
  have hmap (l : List (α × Bool)) :
      presWord σ (mapPath (presInclHom f hf ρ σ g hg) l) =
        presInclGroupHom f ρ σ g hg (presWord ρ l) :=
    (presInclGroupHom_mk f ρ σ g hg (FreeGroup.mk l)).symm
  constructor
  · intro hpi w
    induction w using QuotientGroup.induction_on with | H x =>
    have hw := presWord_htpy σ (hpi PUnit.unit x.toWord (isPath_of_subsingleton _ _ _ _ _))
    rw [hmap, presWord_nil] at hw
    rw [← hw]
    exact congrArg (presInclGroupHom f ρ σ g hg ∘ QuotientGroup.mk) (FreeGroup.mk_toWord.symm)
  · intro hw _ p _
    have hone : (Pi1.mk ⟨mapPath (presInclHom f hf ρ σ g hg) p, isPath_of_subsingleton _ _ _ _ _⟩ :
        Pi1 (presComplex σ) PUnit.unit) = 1 :=
      (pi1PresEquiv σ).injective (by rw [map_one]; exact (hmap p).trans (hw _))
    exact Quotient.exact hone
