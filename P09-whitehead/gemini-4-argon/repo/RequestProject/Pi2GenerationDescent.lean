module

public import RequestProject.ZeroPi2Descent

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

section

variable {X : Complex2.{u}} {y₀ w₀ : X.V} {q : List (X.E × Bool)}

def shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) : PathFrom X y₀ :=
  ⟨q ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath hq]
    exact isPath_append_iff.mpr ⟨w₀, hq, p.2⟩⟩

theorem endpt_shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) :
    endpt X y₀ (shiftP hq p).1 = endpt X w₀ p.1 := by
  show endpt X y₀ (q ++ p.1) = endpt X w₀ p.1
  rw [endpt_append, endpt_eq_of_isPath hq]

def shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) : UV X y₀ :=
  Quotient.map (shiftP hq) (fun p p' hpp => by
    show Htpy X y₀ (endpt X y₀ (shiftP hq p).1) (shiftP hq p).1 (shiftP hq p').1
    rw [endpt_shiftP]
    exact Htpy.append_congr hq p.2 (.refl q) hpp) c

@[simp] theorem endV_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) :
    endV (shiftV hq c) = endV c := by
  induction c using UV.ind with | h p => exact endpt_shiftP hq p

theorem shiftV_base (hq : IsPath X.src X.tgt q y₀ w₀) :
    shiftV hq (UV.base X w₀) = UV.mk ⟨q, (endpt_eq_of_isPath hq).symm ▸ hq⟩ :=
  congrArg UV.mk (Subtype.ext (List.append_nil q))

theorem extend_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (eb : X.E × Bool) (c : UV X w₀) :
    extend eb (shiftV hq c) = shiftV hq (extend eb c) := by
  induction c using UV.ind with | h p =>
  have hl : (extendP eb (shiftP hq p)).1 = (shiftP hq (extendP eb p)).1 := by
    by_cases h : endpt X w₀ p.1 = germSrc X.src X.tgt eb
    · rw [extendP_pos (by rwa [endpt_shiftP])]; show (q ++ p.1) ++ [eb] = q ++ (extendP eb p).1
      simp [extendP_pos h]
    · rw [extendP_neg (by rwa [endpt_shiftP])]; show q ++ p.1 = q ++ (extendP eb p).1
      simp [extendP_neg h]
  refine Quotient.sound ?_
  show Htpy X y₀ (endpt X y₀ (extendP eb (shiftP hq p)).1) (extendP eb (shiftP hq p)).1
    (shiftP hq (extendP eb p)).1
  rw [hl]

def shiftE (hq : IsPath X.src X.tgt q y₀ w₀) (E : UE X w₀) : UE X y₀ :=
  ⟨(shiftV hq E.1.1, E.1.2), by rw [endV_shiftV]; exact E.2⟩

def shiftF (hq : IsPath X.src X.tgt q y₀ w₀) (F : UF X w₀) : UF X y₀ :=
  ⟨(shiftV hq F.1.1, F.1.2), by rw [endV_shiftV]; exact F.2⟩

theorem uLiftPath_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) :
    ∀ (l : List (X.E × Bool)) (c : UV X w₀) (v : X.V), IsPath X.src X.tgt l (endV c) v →
      uLiftPath l (shiftV hq c) = (uLiftPath l c).map (fun Eb => (shiftE hq Eb.1, Eb.2))
  | [], _, _, _ => rfl
  | eb :: t, c, v, hl => by
      have h' : endV (shiftV hq c) = germSrc X.src X.tgt eb := (endV_shiftV hq c).trans hl.1
      have hlg : liftGerm (shiftV hq c) eb h' = (shiftE hq (liftGerm c eb hl.1).1, (liftGerm c eb hl.1).2) := by
        rcases eb with ⟨e, _ | _⟩
        · exact Prod.ext (Subtype.ext (Prod.ext (extend_shiftV hq (e, false) c) rfl)) rfl
        · rfl
      rw [uLiftPath_cons h', uLiftPath_cons hl.1, List.map_cons, hlg,
        extend_shiftV hq eb c, uLiftPath_shiftV hq t (extend eb c) v (endV_extend hl.1 ▸ hl.2)]

def shiftHom (hq : IsPath X.src X.tgt q y₀ w₀) :
    Hom (uCover X w₀) (uCover X y₀) where
  onV := shiftV hq
  onE := shiftE hq
  onF := shiftF hq
  src_onE _ := rfl
  tgt_onE E := extend_shiftV hq (E.1.2, true) E.1.1
  base_onF _ := rfl
  att_onF F := uLiftPath_shiftV hq (X.att F.1.2) F.1.1 (X.base F.1.2) (F.2 ▸ X.att_isLoop F.1.2)

end

variable {L L' E E' D K M : Complex2.{u}}

def Pi2FromSub (ι : Hom L E) (x₀ : E.V) : Set ((uCover E x₀).F →₀ ℤ) :=
  {d | ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ z ∈ Pi2 L l₀, d = chain2 φ z}

theorem zeroPi2_chain_of_generated (ι : Hom L E) (k : Hom L L') (ι' : Hom L' E') (j : Hom E E')
    (hsq : j.comp ι = ι'.comp k) (hconnE' : IsConnected E') (hzero : ZeroPi2 k) {x₀ : E.V}
    {c : (uCover E x₀).F →₀ ℤ} (hgen : c ∈ Submodule.span ℤ (Pi2FromSub ι x₀)) :
    chain2 (univLift E j x₀) c = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (chain2 (univLift E j x₀)))).2 ?_ hgen
  rintro d ⟨l₀, φ, hφV, hφE, hφF, z, hz, rfl⟩
  show chain2 (univLift E j x₀) (chain2 φ z) = 0
  set J := univLift E j x₀
  set A := J.comp φ
  set kappa := univLift L k l₀
  have hbaseV : endV (A.onV (UV.base L l₀)) = ι'.onV (k.onV l₀) := by
    show endV (univLiftV x₀ j (φ.onV (UV.base L l₀))) = ι'.onV (k.onV l₀)
    rw [endV_univLiftV, hφV]; exact congrArg (·.onV l₀) hsq
  obtain ⟨tp, htp⟩ := Quotient.exists_rep (A.onV (UV.base L l₀))
  have hqpath : IsPath E'.src E'.tgt tp.1 (j.onV x₀) (ι'.onV (k.onV l₀)) := by
    have hend : endpt E' (j.onV x₀) tp.1 = ι'.onV (k.onV l₀) := by rw [← hbaseV, ← htp]; rfl
    exact hend ▸ tp.2
  set chi := (shiftHom hqpath).comp (univLift L' ι' (k.onV l₀))
  set B := chi.comp kappa
  have hqcov := isCovering_univProj (x₀ := j.onV x₀) hconnE'
  have hV := lift_onV_eq (A := A) (B := B) hqcov isConnected_univCover
    (fun e => by show j.onE ((φ.onE e).1).2 = ι'.onE (k.onE e.1.2); rw [hφE e]; exact congrArg (·.onE e.1.2) hsq)
    (x := UV.base L l₀)
    (by show A.onV (UV.base L l₀) = shiftV hqpath (UV.base E' (ι'.onV (k.onV l₀)))
        rw [shiftV_base]; exact htp.symm)
  have hFeq := lift_onF_eq (A := A) (B := B) hqcov
    (fun f => by show j.onF ((φ.onF f).1).2 = ι'.onF (k.onF f.1.2); rw [hφF f]; exact congrArg (·.onF f.1.2) hsq) hV
  have hAz : chain2 J (chain2 φ z) = chain2 A z := by
    show Finsupp.mapDomain J.onF (Finsupp.mapDomain φ.onF z) = Finsupp.mapDomain (J.onF ∘ φ.onF) z
    rw [← Finsupp.mapDomain_comp]
  have hBz : chain2 B z = chain2 chi (chain2 kappa z) := by
    show Finsupp.mapDomain (chi.onF ∘ kappa.onF) z = Finsupp.mapDomain chi.onF (Finsupp.mapDomain kappa.onF z)
    rw [← Finsupp.mapDomain_comp]
  have hAB : chain2 A z = chain2 B z := congrArg (Finsupp.mapDomain · z) (funext hFeq)
  rw [hAz, hAB, hBz, hzero l₀ z hz, map_zero]

theorem zeroPi2_pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hjF : Function.Injective j.onF) (hj'V : Function.Injective j'.onV)
    (hj'E : Function.Injective j'.onE) (hj'F : Function.Injective j'.onF)
    (hkj : k.comp j = j') (hconnE' : IsConnected (pushoutComplex p j' hj'V hj'E))
    (hzero : ZeroPi2 k)
    (hgen : ∀ x₀ : (pushoutComplex p j hjV hjE).V,
      ∀ c ∈ Pi2 (pushoutComplex p j hjV hjE) x₀,
        c ∈ Submodule.span ℤ (Pi2FromSub (pushoutMap p j hjV hjE hjF) x₀)) :
    ZeroPi2 (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj) := by
  have hsq : (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj).comp
      (pushoutMap p j hjV hjE hjF) = (pushoutMap p j' hj'V hj'E hj'F).comp k := by
    have hext {X Y : Complex2.{u}} : ∀ a b : Hom X Y,
        a.onV = b.onV → a.onE = b.onE → a.onF = b.onF → a = b := by
      rintro ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ rfl rfl rfl; rfl
    let g := (pushoutMap p j' hj'V hj'E hj'F).comp k
    let f := pushoutInl p j' hj'V hj'E
    refine hext _ _ (funext fun v => ?_) (funext fun e => ?_) (funext fun c => ?_)
    · show Sum.elim f.onV (fun w : OffV j => g.onV w.1) (pushV p j v) = g.onV v
      by_cases h : ∃ d, j.onV d = v
      · obtain ⟨d, rfl⟩ := h; rw [pushV_of_mem p hjV d]
        show Sum.inl (p.onV d) = pushV p j' (k.onV (j.onV d))
        erw [congrFun (congrArg Hom.onV hkj) d, pushV_of_mem p hj'V]
      · rw [pushV_of_off p j ⟨v, fun d hd => h ⟨d, hd⟩⟩]; rfl
    · show Sum.elim f.onE (fun w : OffE j => g.onE w.1) (pushE p j e) = g.onE e
      by_cases h : ∃ d, j.onE d = e
      · obtain ⟨d, rfl⟩ := h; rw [pushE_of_mem p hjE d]
        show Sum.inl (p.onE d) = pushE p j' (k.onE (j.onE d))
        erw [congrFun (congrArg Hom.onE hkj) d, pushE_of_mem p hj'E]
      · rw [pushE_of_off p j ⟨e, fun d hd => h ⟨d, hd⟩⟩]; rfl
    · show Sum.elim f.onF (fun w : OffF j => g.onF w.1) (pushF p j c) = g.onF c
      by_cases h : ∃ d, j.onF d = c
      · obtain ⟨d, rfl⟩ := h; rw [pushF_of_mem p hjF d]
        show Sum.inl (p.onF d) = pushF p j' (k.onF (j.onF d))
        erw [congrFun (congrArg Hom.onF hkj) d, pushF_of_mem p hj'F]
      · rw [pushF_of_off p j ⟨c, fun d hd => h ⟨d, hd⟩⟩]; rfl
  exact fun x₀ c hc => zeroPi2_chain_of_generated _ k _ _ hsq hconnE' hzero (hgen x₀ c hc)
