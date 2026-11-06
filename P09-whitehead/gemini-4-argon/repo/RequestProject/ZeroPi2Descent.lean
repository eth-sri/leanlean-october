module

public import RequestProject.UniversalToCover
public import RequestProject.CombPushout

@[expose] public section

noncomputable section
namespace FiniteChains.Comb

universe u

section

variable {X Z W : Complex2.{u}}

theorem mapPath_comp (g : Hom Z W) (h : Hom X Z) (l : List (X.E × Bool)) :
    mapPath g (mapPath h l) = mapPath (g.comp h) l := by
  simp [mapPath, List.map_map, Function.comp_def, Hom.comp]

variable {q : Hom Z W} {A B : Hom X Z}

theorem lift_onV_eq (hq : IsCovering q) (hX : IsConnected X)
    (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e)) {x : X.V} (hx : A.onV x = B.onV x) :
    ∀ v, A.onV v = B.onV v := by
  intro v
  obtain ⟨m, hm⟩ := hX x v
  have hA := isPath_mapPath A hm
  have hB : IsPath Z.src Z.tgt (mapPath B m) (A.onV x) (B.onV v) := hx.symm ▸ isPath_mapPath B hm
  have hlists := liftPath_unique hq (mapPath A m) (mapPath B m) (A.onV x) _ _ hA hB (by
    simp only [mapPath, List.map_map, Function.comp_def]
    exact List.map_congr_left fun eb _ => by rw [hE eb.1])
  exact isPath_endpoint_eq hA (hlists ▸ hB)

theorem lift_onE_eq (hq : IsCovering q) (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ e, A.onE e = B.onE e := fun e => by
  have h1 : germSrc Z.src Z.tgt (A.onE e, true) = A.onV (X.src e) := A.src_onE e
  have h2 : germSrc Z.src Z.tgt (B.onE e, true) = A.onV (X.src e) := (B.src_onE e).trans (hV _).symm
  exact congrArg Prod.fst (liftGerm_unique hq h1 h2
    (show (q.onE (A.onE e, true).1, (A.onE e, true).2) =
      (q.onE (B.onE e, true).1, (B.onE e, true).2) by rw [hE e]))

theorem lift_onF_eq (hq : IsCovering q) (hF : ∀ f, q.onF (A.onF f) = q.onF (B.onF f))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ f, A.onF f = B.onF f := by
  intro f
  obtain ⟨g, -, huniq⟩ := exists_unique_liftCell hq (q.onF (A.onF f))
    (by rw [q.base_onF, A.base_onF])
  rw [huniq (A.onF f) ⟨rfl, A.base_onF f⟩,
    huniq (B.onF f) ⟨(hF f).symm, by rw [B.base_onF f, hV]⟩]

end

section

variable {D Y : Complex2.{u}}

theorem mapPath_revPath (f : Hom D Y) (m : List (D.E × Bool)) :
    mapPath f (revPath m) = revPath (mapPath f m) := by
  simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]

theorem htpy_mapPath_of_pi1Trivial {f : Hom D Y} (htriv : Pi1Trivial f)
    {m m' : List (D.E × Bool)} {a b : D.V} (hm : IsPath D.src D.tgt m a b)
    (hm' : IsPath D.src D.tgt m' a b) :
    Htpy Y (f.onV a) (f.onV b) (mapPath f m) (mapPath f m') := by
  have hP := isPath_mapPath f hm
  have hQ := isPath_mapPath f hm'
  have hQrev := isPath_revPath hQ
  have h0 : Htpy Y (f.onV a) (f.onV a) (mapPath f m ++ revPath (mapPath f m')) [] := by
    have h := htriv a (m ++ revPath m') (isPath_append_iff.mpr ⟨b, hm, isPath_revPath hm'⟩)
    rwa [mapPath_append, mapPath_revPath] at h
  have step1 := Htpy.append_congr hP (isPath_append_iff.mpr ⟨f.onV a, hQrev, hQ⟩)
    (.refl _) (htpy_revPath_append hQ)
  have step2 := Htpy.append_congr (isPath_append_iff.mpr ⟨f.onV b, hP, hQrev⟩) hQ h0 (.refl _)
  rw [List.append_assoc] at step2
  simpa using step1.symm.trans step2

variable (f : Hom D Y) (hconn : IsConnected D) (d₀ : D.V)

def cPath (v : D.V) : List (D.E × Bool) := (hconn d₀ v).choose

theorem cPath_isPath (v : D.V) : IsPath D.src D.tgt (cPath hconn d₀ v) d₀ v :=
  (hconn d₀ v).choose_spec

def pathFromMap {v : D.V} {m : List (D.E × Bool)} (hm : IsPath D.src D.tgt m d₀ v) :
    PathFrom Y (f.onV d₀) :=
  ⟨mapPath f m, (endpt_eq_of_isPath (isPath_mapPath f hm)).symm ▸ isPath_mapPath f hm⟩

def liftV (v : D.V) : UV Y (f.onV d₀) :=
  UV.mk (pathFromMap f d₀ (cPath_isPath hconn d₀ v))

variable {f d₀}

theorem liftV_eq (htriv : Pi1Trivial f) {v : D.V} {m : List (D.E × Bool)}
    (hm : IsPath D.src D.tgt m d₀ v) :
    liftV f hconn d₀ v = UV.mk (pathFromMap f d₀ hm) := by
  refine UV.sound ?_
  show Htpy Y (f.onV d₀) (endpt Y (f.onV d₀) (mapPath f (cPath hconn d₀ v)))
    (mapPath f (cPath hconn d₀ v)) (mapPath f m)
  rw [endpt_eq_of_isPath (isPath_mapPath f (cPath_isPath hconn d₀ v))]
  exact htpy_mapPath_of_pi1Trivial htriv (cPath_isPath hconn d₀ v) hm

@[simp] theorem endV_liftV (v : D.V) : endV (liftV f hconn d₀ v) = f.onV v :=
  endpt_eq_of_isPath (isPath_mapPath f (cPath_isPath hconn d₀ v))

variable (f d₀)

def liftE (e : D.E) : UE Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.src e), f.onE e), by rw [endV_liftV, f.src_onE]⟩

def liftF (g : D.F) : UF Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.base g), f.onF g), by rw [endV_liftV, f.base_onF]⟩

variable {f d₀}

theorem uTgt_liftE (htriv : Pi1Trivial f) (e : D.E) :
    uTgt (liftE f hconn d₀ e) = liftV f hconn d₀ (D.tgt e) := by
  let eb := (e, true)
  set v := germSrc D.src D.tgt eb
  have hm := cPath_isPath hconn d₀ v
  have hstep : IsPath D.src D.tgt (cPath hconn d₀ v ++ [eb]) d₀ (D.tgt e) :=
    isPath_append_iff.mpr ⟨v, hm, isPath_single eb⟩
  show extend (f.onE e, true) (liftV f hconn d₀ v) = _
  rw [liftV_eq hconn htriv hstep, liftV_eq hconn htriv hm, extend_mk]
  refine congrArg UV.mk (Subtype.ext ?_)
  have hend : endpt Y (f.onV d₀) (mapPath f (cPath hconn d₀ v)) =
      germSrc Y.src Y.tgt (f.onE e, true) := by
    rw [endpt_eq_of_isPath (isPath_mapPath f hm), germSrc_onE f eb]
  show (extendP (f.onE e, true) (pathFromMap f d₀ hm)).1 = mapPath f (cPath hconn d₀ v ++ [eb])
  rw [extendP_pos hend]
  simp [mapPath, pathFromMap, eb]

def liftHom (htriv : Pi1Trivial f) : Hom D (uCover Y (f.onV d₀)) where
  onV := liftV f hconn d₀
  onE := liftE f hconn d₀
  onF := liftF f hconn d₀
  src_onE _ := rfl
  tgt_onE := uTgt_liftE hconn htriv
  base_onF _ := rfl
  att_onF g := by
    have hpath := isPath_map (src := D.src) (tgt := D.tgt)
      (src' := (uCover Y (f.onV d₀)).src) (tgt' := (uCover Y (f.onV d₀)).tgt)
      (liftV f hconn d₀) (liftE f hconn d₀) (fun _ => rfl) (uTgt_liftE hconn htriv)
      (D.att_isLoop g)
    have hproj : mapPath (univProj Y (f.onV d₀))
        ((D.att g).map fun eb => (liftE f hconn d₀ eb.1, eb.2)) = Y.att (f.onF g) := by
      rw [f.att_onF g]; simp [mapPath, List.map_map, Function.comp_def, univProj, liftE]
    have := eq_uLiftPath_of_isPath _ _ _ hpath
    rw [hproj] at this
    exact this.symm

theorem univProj_liftHom_onV (htriv : Pi1Trivial f) (v : D.V) :
    (univProj Y (f.onV d₀)).onV ((liftHom hconn htriv).onV v) = f.onV v := endV_liftV hconn v

theorem univProj_liftHom_onE (htriv : Pi1Trivial f) (e : D.E) :
    (univProj Y (f.onV d₀)).onE ((liftHom hconn htriv).onE e) = f.onE e := rfl

theorem univProj_liftHom_onF (htriv : Pi1Trivial f) (g : D.F) :
    (univProj Y (f.onV d₀)).onF ((liftHom hconn htriv).onF g) = f.onF g := rfl

theorem liftHom_base (htriv : Pi1Trivial f) :
    (liftHom hconn htriv).onV d₀ = UV.base Y (f.onV d₀) :=
  liftV_eq hconn htriv (m := []) rfl

end

variable {D K Y L : Complex2.{u}}

theorem Pi1Trivial.comp_left {X Z W : Complex2.{u}} {h : Hom X Z} (g : Hom Z W)
    (hh : Pi1Trivial h) : Pi1Trivial (g.comp h) := fun a m hm => by
  have := mapPath_htpy g (hh a m hm)
  rwa [mapPath_comp, mapPath_nil] at this

theorem zeroPi2_pushoutInl {p : Hom D K} (i : Hom D L) (hiV : Function.Injective i.onV)
    (hiE : Function.Injective i.onE) (hiF : Function.Injective i.onF) (hcov : IsCovering p)
    (hD : IsAcyclic D) (hconnD : IsConnected D) (hconnK : IsConnected K)
    (hconnL : IsConnected L) (hpi1 : Pi1Trivial i) :
    ZeroPi2 (pushoutInl p i hiV hiE) := by
  intro x₀ c hc
  obtain ⟨d₀, rfl⟩ := hcov.surjV x₀
  let f := pushoutInl p i hiV hiE
  have htriv : Pi1Trivial (f.comp p) := by
    rw [show f.comp p = (pushoutMap p i hiV hiE hiF).comp i from (pushout_comm p i hiV hiE hiF).symm]
    exact Pi1Trivial.comp_left _ hpi1
  let F : Hom (uCover K (p.onV d₀)) D := coverHom hcov rfl
  let psi : Hom D (uCover (pushoutComplex p i hiV hiE) (f.onV (p.onV d₀))) := liftHom hconnD htriv
  let A := univLift K f (p.onV d₀)
  let B := psi.comp F
  have hq : IsCovering (univProj (pushoutComplex p i hiV hiE) (f.onV (p.onV d₀))) :=
    isCovering_univProj (isConnected_pushoutComplex p i hiV hiE hconnK hconnL d₀)
  have hV := lift_onV_eq (A := A) (B := B) hq isConnected_univCover
    (fun e => by show f.onE e.1.2 = f.onE (p.onE (coverE hcov rfl e)); rw [onE_coverE hcov rfl e])
    (x := UV.base K (p.onV d₀))
    (by show UV.mk (mapPathFrom (p.onV d₀) f ⟨[], rfl⟩) = psi.onV (F.onV (UV.base K (p.onV d₀)))
        rw [show F.onV (UV.base K (p.onV d₀)) = d₀ from coverV_base hcov rfl,
          show psi = liftHom hconnD htriv from rfl, liftHom_base hconnD htriv]; rfl)
  have hFeq := lift_onF_eq (A := A) (B := B) hq
    (fun g => by show f.onF g.1.2 = f.onF (p.onF (coverF hcov rfl g)); rw [onF_coverF hcov rfl g]) hV
  have hzero : chain2 F c = 0 := hD.h2 (by
    rw [bdry2_chain2 F c, show bdry2 (uCover K (p.onV d₀)) c = 0 from hc, map_zero, map_zero])
  have hcomp : chain2 A c = chain2 psi (chain2 F c) := by
    show Finsupp.mapDomain A.onF c = Finsupp.mapDomain psi.onF (Finsupp.mapDomain F.onF c)
    rw [← Finsupp.mapDomain_comp]
    exact congrArg (Finsupp.mapDomain · c) (funext hFeq)
  rw [hcomp, hzero, map_zero]
