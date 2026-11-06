module

public import RequestProject.CombCoveringLift
public import RequestProject.CombPi2
public import RequestProject.ComponentComplex
public import RequestProject.TreeChainTopological
public import RequestProject.CombData
public import RequestProject.Pigeonhole
public import RequestProject.SubgroupCompactness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb

universe u

variable {D K : Complex2.{u}} {p : Hom D K} {x₀ : K.V} {d₀ : D.V}

variable (p d₀) in
def LiftsTo (q : List (K.E × Bool)) (v : D.V) : Prop :=
  ∃ m : List (D.E × Bool), IsPath D.src D.tgt m d₀ v ∧ mapPath p m = q

theorem exists_liftsTo (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    ∃ v, LiftsTo p d₀ q.1 v :=
  let ⟨m, c, hm, hmap⟩ := exists_liftPathAt hcov q.1 d₀ (endpt K x₀ q.1) (hd.symm ▸ q.2)
  ⟨c, m, hm, hmap⟩

theorem liftsTo_unique (hcov : IsCovering p) {q : List (K.E × Bool)} {v w : D.V}
    (hv : LiftsTo p d₀ q v) (hw : LiftsTo p d₀ q w) : v = w := by
  obtain ⟨m, hm, hmap⟩ := hv; obtain ⟨m', hm', hmap'⟩ := hw
  cases liftPath_unique hcov m m' d₀ v w hm hm' (hmap.trans hmap'.symm)
  exact isPath_endpoint_eq hm hm'

def coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) : D.V :=
  Quotient.liftOn c (fun q => Classical.choose (exists_liftsTo hcov hd q)) fun q q' hqq' => by
    obtain ⟨m, hm, hmap⟩ := Classical.choose_spec (exists_liftsTo hcov hd q)
    generalize Classical.choose (exists_liftsTo hcov hd q) = v at hm
    change Htpy K x₀ (endpt K x₀ q.1) q.1 q'.1 at hqq'
    have hpath := isPath_mapPath p hm
    rw [hmap, hd] at hpath
    have hqq'' : Htpy K (p.onV d₀) (p.onV v) (mapPath p m) q'.1 := by
      rw [hd, hmap, ← endpt_eq_of_isPath hpath]; exact hqq'
    obtain ⟨m', hm', hmap', -⟩ := lift_htpy hcov hm hqq''
    exact liftsTo_unique hcov ⟨m', hm', hmap'⟩ (Classical.choose_spec (exists_liftsTo hcov hd q'))

theorem coverV_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    LiftsTo p d₀ q.1 (coverV hcov hd (UV.mk q)) :=
  Classical.choose_spec (exists_liftsTo hcov hd q)

theorem coverV_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q : PathFrom K x₀} {v : D.V}
    (h : LiftsTo p d₀ q.1 v) : coverV hcov hd (UV.mk q) = v :=
  liftsTo_unique hcov (coverV_spec hcov hd q) h

theorem coverV_base (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    coverV hcov hd (UV.base K x₀) = d₀ :=
  coverV_eq hcov hd ⟨[], rfl, rfl⟩

theorem onV_coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) :
    p.onV (coverV hcov hd c) = endV c := by
  induction c using UV.ind with | h q =>
  obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
  have hpath := isPath_mapPath p hm
  rw [hmap, hd] at hpath
  exact (endpt_eq_of_isPath hpath).symm

theorem coverE_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc K.src K.tgt (ce.1.2, true) = p.onV (coverV hcov hd ce.1.1) := by
  rw [onV_coverV]; exact ce.2.symm

def coverGerm (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) : D.E × Bool :=
  Classical.choose (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))

theorem coverGerm_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc D.src D.tgt (coverGerm hcov hd ce) = coverV hcov hd ce.1.1 ∧
      (p.onE (coverGerm hcov hd ce).1, (coverGerm hcov hd ce).2) = (ce.1.2, true) :=
  (Classical.choose_spec (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))).1

def coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) : D.E :=
  (coverGerm hcov hd ce).1

theorem onE_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    p.onE (coverE hcov hd ce) = ce.1.2 :=
  congrArg Prod.fst (coverGerm_spec hcov hd ce).2

theorem coverGerm_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    coverGerm hcov hd ce = (coverE hcov hd ce, true) := by
  have hs : (coverGerm hcov hd ce).2 = true := congrArg Prod.snd (coverGerm_spec hcov hd ce).2
  rw [coverE, ← hs]

theorem src_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.src (coverE hcov hd ce) = coverV hcov hd ce.1.1 := by
  have h := (coverGerm_spec hcov hd ce).1
  rwa [coverGerm_eq hcov hd ce, germSrc_true] at h

theorem coverV_extend (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {c : UV K x₀}
    {eb : K.E × Bool} (h : endV c = germSrc K.src K.tgt eb) {x : D.E × Bool}
    (hx1 : germSrc D.src D.tgt x = coverV hcov hd c) (hx2 : (p.onE x.1, x.2) = eb) :
    coverV hcov hd (extend eb c) = germTgt D.src D.tgt x := by
  induction c using UV.ind with | h q =>
  obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
  rw [extend_mk]
  refine coverV_eq hcov hd ⟨m ++ [x], hm.append ⟨hx1.symm, rfl⟩, ?_⟩
  rw [extendP_pos (h : endpt K x₀ q.1 = germSrc K.src K.tgt eb), mapPath_append, hmap]
  exact congrArg (q.1 ++ [·]) hx2

theorem tgt_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.tgt (coverE hcov hd ce) = coverV hcov hd (extend (ce.1.2, true) ce.1.1) := by
  rw [coverV_extend hcov hd ce.2 (coverGerm_spec hcov hd ce).1 (coverGerm_spec hcov hd ce).2,
    coverGerm_eq hcov hd ce, germTgt_true]

theorem coverF_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    K.base cf.1.2 = p.onV (coverV hcov hd cf.1.1) := by
  rw [onV_coverV]; exact cf.2.symm

def coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) : D.F :=
  Classical.choose (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))

theorem onF_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    p.onF (coverF hcov hd cf) = cf.1.2 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.1

theorem base_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    D.base (coverF hcov hd cf) = coverV hcov hd cf.1.1 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.2

theorem isPath_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    ∀ (L : List (UE K x₀ × Bool)) (a b : UV K x₀),
      IsPath (uCover K x₀).src (uCover K x₀).tgt L a b →
        IsPath D.src D.tgt (L.map fun x => (coverE hcov hd x.1, x.2))
          (coverV hcov hd a) (coverV hcov hd b)
  | [], _, _, h => congrArg (coverV hcov hd) h
  | ⟨ce, b⟩ :: L, a, c, ⟨h1, h2⟩ => by
      have hs : germSrc D.src D.tgt (coverE hcov hd ce, b) =
          coverV hcov hd (germSrc (uCover K x₀).src (uCover K x₀).tgt (ce, b)) := by
        cases b <;> [exact tgt_coverE hcov hd ce; exact src_coverE hcov hd ce]
      have ht : germTgt D.src D.tgt (coverE hcov hd ce, b) =
          coverV hcov hd (germTgt (uCover K x₀).src (uCover K x₀).tgt (ce, b)) := by
        cases b <;> [exact src_coverE hcov hd ce; exact tgt_coverE hcov hd ce]
      exact ⟨(hs.trans (congrArg (coverV hcov hd) h1.symm)).symm, ht.symm ▸ isPath_mapUP hcov hd L _ c h2⟩

def coverHom (hcov : IsCovering p) (hd : p.onV d₀ = x₀) : Hom (uCover K x₀) D where
  onV := coverV hcov hd
  onE := coverE hcov hd
  onF := coverF hcov hd
  src_onE := src_coverE hcov hd
  tgt_onE := tgt_coverE hcov hd
  base_onF := base_coverF hcov hd
  att_onF cf := by
    have hA := isPath_mapUP hcov hd _ _ _ (uAtt_isLoop (X := K) (x₀ := x₀) cf)
    have hproj : mapPath p ((uAtt cf).map fun x => (coverE hcov hd x.1, x.2)) =
        K.att (p.onF (coverF hcov hd cf)) := by
      rw [onF_coverF]
      exact (by simp only [mapPath, List.map_map, Function.comp_def, onE_coverE]; rfl :
        mapPath p ((uAtt cf).map fun x => (coverE hcov hd x.1, x.2)) =
          mapPath (univProj K x₀) (uAtt cf)).trans ((univProj K x₀).att_onF cf).symm
    exact (liftPath_unique hcov _ _ _ _ _ hA (base_coverF hcov hd cf ▸ D.att_isLoop (coverF hcov hd cf))
      (hproj.trans (p.att_onF _))).symm
