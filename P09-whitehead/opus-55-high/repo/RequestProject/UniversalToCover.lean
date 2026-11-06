import RequestProject.CombCoveringLift
import RequestProject.CombPi2
import RequestProject.MinimalGap
import RequestProject.Tac
noncomputable section


/-!
# The universal cover maps to every covering, and acyclic covers force the Cockcroft property

Let `p : D → K` be a combinatorial covering and let `d₀` be a vertex of `D` over the base
vertex `x₀` of `K`.  The universal cover of `K` is built in
`RequestProject/CombUniversalCover.lean` out of homotopy classes of edge paths issued from
`x₀`; sending such a class to the endpoint of the lift of any of its representatives at `d₀`
is well defined by the homotopy lifting property of
`RequestProject/CombCoveringLift.lean`, and extends to a cellular map

`FiniteChains.Comb.coverHom : Hom (uCover K x₀) D`  with  `p ∘ coverHom = univProj`.

* `FiniteChains.Comb.coverV`, `coverE`, `coverF` — the map on vertices, edges and two-cells;
* `FiniteChains.Comb.onV_coverV`, `onE_coverE`, `onF_coverF` — the lift covers the projection
  of the universal cover;
* `FiniteChains.Comb.isCockcroft_of_isAcyclicCover` — **a two-complex with a connected acyclic
  regular cover is Cockcroft**: a spherical class of `K` lifts to a two-cycle of `D`, which
  vanishes because `D` is acyclic.  This is the step "`(2)` implies that `K` is Cockcroft" of
  the paper, and it was previously carried as a hypothesis.
-/

bwd

namespace FiniteChains.Comb

universe u

variable {D K : Complex2.{u}} {p : Hom D K} {x₀ : K.V} {d₀ : D.V}

/-! ### Endpoints of lifted paths -/

variable (p d₀) in
/-- `LiftsTo p d₀ q v`: the edge path `q` of the base lifts to an edge path from `d₀` to `v`. -/
def LiftsTo (q : List (K.E × Bool)) (v : D.V) : Prop :=
  ∃ m : List (D.E × Bool), IsPathX D m d₀ v ∧ mapPath p m = q

theorem exists_liftsTo (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    ∃ v, LiftsTo p d₀ q.1 v := by
  obtain ⟨m, c, hm, hmap⟩ :=
    exists_liftPathAt hcov q.1 d₀ (endpt K x₀ q.1) (by grind)
  tauto

theorem liftsTo_unique (hcov : IsCovering p) {q} {v w}
    (hv : LiftsTo p d₀ q v) (hw : LiftsTo p d₀ q w) : v = w := by
  obtain ⟨m, hm, hmap⟩ := hv
  obtain ⟨m', hm', hmap'⟩ := hw
  have hmm := liftPath_unique hcov m m' d₀ v w hm hm' (by simp_all)
  subst hmm
  exact isPath_endpoint_eq hm hm'

/-- The endpoint of a lift only depends on the homotopy class of the path. -/
theorem liftsTo_htpy (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q q'}
    {v} (hv : LiftsTo p d₀ q v) (h : Htpy K x₀ (endpt K x₀ q) q q') :
    LiftsTo p d₀ q' v := by
  obtain ⟨m, hm, hmap⟩ := hv
  have hpath := isPath_mapPath p hm
  rw [hmap, hd] at hpath
  have hb := endpt_eq_of_isPath hpath
  rw [hb, ← hd] at h
  obtain ⟨m', hm', hmap', -⟩ := lift_htpy hcov hm (by rw [hmap]; exact h)
  tauto

/-! ### The lift on vertices -/

/-- The lift of the universal cover on vertices: the class of a path from `x₀` goes to the
endpoint of the lift of that path at `d₀`. -/
def coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) :=
  c.liftOn (fun q => Classical.choose (exists_liftsTo hcov hd q)) (by
    intro q q' hqq'
    exact liftsTo_unique hcov
      (liftsTo_htpy hcov hd (by grind) hqq')
      (by grind))

theorem coverV_spec hcov (hd : p.onV d₀ = x₀) q :
    LiftsTo p d₀ q.1 (coverV hcov hd (UV.mk q)) :=
  Classical.choose_spec _

theorem coverV_eq hcov (hd : p.onV d₀ = x₀) {q} {v}
    (h : LiftsTo p d₀ q.1 v) : coverV hcov hd (UV.mk q) = v :=
  liftsTo_unique hcov (coverV_spec hcov hd q) h

theorem coverV_base hcov (hd : p.onV d₀ = x₀) :
    coverV hcov hd (UV.base K x₀) = d₀ :=
  coverV_eq hcov hd (by tauto)

/-- The lift covers the projection of the universal cover. -/
theorem onV_coverV hcov (hd : p.onV d₀ = x₀) c :
    p.onV (coverV hcov hd c) = endV c := by
  induction c using UV.ind with
  | h q =>
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      have hpath :=
        isPath_mapPath p hm
      rw [hmap, hd] at hpath
      exact (endpt_eq_of_isPath hpath).symm

/-- Extending a class by an oriented edge moves the lift along the lifted edge. -/
theorem coverV_extend hcov (hd : p.onV d₀ = x₀) {c}
    {eb} (h : endV c = gSrcX K eb) {x}
    (hx1 : gSrcX D x = coverV hcov hd c) (hx2 : (p.onE x.1, x.2) = eb) :
    coverV hcov hd (extend eb c) = gTgtX D x := by
  induction c using UV.ind with
  | h q =>
      have h' := h
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      refine coverV_eq hcov hd ⟨m ++ [x], hm.append ⟨hx1.symm, rfl⟩, ?_⟩
      rw [extendP_pos h', mapPath_append, hmap]
      aesop

/-! ### The lift on edges -/

theorem coverE_cond hcov (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    gSrcX K (ce.1.2, true) = p.onV (coverV hcov hd ce.1.1) := by
  rw [onV_coverV]
  exact ce.2.symm

/-- The lift, at the image of its initial vertex, of the oriented edge underlying an edge of
the universal cover. -/
def coverGerm (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :=
  Classical.choose (exists_unique_liftGerm hcov _ (coverE_cond hcov hd ce))

theorem coverGerm_spec hcov (hd : p.onV d₀ = x₀) ce :
    gSrcX D (coverGerm hcov hd ce) = coverV hcov hd ce.1.1 ∧
      (p.onE (coverGerm hcov hd ce).1, (coverGerm hcov hd ce).2) = (ce.1.2, true) :=
  (Classical.choose_spec
    (exists_unique_liftGerm hcov _ (coverE_cond hcov hd ce))).1

theorem coverGerm_snd hcov (hd : p.onV d₀ = x₀) ce :
    (coverGerm hcov hd ce).2 = true :=
  congrArg Prod.snd (coverGerm_spec hcov hd ce).2

/-- The lift of the universal cover on edges. -/
def coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :=
  (coverGerm hcov hd ce).1

theorem onE_coverE hcov (hd : p.onV d₀ = x₀) ce :
    p.onE (coverE hcov hd ce) = ce.1.2 :=
  congrArg Prod.fst (coverGerm_spec hcov hd ce).2

theorem coverGerm_eq hcov (hd : p.onV d₀ = x₀) ce :
    coverGerm hcov hd ce = (coverE hcov hd ce, true) := by
  rw [coverE, ← coverGerm_snd hcov hd ce]

theorem src_coverE hcov (hd : p.onV d₀ = x₀) ce :
    D.src (coverE hcov hd ce) = coverV hcov hd ce.1.1 := by
  have h := (coverGerm_spec hcov hd ce).1
  grind [coverGerm_eq hcov hd ce, germSrc_true]

theorem tgt_coverE hcov (hd : p.onV d₀ = x₀) ce :
    D.tgt (coverE hcov hd ce) = coverV hcov hd (extend (ce.1.2, true) ce.1.1) := by
  have hcond := ce.2
  have h := coverV_extend hcov hd (c := ce.1.1) (eb := (ce.1.2, true)) hcond
    (x := coverGerm hcov hd ce) (coverGerm_spec hcov hd ce).1 (coverGerm_spec hcov hd ce).2
  rw [h, coverGerm_eq hcov hd ce, germTgt_true]

/-! ### The lift on two-cells -/

theorem coverF_cond hcov (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    K.base cf.1.2 = p.onV (coverV hcov hd cf.1.1) := by
  grind [onV_coverV]

/-- The lift of the universal cover on two-cells. -/
def coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :=
  Classical.choose (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))

theorem onF_coverF hcov (hd : p.onV d₀ = x₀) cf :
    p.onF (coverF hcov hd cf) = cf.1.2 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.1

theorem base_coverF hcov (hd : p.onV d₀ = x₀) cf :
    D.base (coverF hcov hd cf) = coverV hcov hd cf.1.1 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.2

/-! ### Paths -/

/-- The image of an edge path of the universal cover. -/
def mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (L : List (UE K x₀ × Bool)) :=
  L.map (fun x => (coverE hcov hd x.1, x.2))

theorem germSrc_mapUP hcov (hd : p.onV d₀ = x₀) (x : UE K x₀ × Bool) :
    gSrcX D (coverE hcov hd x.1, x.2)
      = coverV hcov hd (gSrcX (uCover K x₀) x) := by
  cases' x with ce b
  cases b with
  | true => exact src_coverE hcov hd ce
  | false => exact tgt_coverE hcov hd ce

theorem germTgt_mapUP hcov (hd : p.onV d₀ = x₀) (x : UE K x₀ × Bool) :
    gTgtX D (coverE hcov hd x.1, x.2)
      = coverV hcov hd (gTgtX (uCover K x₀) x) := by
  cases' x with ce b
  cases b with
  | true => exact tgt_coverE hcov hd ce
  | false => exact src_coverE hcov hd ce

theorem isPath_mapUP hcov (hd : p.onV d₀ = x₀) :
    ∀ (L : List (UE K x₀ × Bool)) (a b : UV K x₀),
      IsPathX (uCover K x₀) L a b →
        IsPathX D (mapUP hcov hd L) (coverV hcov hd a) (coverV hcov hd b) := by
  intro L
  induction L with
  | nil => tauto
  | cons x L ih =>
      intro a b h
      refine ⟨?_, ?_⟩
      · rw [germSrc_mapUP hcov hd x, h.1]
      · have := ih _ b h.2
        rwa [← germTgt_mapUP hcov hd x] at this

theorem mapPath_mapUP hcov (hd : p.onV d₀ = x₀) L :
    mapPath p (mapUP hcov hd L) = mapPath (univProj K x₀) L := by
  simp only [mapPath, mapUP, List.map_map, Function.comp_def, onE_coverE]
  rfl

/-! ### The cellular lift -/

/-- **The universal cover maps to every covering.**  The lift of `univProj : uCover K x₀ → K`
along the covering `p : D → K` determined by the choice of a vertex `d₀` over `x₀`. -/
def coverHom (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    Hom (uCover K x₀) D where
  onV := coverV hcov hd
  onE := coverE hcov hd
  onF := coverF hcov hd
  src_onE := (src_coverE hcov hd)
  tgt_onE := (tgt_coverE hcov hd)
  base_onF := (base_coverF hcov hd)
  att_onF := fun cf => by
    have hloop := uAtt_isLoop (X := K) (x₀ := x₀) cf
    have hA := isPath_mapUP hcov hd _ _ _ hloop
    have hproj : mapPath p (mapUP hcov hd (uAtt cf)) = K.att (p.onF (coverF hcov hd cf)) := by
      rw [mapPath_mapUP, onF_coverF]
      exact ((univProj K x₀).att_onF cf).symm
    exact (eq_att_of_lift hcov hA (base_coverF hcov hd cf) hproj).symm

/-! ### Acyclic covers force the Cockcroft property -/
