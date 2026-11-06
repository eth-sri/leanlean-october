import Mathlib.Tactic

import RequestProject.CombCoveringLift
import RequestProject.CombPi2
import RequestProject.MinimalGap

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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb



variable {D K : Complex2.{u}} {p : Hom D K} {x₀ : K.V} {d₀ : D.V}

/-! ### Endpoints of lifted paths -/

variable (p d₀) in
/-- `LiftsTo p d₀ q v`: the edge path `q` of the base lifts to an edge path from `d₀` to `v`. -/
def LiftsTo (q : List (K.E × Bool)) (v : D.V)  :=
  ∃ m : List (D.E × Bool), IsPath D.src D.tgt m d₀ v ∧ mapPath p m = q

variable (hcov : IsCovering p)
  (hd : p.onV d₀ = x₀)
  (q : PathFrom K x₀)
include hd in
include hcov in
theorem exists_liftsTo    :
    ∃ v, LiftsTo p d₀ q.1 v := by
  obtain ⟨m, c, hm, hmap⟩ :=
    exists_liftPathAt hcov q.1 d₀ (endpt K x₀ q.1) (by rw [hd]; exact q.2)
  exact ⟨c, m, hm, hmap⟩

include hcov in
theorem liftsTo_unique  {q : List (K.E × Bool)} {v w : D.V}
    (hv : LiftsTo p d₀ q v) (hw : LiftsTo p d₀ q w) : v = w := by
  obtain ⟨m, hm, hmap⟩ := hv
  obtain ⟨m', hm', hmap'⟩ := hw
  have hmm  := liftPath_unique hcov m m' d₀ v w hm hm' (by rw [hmap, hmap'])
  subst hmm
  exact isPath_endpoint_eq hm hm'

include hd in
include hcov in
/-- The endpoint of a lift only depends on the homotopy class of the path. -/
theorem liftsTo_htpy   {q q' : List (K.E × Bool)}
    {v : D.V} (hv : LiftsTo p d₀ q v) (h : Htpy K x₀ (endpt K x₀ q) q q') :
    LiftsTo p d₀ q' v := by
  obtain ⟨m, hm, hmap⟩ := hv
  have hpath  := isPath_mapPath p hm
  rw [hmap, hd] at hpath
  have hb  := endpt_eq_of_isPath hpath
  rw [hb, ← hd] at h
  obtain ⟨m', hm', hmap', -⟩ := lift_htpy hcov hm (by rw [hmap]; exact h)
  exact ⟨m', hm', hmap'⟩

/-! ### The lift on vertices -/

variable (c : UV K x₀)
include hd in
include hcov in
/-- The lift of the universal cover on vertices: the class of a path from `x₀` goes to the
endpoint of the lift of that path at `d₀`. -/
noncomputable def coverV     :=
  Quotient.liftOn c (fun q => Classical.choose (exists_liftsTo hcov hd q)) (by
    intro q q' hqq'
    exact liftsTo_unique hcov
      (liftsTo_htpy hcov hd (Classical.choose_spec (exists_liftsTo hcov hd q)) hqq')
      (Classical.choose_spec (exists_liftsTo hcov hd q')))

include hd in
include hcov in
theorem coverV_spec    :
    LiftsTo p d₀ q.1 (coverV hcov hd (UV.mk q)) :=
  Classical.choose_spec (exists_liftsTo hcov hd q)

include hd in
include hcov in
theorem coverV_eq   {q : PathFrom K x₀} {v : D.V}
    (h : LiftsTo p d₀ q.1 v) : coverV hcov hd (UV.mk q) = v :=
  liftsTo_unique hcov (coverV_spec hcov hd q) h

include hd in
include hcov in
theorem coverV_base   :
    coverV hcov hd (UV.base K x₀) = d₀ :=
  coverV_eq hcov hd ⟨[], rfl, rfl⟩

include hd in
include hcov in
/-- The lift covers the projection of the universal cover. -/
theorem onV_coverV    :
    p.onV (coverV hcov hd c) = endV c := by
  induction c using UV.ind with
  | h q =>
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      have hpath  :=
        isPath_mapPath p hm
      rw [hmap, hd] at hpath
      exact (endpt_eq_of_isPath hpath).symm

include hd in
include hcov in
/-- Extending a class by an oriented edge moves the lift along the lifted edge. -/
theorem coverV_extend   {c : UV K x₀}
    {eb : K.E × Bool} (h : endV c = germSrc K.src K.tgt eb) {x : D.E × Bool}
    (hx1 : germSrc D.src D.tgt x = coverV hcov hd c) (hx2 : (p.onE x.1, x.2) = eb) :
    coverV hcov hd (extend eb c) = germTgt D.src D.tgt x := by
  induction c using UV.ind with
  | h q =>
      have h'  := h
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      rw [extend_mk]
      refine coverV_eq hcov hd ⟨m ++ [x], hm.append ⟨hx1.symm, rfl⟩, ?_⟩
      rw [extendP_pos h', mapPath_append, hmap]
      show q.1 ++ [(p.onE x.1, x.2)] = q.1 ++ [eb]
      rw [hx2]

/-! ### The lift on edges -/

variable (ce : UE K x₀)
include hd in
include hcov in
theorem coverE_cond    :
    germSrc K.src K.tgt (ce.1.2, true) = p.onV (coverV hcov hd ce.1.1) := by
  rw [onV_coverV]
  exact ce.2.symm

include hd in
include hcov in
/-- The lift, at the image of its initial vertex, of the oriented edge underlying an edge of
the universal cover. -/
noncomputable def coverGerm     :=
  Classical.choose (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))

include hd in
include hcov in
theorem coverGerm_spec    :
    germSrc D.src D.tgt (coverGerm hcov hd ce) = coverV hcov hd ce.1.1 ∧
      (p.onE (coverGerm hcov hd ce).1, (coverGerm hcov hd ce).2) = (ce.1.2, true) :=
  (Classical.choose_spec
    (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))).1

include hd in
include hcov in
theorem coverGerm_snd    :
    (coverGerm hcov hd ce).2 = true :=
  congrArg Prod.snd (coverGerm_spec hcov hd ce).2

include hd in
include hcov in
/-- The lift of the universal cover on edges. -/
noncomputable def coverE     :=
  (coverGerm hcov hd ce).1

include hd in
include hcov in
theorem onE_coverE    :
    p.onE (coverE hcov hd ce) = ce.1.2 :=
  congrArg Prod.fst (coverGerm_spec hcov hd ce).2

include hd in
include hcov in
theorem coverGerm_eq    :
    coverGerm hcov hd ce = (coverE hcov hd ce, true) := by
  rw [coverE, ← coverGerm_snd hcov hd ce]

include hd in
include hcov in
theorem src_coverE    :
    D.src (coverE hcov hd ce) = coverV hcov hd ce.1.1 := by
  have h := (coverGerm_spec hcov hd ce).1
  rwa [coverGerm_eq hcov hd ce, germSrc_true] at h

include hd in
include hcov in
theorem tgt_coverE    :
    D.tgt (coverE hcov hd ce) = coverV hcov hd (extend (ce.1.2, true) ce.1.1) := by
  have hcond  := ce.2
  have h := coverV_extend hcov hd (c := ce.1.1) (eb := (ce.1.2, true)) hcond
    (x := coverGerm hcov hd ce) (coverGerm_spec hcov hd ce).1 (coverGerm_spec hcov hd ce).2
  rw [h, coverGerm_eq hcov hd ce, germTgt_true]

/-! ### The lift on two-cells -/

variable (cf : UF K x₀)
include hd in
include hcov in
theorem coverF_cond    :
    K.base cf.1.2 = p.onV (coverV hcov hd cf.1.1) := by
  rw [onV_coverV]
  exact cf.2.symm

include hd in
include hcov in
/-- The lift of the universal cover on two-cells. -/
noncomputable def coverF     :=
  Classical.choose (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))

include hd in
include hcov in
theorem onF_coverF    :
    p.onF (coverF hcov hd cf) = cf.1.2 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.1

include hd in
include hcov in
theorem base_coverF    :
    D.base (coverF hcov hd cf) = coverV hcov hd cf.1.1 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.2

/-! ### Paths -/

variable (L : List (UE K x₀ × Bool))
include hd in
include hcov in
/-- The image of an edge path of the universal cover. -/
noncomputable def mapUP     :=
  L.map (fun x => (coverE hcov hd x.1, x.2))

variable (x : UE K x₀ × Bool)
include hd in
include hcov in
theorem germSrc_mapUP    :
    germSrc D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germSrc (uCover K x₀).src (uCover K x₀).tgt x) := by
  obtain ⟨ce, b⟩ := x
  cases b with
  | true => exact src_coverE hcov hd ce
  | false => exact tgt_coverE hcov hd ce

include hd in
include hcov in
theorem germTgt_mapUP    :
    germTgt D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germTgt (uCover K x₀).src (uCover K x₀).tgt x) := by
  obtain ⟨ce, b⟩ := x
  cases b with
  | true => exact tgt_coverE hcov hd ce
  | false => exact src_coverE hcov hd ce

include hd in
include hcov in
theorem isPath_mapUP   :
    ∀ (L : List (UE K x₀ × Bool)) (a b : UV K x₀),
      IsPath (uCover K x₀).src (uCover K x₀).tgt L a b →
        IsPath D.src D.tgt (mapUP hcov hd L) (coverV hcov hd a) (coverV hcov hd b) := by
  intro L
  induction L with
  | nil => intro a b h; exact congrArg (coverV hcov hd) h
  | cons x L ih =>
      intro a b h
      refine ⟨?_, ?_⟩
      · rw [germSrc_mapUP hcov hd x, h.1]
      aesop (add simp [FiniteChains.Comb.germTgt_mapUP])

include hd in
include hcov in
theorem mapPath_mapUP    :
    mapPath p (mapUP hcov hd L) = mapPath (univProj K x₀) L := by
  simp only [mapPath, mapUP, List.map_map, Function.comp_def, onE_coverE]
  rfl

/-! ### The cellular lift -/

include hd in
include hcov in
/-- **The universal cover maps to every covering.**  The lift of `univProj : uCover K x₀ → K`
along the covering `p : D → K` determined by the choice of a vertex `d₀` over `x₀`. -/
noncomputable def coverHom   :
    Hom (uCover K x₀) D where
  onV := coverV hcov hd
  onE := coverE hcov hd
  onF := coverF hcov hd
  src_onE := fun ce => src_coverE hcov hd ce
  tgt_onE := fun ce => tgt_coverE hcov hd ce
  base_onF := fun cf => base_coverF hcov hd cf
  att_onF := fun cf => by
    have hloop := uAtt_isLoop (X := K) (x₀ := x₀) cf
    have hA  := isPath_mapUP hcov hd _ _ _ hloop
    have hproj : mapPath p (mapUP hcov hd (uAtt cf)) = K.att (p.onF (coverF hcov hd cf)) := by
      rw [mapPath_mapUP, onF_coverF]
      exact ((univProj K x₀).att_onF cf).symm
    exact (eq_att_of_lift hcov hA (base_coverF hcov hd cf) hproj).symm

/-! ### Acyclic covers force the Cockcroft property -/

end FiniteChains.Comb

