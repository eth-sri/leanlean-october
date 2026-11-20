module

public import RequestProject.UniversalToCover
public import RequestProject.CombPushout
public import RequestProject.DeckChainTransport

@[expose] public section

/-!
# The inclusion of the base into the pushout is zero on `π₂`

This file proves the first of the three homotopy-theoretic assertions of Proposition 3.11
(step 3 of its proof in the paper): *the arrow `K → E₁ = K ∪_p L` is zero on `π₂`.*  The
argument of the paper is: "the map `K → E₁` lifts, after passing to the acyclic cover `D`, to
a map `D → Ẽ₁`; its map on `π₂` factors through `H₂(D) = 0`, and is zero."  Making that
precise in the combinatorial model needs three things, all proved here from scratch.

* `FiniteChains.Comb.lift_onF_eq` (and its companions for vertices and edges) — **uniqueness
  of lifts**: two cellular maps of a connected complex into a covering which have the same
  composite with the covering and agree at one vertex agree everywhere;
* `FiniteChains.Comb.liftHom` — **the lifting criterion**: a cellular map `f : D → Y` of a
  connected complex which kills `π₁` lifts to the universal cover of `Y`, i.e. there is a
  cellular `f̃ : D → Ỹ` with `univProj ∘ f̃ = f` and `f̃ d₀ = ` the base vertex;
* `FiniteChains.Comb.zeroPi2_of_pi1Trivial_comp` — **the homotopy statement**: if `K` has a
  connected acyclic covering `p : D → K` and `f : K → Y` is such that `f ∘ p` kills `π₁`,
  then `f` is zero on `π₂`.  Indeed the lift `K̃ → D` of the universal covering along `p`
  composed with the lift `D → Ỹ` is, by uniqueness of lifts, the lift of `f` itself, and a
  spherical class of `K` already dies in `D` because `D` is acyclic.

Applying this to the cellular pushout of `RequestProject/CombPushout.lean` gives

* `FiniteChains.Comb.zeroPi2_pushoutInl` — for a connected acyclic covering `p : D → K` and a
  connected complex `L ⊇ D` in which `π₁(D)` dies, the inclusion `K ⊆ K ∪_p L` is zero on
  `π₂`;
* `FiniteChains.Comb.zeroPi2_descentChain_zero` — the same statement for the first arrow
  `E₀ = K → E₁` of the descended chain of `RequestProject/PushoutChain.lean`.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Uniqueness of lifts along a covering -/

section Unique

variable {X Z W : Complex2.{u}}

variable {q : Hom Z W} {A B : Hom X Z}

/-- **Uniqueness of lifts, on vertices.**  Two cellular maps of a connected complex into a
covering with the same composite with the covering which agree at one vertex agree on all
vertices. -/
theorem lift_onV_eq (hq : IsCovering q) (hX : IsConnected X)
    (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e)) {x : X.V} (hx : A.onV x = B.onV x) :
    ∀ v, A.onV v = B.onV v := by
  intro v
  obtain ⟨m, hm⟩ := hX x v
  have hA  := isPath_mapPath A hm
  have hB : IsPath Z.src Z.tgt (mapPath B m) (A.onV x) (B.onV v) := by
    rw [hx]; exact isPath_mapPath B hm
  have hmap : mapPath q (mapPath A m) = mapPath q (mapPath B m) := by
    rw [mapPath_comp, mapPath_comp]
    exact mapPath_congr hE m
  have hlists := liftPath_unique hq.uniqueLifts (mapPath A m) (mapPath B m) (A.onV x) _ _ hA hB hmap
  rw [← hlists] at hB
  exact isPath_endpoint_eq hA hB

/-- **Uniqueness of lifts, on edges.** -/
theorem lift_onE_eq (hq : IsCovering q) (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ e, A.onE e = B.onE e := by
  intro e
  have h1 : germSrc Z.src Z.tgt (A.onE e, true) = A.onV (X.src e) := A.src_onE e
  have h2 : germSrc Z.src Z.tgt (B.onE e, true) = A.onV (X.src e) := by
    rw [germSrc_true, B.src_onE e, hV]
  have h3 : (q.onE (A.onE e, true).1, (A.onE e, true).2)
      = (q.onE (B.onE e, true).1, (B.onE e, true).2) := by tauto
  exact congrArg Prod.fst (liftGerm_unique hq.uniqueLifts h1 h2 h3)

/-- **Uniqueness of lifts, on two-cells.** -/
theorem lift_onF_eq (hq : IsCovering q) (hF : ∀ f, q.onF (A.onF f) = q.onF (B.onF f))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ f, A.onF f = B.onF f := by
  intro f
  have hv : W.base (q.onF (A.onF f)) = q.onV (A.onV (X.base f)) := by
    rw [q.base_onF, A.base_onF]
  obtain ⟨g, -, huniq⟩ := exists_unique_liftCell hq.uniqueLifts (q.onF (A.onF f)) hv
  rw [huniq (A.onF f) ⟨rfl, A.base_onF f⟩,
    huniq (B.onF f) ⟨(hF f).symm, by rw [B.base_onF f, hV]⟩]

/-- Lifts of a connected complex with the same projected cells agree once they meet
at a vertex. -/
theorem lift_cells_eq (hq : IsCovering q) (hX : IsConnected X)
    (hE : ∀ e, q.onE (A.onE e) = q.onE (B.onE e))
    (hF : ∀ f, q.onF (A.onF f) = q.onF (B.onF f))
    {x : X.V} (hx : A.onV x = B.onV x) :
    (∀ v, A.onV v = B.onV v) ∧ (∀ e, A.onE e = B.onE e) ∧
      (∀ f, A.onF f = B.onF f) :=
  let hV := lift_onV_eq hq hX hE hx
  ⟨hV, lift_onE_eq hq hE hV, lift_onF_eq hq hF hV⟩

end Unique

/-- Two lifts which meet over the same source fibre differ only by a deck transformation. -/
theorem lifts_identified {D K Y Z : Complex2.{u}} {Q : Type v} [Group Q]
    {p : Hom D K} {a : DeckAction D Q} {q : Hom Y Z} {F G : Hom D Y}
    (hr : IsRegular p a) (hq : IsCovering q) (hD : IsConnected D)
    (hE : ∀ k e, q.onE (F.onE e) = q.onE (G.onE (a.smulE k e)))
    (hF : ∀ k f, q.onF (F.onF f) = q.onF (G.onF (a.smulF k f)))
    {d e : D.V} (he : p.onV d = p.onV e) (hm : F.onV d = G.onV e) :
    ∃ k, F = G.comp (a.cellHom k) := by
  obtain ⟨k, hk, _⟩ := hr.simply_transitive d e he
  have h : F.onV d = (G.comp (a.cellHom k)).onV d := hm.trans (congrArg G.onV hk).symm
  obtain ⟨hv, he, hf⟩ := lift_cells_eq hq hD (hE k) (hF k) h
  exact ⟨k, Hom.ext' (funext hv) (funext he) (funext hf)⟩

/-! ### The lifting criterion -/

section Lift

variable {D Y : Complex2.{u}}

/-- A map which kills `π₁` sends any two paths with the same endpoints to homotopic paths. -/
theorem htpy_mapPath_of_pi1Trivial {f : Hom D Y} (htriv : Pi1Trivial f)
    {m m' : List (D.E × Bool)} {a b : D.V} (hm : IsPath D.src D.tgt m a b)
    (hm' : IsPath D.src D.tgt m' a b) :
    Htpy Y (f.onV a) (f.onV b) (mapPath f m) (mapPath f m') := by
  have hP  := isPath_mapPath f hm
  have hQ  := isPath_mapPath f hm'
  have hQrev  :=
    isPath_revPath hQ
  have h0 : Htpy Y (f.onV a) (f.onV a) (mapPath f m ++ revPath (mapPath f m')) [] := by
    have hloop  :=
      isPath_append_iff.mpr ⟨b, hm, isPath_revPath hm'⟩
    have h := htriv a (m ++ revPath m') hloop
    rwa [mapPath_append, mapPath_revPath] at h
  have hrev  :=
    htpy_revPath_append hQ
  have step1  :=
    Htpy.append_congr hP (isPath_append_iff.mpr ⟨f.onV a, hQrev, hQ⟩) (Htpy.refl _) hrev
  have step2  :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨f.onV b, hP, hQrev⟩) hQ h0 (Htpy.refl _)
  grind [step1.symm.trans]

variable (f : Hom D Y) (hconn : IsConnected D) (d₀ : D.V)

/-- A chosen edge path from the base vertex. -/
noncomputable def cPath (v : D.V) : List (D.E × Bool) := (hconn d₀ v).choose

theorem cPath_isPath (v : D.V) : IsPath D.src D.tgt (cPath hconn d₀ v) d₀ v :=
  (hconn d₀ v).choose_spec

/-- The image of a path issued from `d₀`, as a path of `Y` issued from `f d₀`. -/
def pathFromMap {v : D.V} {m : List (D.E × Bool)} (hm : IsPath D.src D.tgt m d₀ v) :
    PathFrom Y (f.onV d₀) :=
  ⟨mapPath f m, by
    have h := isPath_mapPath f hm
    rw [endpt_eq_of_isPath h]
    exact h⟩

/-- **The lift of a `π₁`-trivial map to the universal cover, on vertices**: send `v` to the
class of the image of any path from `d₀` to `v`. -/
noncomputable def liftV (v : D.V) : UV Y (f.onV d₀) :=
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

theorem liftV_base (htriv : Pi1Trivial f) : liftV f hconn d₀ d₀ = UV.base Y (f.onV d₀) :=
  liftV_eq hconn htriv (m := []) rfl

/-- Extending the lift along an oriented edge. -/
theorem liftV_extend (htriv : Pi1Trivial f) (eb : D.E × Bool) :
    liftV f hconn d₀ (germTgt D.src D.tgt eb)
      = extend (f.onE eb.1, eb.2) (liftV f hconn d₀ (germSrc D.src D.tgt eb)) := by
  set v := germSrc D.src D.tgt eb with hv
  have hm  := cPath_isPath hconn d₀ v
  have hstep  :=
    isPath_append_iff.mpr ⟨v, hm, isPath_single eb⟩
  rw [liftV_eq hconn htriv hstep, liftV_eq hconn htriv hm, extend_mk]
  refine congrArg UV.mk (Subtype.ext ?_)
  have hend : endpt Y (f.onV d₀) (mapPath f (cPath hconn d₀ v))
      = germSrc Y.src Y.tgt (f.onE eb.1, eb.2) := by
    rw [endpt_eq_of_isPath (isPath_mapPath f hm), germSrc_onE f eb]
  show mapPath f (cPath hconn d₀ v ++ [eb])
    = (extendP (f.onE eb.1, eb.2) (pathFromMap f d₀ hm)).1
  rw [extendP_pos hend]
  simp [mapPath, pathFromMap]

variable (f d₀)

/-- The lift of a `π₁`-trivial map to the universal cover, on edges. -/
noncomputable def liftE (e : D.E) : UE Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.src e), f.onE e), by rw [endV_liftV, f.src_onE]⟩

/-- The lift of a `π₁`-trivial map to the universal cover, on two-cells. -/
noncomputable def liftF (g : D.F) : UF Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.base g), f.onF g), by rw [endV_liftV, f.base_onF]⟩

variable {f d₀}

theorem uTgt_liftE (htriv : Pi1Trivial f) (e : D.E) :
    uTgt (liftE f hconn d₀ e) = liftV f hconn d₀ (D.tgt e) :=
  (liftV_extend hconn htriv (e, true)).symm

/-- **The lifting criterion.**  A cellular map of a connected complex which kills `π₁` lifts
to the universal cover of its target. -/
noncomputable def liftHom (htriv : Pi1Trivial f) : Hom D (uCover Y (f.onV d₀)) where
  onV := liftV f hconn d₀
  onE := liftE f hconn d₀
  onF := liftF f hconn d₀
  src_onE := fun _ => rfl
  tgt_onE := fun e => uTgt_liftE hconn htriv e
  base_onF := fun _ => rfl
  att_onF := fun g => by
    change uLiftPath (Y.att (f.onF g)) (liftV f hconn d₀ (D.base g)) = _
    rw [show Y.att (f.onF g) = mapPath f (D.att g) from f.att_onF g]
    exact (map_eq_uLiftPath (liftV f hconn d₀) (liftE f hconn d₀) (fun _ => rfl)
      (uTgt_liftE hconn htriv) (D.att_isLoop g)).symm




theorem liftHom_base (htriv : Pi1Trivial f) :
    (liftHom hconn htriv).onV d₀ = UV.base Y (f.onV d₀) := liftV_base hconn htriv

end Lift

/-! ### Maps that are zero on `π₂` -/

variable {D K Y : Complex2.{u}}

/-- Composing on the left preserves the triviality of the induced map on `π₁`. -/
theorem Pi1Trivial.comp_left {X Z W : Complex2.{u}} {h : Hom X Z} (g : Hom Z W)
    (hh : Pi1Trivial h) : Pi1Trivial (g.comp h) := by
  intro a m hm
  have := mapPath_htpy g (hh a m hm)
  rwa [mapPath_comp, mapPath_nil] at this

/-- **A map of a complex with a connected acyclic cover which kills `π₁` upstairs is zero on
`π₂`.**  This is step 3 of the proof of Proposition 3.11: the composite `D → K → Y` lifts to
the universal cover of `Y`, so the lift `K̃ → Ỹ` factors through the acyclic complex `D`,
where every two-cycle vanishes. -/
theorem zeroPi2_of_pi1Trivial_comp {p : Hom D K} (hcov : IsCovering p) (hD : IsAcyclic D)
    (hconnD : IsConnected D) (hconnY : IsConnected Y) (f : Hom K Y)
    (htriv : Pi1Trivial (f.comp p)) : ZeroPi2 f := by
  intro x₀ c hc
  obtain ⟨d₀, hd⟩ := hcov.surjV x₀
  subst hd
  set F : Hom (uCover K (p.onV d₀)) D := coverHom hcov rfl
  set psi : Hom D (uCover Y (f.onV (p.onV d₀))) := liftHom hconnD htriv with hpsi
  set A : Hom (uCover K (p.onV d₀)) (uCover Y (f.onV (p.onV d₀))) :=
    univLift K f (p.onV d₀)
  set B : Hom (uCover K (p.onV d₀)) (uCover Y (f.onV (p.onV d₀))) := psi.comp F
  have hq : IsCovering (univProj Y (f.onV (p.onV d₀))) := isCovering_univProj hconnY
  have hqE : ∀ e, (univProj Y (f.onV (p.onV d₀))).onE (A.onE e)
      = (univProj Y (f.onV (p.onV d₀))).onE (B.onE e) := by
    intro e
    show f.onE e.1.2 = f.onE (p.onE (coverE hcov rfl e))
    rw [onE_coverE hcov rfl e]
  have hqF : ∀ g, (univProj Y (f.onV (p.onV d₀))).onF (A.onF g)
      = (univProj Y (f.onV (p.onV d₀))).onF (B.onF g) := by
    intro g
    show f.onF g.1.2 = f.onF (p.onF (coverF hcov rfl g))
    rw [onF_coverF hcov rfl g]
  have hbase : A.onV (UV.base K (p.onV d₀)) = B.onV (UV.base K (p.onV d₀)) := by
    have hFbase : F.onV (UV.base K (p.onV d₀)) = d₀ := coverV_base hcov rfl
    show UV.mk (mapPathFrom (p.onV d₀) f ⟨[], rfl⟩) = psi.onV (F.onV (UV.base K (p.onV d₀)))
    rw [hFbase, hpsi, liftHom_base hconnD htriv]
    rfl
  obtain ⟨_, _, hFeq⟩ := lift_cells_eq hq isConnected_univCover hqE hqF hbase
  have hcycle : bdry2 D (chain2 F c) = 0 := by
    rw [bdry2_chain2 F c]
    have h  := hc
    rw [h, map_zero]
  have hzero : chain2 F c = 0 := hD.h2 (by tauto)
  have hcomp : chain2 A c = chain2 psi (chain2 F c) := by
    show Finsupp.mapDomain A.onF c = Finsupp.mapDomain psi.onF (Finsupp.mapDomain F.onF c)
    rw [← Finsupp.mapDomain_comp]
    exact congrArg (fun m => Finsupp.mapDomain m c) (funext hFeq)
  rw [hcomp, hzero, map_zero]

/-! ### Maps out of an acyclic complex -/

/-! ### The inclusion of the base into the cellular pushout -/

variable {L : Complex2.{u}}

/-- **The inclusion `K ⊆ K ∪_p L` is zero on `π₂`.**  Here `p : D → K` is a connected acyclic
covering, `D ⊆ L` with `π₁(D)` dying in `L`, and `L` is connected. -/
theorem zeroPi2_pushoutInl {p : Hom D K} (i : Hom D L) (hiV : Function.Injective i.onV)
    (hiE : Function.Injective i.onE) (hiF : Function.Injective i.onF) (hcov : IsCovering p)
    (hD : IsAcyclic D) (hconnD : IsConnected D) (hconnK : IsConnected K)
    (hconnL : IsConnected L) (hpi1 : Pi1Trivial i) :
    ZeroPi2 (pushoutInl p i hiV hiE) := by
  intro x₀ c hc
  obtain ⟨d₀, -⟩ := hcov.surjV x₀
  have hconnE  :=
    isConnected_pushoutComplex p i hiV hiE hconnK hconnL d₀
  have hcomm  :=
    (pushout_comm p i hiV hiE hiF).symm
  have htriv : Pi1Trivial ((pushoutInl p i hiV hiE).comp p) := by
    rw [hcomm]
    exact Pi1Trivial.comp_left _ hpi1
  exact zeroPi2_of_pi1Trivial_comp hcov hD hconnD hconnE _ htriv x₀ c hc

/-! ### The first arrow of the descended chain -/



end Comb
end FiniteChains
