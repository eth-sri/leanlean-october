import RequestProject.CombData
import RequestProject.Tac
noncomputable section


/-!
# The connected component of a two-complex, and `π₂`

Condition (1) of Theorem A speaks of chains `K ⊂ X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes.  The
machinery of Section 2 (spanning trees, presentations, Fox matrices) needs the stages to be
*connected*, and up to now this was an extra hypothesis of the formalised implication
`(1) ⇒ (2)`.  This file removes it: a stage may be replaced by the connected component of the
image of `K`, and nothing is lost, because the inclusion of a component induces an injection
of universal covers, hence carries the condition "zero on `π₂`" along.

* `FiniteChains.Comb.Reach` — the vertex is joined to the base vertex by an edge path;
* `FiniteChains.Comb.component` — the connected component of `x₀`: the subcomplex of all
  cells reachable from `x₀`;
* `FiniteChains.Comb.componentIncl` — its inclusion into the ambient complex, injective on
  cells of every dimension;
* `FiniteChains.Comb.Hom.toComponent` — the corestriction of a cellular map whose image is
  reachable;
* `FiniteChains.Comb.htpy_liftGerms` — a homotopy inside the ambient complex between edge
  paths issued from a reachable vertex already takes place inside the component;
* `FiniteChains.Comb.univLiftV_componentIncl_injective` — consequently the inclusion of the
  component induces an injection of universal covers;
* `FiniteChains.Comb.zeroPi2_toComponent` and `FiniteChains.Comb.zeroPi2_comp_right` — being
  zero on `π₂` is inherited by the corestriction to a component and by precomposition.
-/

bwd

namespace FiniteChains.Comb

universe u

variable {A X Y Z : Complex2.{u}}

/-! ### Reachable cells -/

/-- `Reach X x₀ v` : the vertex `v` is joined to `x₀` by an edge path. -/
def Reach (X : Complex2.{u}) (x₀ v : X.V) := ∃ p, IsPathX X p x₀ v

theorem reach_self X x₀ : Reach X x₀ x₀ := by tauto

theorem Reach.trans_path (h : Reach X x₀ a) {p}
    (hp : IsPathX X p a b) : Reach X x₀ b := by
  cases' h with q hq
  exact ⟨q ++ p, hq.append hp⟩


theorem Reach.tgt_of_src (h : Reach X x₀ (X.src e)) :
    Reach X x₀ (X.tgt e) :=
  h.trans_path (p := [(e, true)]) ⟨rfl, rfl⟩

theorem Reach.src_of_tgt (h : Reach X x₀ (X.tgt e)) :
    Reach X x₀ (X.src e) :=
  h.trans_path (p := [(e, false)]) ⟨rfl, rfl⟩

theorem Reach.src_of_germSrc
    (h : Reach X x₀ (gSrcX X eb)) : Reach X x₀ (X.src eb.1) := by
  cases' eb with e b
  cases b with
  | true => exact h
  | false => exact h.src_of_tgt

theorem Reach.germSrc_of_src
    (h : Reach X x₀ (X.src eb.1)) : Reach X x₀ (gSrcX X eb) := by
  cases' eb with e b
  cases b with
  | true => exact h
  | false => exact h.tgt_of_src

/-- Every edge of a path issued from a reachable vertex is reachable. -/
theorem reach_of_mem_path {x₀ : X.V} :
    ∀ {l : List (X.E × Bool)} {a b : X.V}, IsPathX X l a b → Reach X x₀ a →
      ∀ eb ∈ l, Reach X x₀ (X.src eb.1)
  | [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | eb :: t, a, b, hl, ha, eb', hm => by
      have ha' := hl.1 ▸ ha
      have htail :=
        ha'.trans_path (p := [eb]) ⟨rfl, rfl⟩
      rcases List.mem_cons.mp hm with h | h
      · subst h; exact ha'.src_of_germSrc
      · exact reach_of_mem_path hl.2 htail eb' h

/-! ### The cells of the component -/

variable (X) in
/-- The vertices of the component of `x₀`. -/
def CV (x₀ : X.V) : Type u := {v : X.V // Reach X x₀ v}

variable (X) in
/-- The edges of the component of `x₀`. -/
def CE (x₀ : X.V) : Type u := {e : X.E // Reach X x₀ (X.src e)}

variable (X) in
/-- The two-cells of the component of `x₀`. -/
def CF (x₀ : X.V) : Type u := {f : X.F // Reach X x₀ (X.base f)}

variable {x₀ : X.V}

/-- The initial vertex of an edge of the component. -/
def cSrc (e : CE X x₀) : CV X x₀ := ⟨X.src e.1, e.2⟩

/-- The terminal vertex of an edge of the component. -/
def cTgt (e : CE X x₀) : CV X x₀ := ⟨X.tgt e.1, e.2.tgt_of_src⟩

open Classical in
/-- The list of oriented edges of the component carried by a list of oriented edges of the
ambient complex: unreachable edges are dropped (they never occur in the lists we lift). -/
def liftGerms (X : Complex2.{u}) (x₀ : X.V) (l : List (X.E × Bool)) :
    List (CE X x₀ × Bool) :=
  l.filterMap fun eb => if h : Reach X x₀ (X.src eb.1) then some (⟨eb.1, h⟩, eb.2) else none


@[simp] theorem liftGerms_append X x₀ l l' :
    liftGerms X x₀ (l ++ l') = liftGerms X x₀ l ++ liftGerms X x₀ l' := by
  simp [liftGerms, List.filterMap_append]

theorem liftGerms_cons h
    l :
    liftGerms X x₀ (eb :: l) = ((⟨eb.1, h⟩ : CE X x₀), eb.2) :: liftGerms X x₀ l := by
  classical
  simp [liftGerms, h]

/-- The forgetful map on oriented edges of the component. -/
def cForget (eb : CE X x₀ × Bool) := (eb.1.1, eb.2)

@[simp] theorem liftGerms_map_cForget L :
    liftGerms X x₀ (L.map cForget) = L := by
  induction L with
  | nil => rfl
  | cons eb L ih =>
      rw [List.map_cons, liftGerms_cons (eb := cForget eb) eb.1.2, ih]
      rfl

theorem map_cForget_liftGerms
    (h : ∀ eb ∈ l, Reach X x₀ (X.src eb.1)) :
    (liftGerms X x₀ l).map cForget = l := by
  induction l with
  | nil => rfl
  | cons eb l ih =>
      rw [liftGerms_cons (h eb List.mem_cons_self), List.map_cons,
        ih (by simp_all)]
      rfl

@[simp] theorem cGermSrc (eb : CE X x₀ × Bool) :
    germSrc cSrc cTgt eb = ⟨gSrcX X (cForget eb), (eb.1.2).germSrc_of_src⟩ := by
  cases' eb with e b
  cases b <;> rfl

@[simp] theorem cGermTgt (eb : CE X x₀ × Bool) :
    germTgt cSrc cTgt eb = ⟨gTgtX X (cForget eb), by
      cases' eb with e b
      cases b
      · exact e.2
      · exact e.2.tgt_of_src⟩ := by
  cases' eb with e b
  cases b <;> rfl

/-- A path of the ambient complex issued from a reachable vertex lifts to a path of the
component. -/
theorem isPath_liftGerms :
    ∀ {l : List (X.E × Bool)} {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b),
      IsPathX X l a b →
        IsPath (cSrc (X := X) (x₀ := x₀)) cTgt (liftGerms X x₀ l) ⟨a, ha⟩ ⟨b, hb⟩
  | [], a, b, ha, hb, hl => by
      aesop
  | eb :: t, a, b, ha, hb, hl => by
      have hsrc := (hl.1 ▸ ha).src_of_germSrc
      have htgt :=
        (hl.1 ▸ ha).trans_path (p := [eb]) ⟨rfl, rfl⟩
      rw [liftGerms_cons hsrc]
      refine ⟨?_, ?_⟩
      · aesop
      · have := isPath_liftGerms htgt hb hl.2
        aesop

/-! ### The component -/

variable (X) in
/-- **The connected component** of a vertex: the subcomplex of all cells reachable from
`x₀`. -/
def component (x₀ : X.V) : Complex2.{u} where
  V := CV X x₀
  E := CE X x₀
  F := CF X x₀
  src := cSrc
  tgt := cTgt
  base f := ⟨X.base f.1, f.2⟩
  att f := liftGerms X x₀ (X.att f.1)
  att_isLoop f := isPath_liftGerms f.2 f.2 (X.att_isLoop f.1)


instance (x₀ : X.V) [Finite X.E] : Finite (component X x₀).E := by
  show Finite (CE X x₀); unfold CE; infer_instance

instance (x₀ : X.V) [Finite X.F] : Finite (component X x₀).F := by
  show Finite (CF X x₀); unfold CF; infer_instance

/-- The component is connected. -/
theorem component_isConnected x₀ : IsConnected (component X x₀) := by
  rintro ⟨a, p, hp⟩ ⟨b, q, hq⟩
  refine ⟨liftGerms X x₀ (revPath p ++ q), ?_⟩
  exact isPath_liftGerms _ _ ((isPath_revPath hp).append hq)

variable (X) in
/-- The inclusion of the component into the complex. -/
def componentIncl (x₀ : X.V) : Hom (component X x₀) X where
  onV := Subtype.val
  onE := Subtype.val
  onF := Subtype.val
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    refine (map_cForget_liftGerms ?_).symm
    exact reach_of_mem_path (X.att_isLoop f.1) f.2




theorem componentIncl_injective_onF x₀ :
    Function.Injective (componentIncl X x₀).onF := fun _ _ h => Subtype.ext h

/-! ### Corestriction of a cellular map to a component -/

/-- Two cellular maps agreeing on cells of every dimension are equal. -/
theorem Hom.ext' {f g : Hom X Y} (hV : f.onV = g.onV) (hE : f.onE = g.onE)
    (hF : f.onF = g.onF) : f = g := by
  cases f; simp_all



/-! ### Homotopies take place inside the component -/

/-- An elementary homotopy of the ambient complex between paths issued from a reachable
vertex lifts to the component. -/
theorem step_liftGerms ha hb
    {l l'} (hstep : Step X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hPl := isPath_liftGerms ha hb hl
  have hPl' := isPath_liftGerms ha hb hl'
  rcases hc with ⟨p, q, eb, hlEq, hl'Eq⟩ | ⟨p, q, f, hlEq, hl'Eq⟩
  · have hmem : eb ∈ l := by
      simp_all
    have hsrc := reach_of_mem_path hl ha eb hmem
    refine Htpy.of_step ⟨hPl, hPl', Or.inl ⟨liftGerms X x₀ p, liftGerms X x₀ q,
      (⟨eb.1, hsrc⟩, eb.2), ?_, ?_⟩⟩
    · rw [hlEq, liftGerms_append, liftGerms_cons hsrc,
        liftGerms_cons (eb := revGerm eb) hsrc]
      rfl
    simp_all
  · by_cases hatt : X.att f = []
    · have : liftGerms X x₀ l = liftGerms X x₀ l' := by
        simp_all
      rw [this]
      exact Htpy.refl _
    · obtain ⟨eb, t, hsplit⟩ : ∃ eb t, X.att f = eb :: t := by
        cases hx : X.att f <;> simp_all
      have hmem : eb ∈ l := by
        simp_all
      have hsrc := reach_of_mem_path hl ha eb hmem
      have hbase : Reach X x₀ (X.base f) := by
        have hloop := X.att_isLoop f
        rw [hsplit] at hloop
        rw [hloop.1]
        exact hsrc.germSrc_of_src
      refine Htpy.of_step ⟨hPl, hPl', Or.inr ⟨liftGerms X x₀ p, liftGerms X x₀ q,
        ⟨f, hbase⟩, ?_, ?_⟩⟩
      · rw [hlEq, liftGerms_append, liftGerms_append]
        rfl
      simp_all

/-- **A homotopy of the ambient complex between paths issued from a reachable vertex already
takes place inside the component.** -/
theorem htpy_liftGerms ha hb
    {l l'} (h : Htpy X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep with hs | hs
      · exact step_liftGerms ha hb hs
      · exact (step_liftGerms ha hb hs).symm

/-! ### The universal cover of a component -/

theorem mapPath_componentIncl x₀ l :
    mapPath (componentIncl X x₀) l = l.map cForget := rfl

/-! ### Functoriality of the lift to universal covers -/

theorem univLiftV_comp (g : Hom Y Z) f x₀ (c : UV X x₀) :
    univLiftV (f.onV x₀) g (univLiftV x₀ f c) = univLiftV x₀ (g.comp f) c := by
  induction c using UV.ind with
  | h p =>
      refine Quotient.sound ?_
      have hlist : mapPath g (mapPath f p.1) = mapPath (g.comp f) p.1 := by
        simp only [mapPath, List.map_map]
        rfl
      show Htpy Z (g.onV (f.onV x₀)) _ (mapPath g (mapPath f p.1)) (mapPath (g.comp f) p.1)
      rw [hlist]
      exact Htpy.refl _

theorem univLiftF_comp (g : Hom Y Z) f x₀ (F : UF X x₀) :
    univLiftF (f.onV x₀) g (univLiftF x₀ f F) = univLiftF x₀ (g.comp f) F :=
  Subtype.ext (Prod.ext (univLiftV_comp g f x₀ F.1.1) rfl)

/-! ### Zero on `π₂` passes to components -/

/-- **Precomposition preserves being zero on `π₂`.** -/
theorem zeroPi2_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 g) :
    ZeroPi2 (g.comp f) := by
  intro x₀ c hc
  have hcycle :=
    mem_pi2_chain2_univLift f hc
  have hg := hz _ _ hcycle
  have hfun : ∀ F : UF X x₀, (univLift Y g _).onF ((univLift X f x₀).onF F)
      = (univLift X (g.comp f) x₀).onF F := (univLiftF_comp g f x₀)
  have : Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c
      = Finsupp.mapDomain (univLift Y g _).onF
        (Finsupp.mapDomain (univLift X f x₀).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    simp_all
  simp_all
