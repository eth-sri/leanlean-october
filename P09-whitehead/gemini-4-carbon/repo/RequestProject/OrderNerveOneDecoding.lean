module

public import RequestProject.GenusCollapseIteration
public import RequestProject.GenusLoops
public import RequestProject.CylinderPi1Surjective
public import RequestProject.CombPi1
public import RequestProject.PresPosetReading
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas
public import RequestProject.Statement
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section
noncomputable section
section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {K D L : Complex2.{u}}

/-! ### Transport of edge paths along a map of graphs -/

/-- A map of graphs takes edge paths to edge paths. -/
theorem isPath_map {V E V' E' : Type*} {src tgt : E → V} {src' tgt' : E' → V'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q : List (E × Bool)} {a b : V}, IsPath src tgt q a b →
      IsPath src' tgt' (q.map fun eb => (fE eb.1, eb.2)) (fV a) (fV b) := by
  intro q
  induction q with
  | nil => simp
  | cons eb q ih =>
      rintro a b ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨e, s⟩ := eb
        cases s <;> simp [germSrc, hs, ht] at h1 ⊢ <;> exact congrArg fV h1
      · obtain ⟨e, s⟩ := eb
        cases s
        · simpa [germTgt, hs, ht] using ih h2
        · simpa [germTgt, hs, ht] using ih h2

/-! ### The cells of `L` off `D` -/

/-- The vertices of `L` which do not come from `D`. -/
def OffV (i : Hom D L) : Type u := {v : L.V // ∀ d, i.onV d ≠ v}

/-- The edges of `L` which do not come from `D`. -/
def OffE (i : Hom D L) : Type u := {e : L.E // ∀ d, i.onE d ≠ e}

/-- The two-cells of `L` which do not come from `D`. -/
def OffF (i : Hom D L) : Type u := {f : L.F // ∀ d, i.onF d ≠ f}

open Classical in
/-- The vertex map `L → E`: a vertex coming from `D` goes to its image in `K`, any other
vertex survives. -/
def pushV (p : Hom D K) (i : Hom D L) (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then Sum.inl (p.onV h.choose) else Sum.inr ⟨v, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The edge map `L → E`. -/
def pushE (p : Hom D K) (i : Hom D L) (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then Sum.inl (p.onE h.choose) else Sum.inr ⟨e, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The two-cell map `L → E`. -/
def pushF (p : Hom D K) (i : Hom D L) (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then Sum.inl (p.onF h.choose) else Sum.inr ⟨f, fun d hd => h ⟨d, hd⟩⟩

theorem pushV_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onV) (d : D.V) :
    pushV p i (i.onV d) = Sum.inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onE) (d : D.E) :
    pushE p i (i.onE d) = Sum.inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := ⟨d, rfl⟩
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onF) (d : D.F) :
    pushF p i (i.onF d) = Sum.inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := ⟨d, rfl⟩
  rw [pushF, dif_pos h, hi h.choose_spec]

theorem pushV_of_off (p : Hom D K) (i : Hom D L) (v : OffV i) :
    pushV p i v.1 = Sum.inr v := by
  rw [pushV, dif_neg (by rintro ⟨d, hd⟩; exact v.2 d hd)]
  rfl

theorem pushE_of_off (p : Hom D K) (i : Hom D L) (e : OffE i) :
    pushE p i e.1 = Sum.inr e := by
  rw [pushE, dif_neg (by rintro ⟨d, hd⟩; exact e.2 d hd)]
  rfl

theorem pushF_of_off (p : Hom D K) (i : Hom D L) (f : OffF i) :
    pushF p i f.1 = Sum.inr f := by
  rw [pushF, dif_neg (by rintro ⟨d, hd⟩; exact f.2 d hd)]
  rfl

/-! ### The pushout complex -/

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.src e)) (fun e => pushV p i (L.src e.1))

def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.src (p.onE d)) = _
    rw [p.src_onE, i.src_onE, pushV_of_mem p hiV]
  · have he : (⟨e, fun d hd => h ⟨d, hd⟩⟩ : OffE i).1 = e := rfl
    rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiV hiE in
theorem ptgt_pushE (e : L.E) : ptgt p i (pushE p i e) = pushV p i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.tgt (p.onE d)) = _
    rw [p.tgt_onE, i.tgt_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

/-- **The cellular pushout `E = K ∪_p L`.**  Its vertices, edges and two-cells are those of
`K` together with those of `L` which do not come from `D`; a cell of `L` coming from `D` is
identified with its image under `p`. -/
def pushoutComplex : Complex2.{u} where
  V := K.V ⊕ OffV i
  E := K.E ⊕ OffE i
  F := K.F ⊕ OffF i
  src := psrc p i
  tgt := ptgt p i
  base := Sum.elim (fun f => Sum.inl (K.base f)) (fun f => pushV p i (L.base f.1))
  att := Sum.elim (fun f => (K.att f).map fun eb => (Sum.inl eb.1, eb.2))
    (fun f => (L.att f.1).map fun eb => (pushE p i eb.1, eb.2))
  att_isLoop := by
    rintro (f | f)
    · exact isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (K.att_isLoop f)
    · exact isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) (L.att_isLoop f.1)

@[simp] theorem pushoutComplex_src_inl (e : K.E) :
    (pushoutComplex p i hiV hiE).src (Sum.inl e) = Sum.inl (K.src e) := rfl

@[simp] theorem pushoutComplex_tgt_inl (e : K.E) :
    (pushoutComplex p i hiV hiE).tgt (Sum.inl e) = Sum.inl (K.tgt e) := rfl

theorem pushoutComplex_src_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).src (pushE p i e) = pushV p i (L.src e) :=
  psrc_pushE p i hiV hiE e

theorem pushoutComplex_tgt_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).tgt (pushE p i e) = pushV p i (L.tgt e) :=
  ptgt_pushE p i hiV hiE e

/-- The inclusion `K ⊆ E`. -/
def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
  onV := Sum.inl
  onE := Sum.inl
  onF := Sum.inl
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun _ => rfl

include hiV hiE in
theorem att_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).att (pushF p i f) =
      (L.att f).map fun eb => (pushE p i eb.1, eb.2) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show (K.att (p.onF d)).map (fun eb => (Sum.inl eb.1, eb.2)) = _
    rw [p.att_onF, i.att_onF]
    simp [Function.comp, pushE_of_mem p hiE]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiV hiE in
theorem base_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show Sum.inl (K.base (p.onF d)) = _
    rw [p.base_onF, i.base_onF, pushV_of_mem p hiV]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

/-- The cellular map `L → E`. -/
def pushoutMap (hiF : Function.Injective i.onF) :
    Hom L (pushoutComplex p i hiV hiE) where
  onV := pushV p i
  onE := pushE p i
  onF := pushF p i
  src_onE := pushoutComplex_src_pushE p i hiV hiE
  tgt_onE := pushoutComplex_tgt_pushE p i hiV hiE
  base_onF := base_pushF p i hiV hiE hiF
  att_onF := att_pushF p i hiV hiE hiF

/-- **The pushout square commutes**: a cell of `D` has the same image in `E` whether it is
pushed into `L` or mapped into `K`. -/
theorem pushout_comm (hiF : Function.Injective i.onF) :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have hV  := pushV_of_mem p hiV
  have hE  := pushE_of_mem p hiE
  have hF  := pushF_of_mem p hiF
  have : ∀ X Y (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨a, b, c, _, _, _, _⟩ ⟨a', b', c', _, _, _, _⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  exact this _ _ _ _ (funext hV) (funext hE) (funext hF)

/-! ### The universal property -/

variable {M : Complex2.{u}}

/-- The map out of the pushout induced by a compatible pair of maps. -/
def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV : ∀ v : L.V, Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v := by
    intro v
    by_cases h : ∃ d, i.onV d = v
    · obtain ⟨d, rfl⟩ := h
      rw [pushV_of_mem p hiV d]
      exact (hV d).symm
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  have lE : ∀ e : L.E, Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e := by
    intro e
    by_cases h : ∃ d, i.onE d = e
    · obtain ⟨d, rfl⟩ := h
      rw [pushE_of_mem p hiE d]
      exact (hE d).symm
    · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  exact
    { onV := Sum.elim f.onV (fun w : OffV i => g.onV w.1)
      onE := Sum.elim f.onE (fun w : OffE i => g.onE w.1)
      onF := Sum.elim f.onF (fun w : OffF i => g.onF w.1)
      src_onE := by
        rintro (e | e)
        · exact f.src_onE e
        · show M.src (g.onE e.1) = Sum.elim f.onV _ (pushV p i (L.src e.1))
          rw [lV, g.src_onE]
      tgt_onE := by
        rintro (e | e)
        · exact f.tgt_onE e
        · show M.tgt (g.onE e.1) = Sum.elim f.onV _ (pushV p i (L.tgt e.1))
          rw [lV, g.tgt_onE]
      base_onF := by
        rintro (c | c)
        · exact f.base_onF c
        · show M.base (g.onF c.1) = Sum.elim f.onV _ (pushV p i (L.base c.1))
          rw [lV, g.base_onF]
      att_onF := by
        rintro (c | c)
        · show M.att (f.onF c) = ((K.att c).map fun eb => (Sum.inl eb.1, eb.2)).map _
          rw [f.att_onF]
          simp
        · show M.att (g.onF c.1) = ((L.att c.1).map fun eb => (pushE p i eb.1, eb.2)).map _
          rw [g.att_onF]
          simp only [List.map_map]
          exact List.map_congr_left (fun eb _ => by simp [Function.comp, lE eb.1]) }

@[simp] theorem pushoutLift_onV (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onV = Sum.elim f.onV (fun w : OffV i => g.onV w.1) := rfl

@[simp] theorem pushoutLift_onE (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onE = Sum.elim f.onE (fun w : OffE i => g.onE w.1) := rfl

@[simp] theorem pushoutLift_onF (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) :
    (pushoutLift p i hiV hiE f g hV hE).onF = Sum.elim f.onF (fun w : OffF i => g.onF w.1) := rfl

/-! ### Finiteness -/

end

/-! ### Functoriality in the term upstairs -/

section Functor

variable {L' : Complex2.{u}}

theorem functor_hV (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.V) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d) =
      (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
  show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
  rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d,
    pushV_of_mem p hj'V]

theorem functor_hE (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.E) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d) =
      (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
  show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
  rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d,
    pushE_of_mem p hj'E]

/-- The map of pushouts induced by an inclusion `L ⊆ L'` of terms over `D`. -/
def pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :
    Hom (pushoutComplex p j hjV hjE) (pushoutComplex p j' hj'V hj'E) :=
  pushoutLift p j hjV hjE (pushoutInl p j' hj'V hj'E) ((pushoutMap p j' hj'V hj'E hj'F).comp k)
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)

/-- A cell of `L` off `D` stays off `D` in a larger term `L'`. -/
theorem off_map_V {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 := by
  intro d hd
  refine w.2 d (hkV ?_)
  rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d, hd]

theorem off_map_E {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 := by
  intro d hd
  refine w.2 d (hkE ?_)
  rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d, hd]

theorem off_map_F {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 := by
  intro d hd
  refine w.2 d (hkF ?_)
  rw [show k.onF (j.onF d) = j'.onF d from congrFun (congrArg Hom.onF hkj) d, hd]

end Functor

/-! ### Connectivity -/

section Connected

/-- **The pushout of connected complexes is connected.** -/
theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  set E := pushoutComplex p i hiV hiE
  set b : E.V := Sum.inl (p.onV d₀)
  have key : ∀ x : E.V, (∃ q, IsPath E.src E.tgt q x b) ∧ ∃ q, IsPath E.src E.tgt q b x := by
    rintro (a | w)
    · obtain ⟨q₁, hq₁⟩ := hK a (p.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hK (p.onV d₀) a
      exact ⟨⟨_, isPath_map (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₁⟩,
        ⟨_, isPath_map (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₂⟩⟩
    · have hw  := pushV_of_off p i w
      have hd  := pushV_of_mem p hiV d₀
      obtain ⟨q₁, hq₁⟩ := hL w.1 (i.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hL (i.onV d₀) w.1
      have h₁ := isPath_map (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₁
      have h₂ := isPath_map (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₂
      rw [hw, hd] at h₁
      rw [hw, hd] at h₂
      exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
  intro x y
  obtain ⟨⟨q₁, hq₁⟩, -⟩ := key x
  obtain ⟨-, ⟨q₂, hq₂⟩⟩ := key y
  exact ⟨q₁ ++ q₂, hq₁.append hq₂⟩

end Connected

end Comb
end FiniteChains
end

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {X Y : Complex2.{u}}

/-! ### Distance to the image of a subcomplex -/

section Extension

/-- The lengths of the edge paths from `a` to the image of `X`. -/
def imReach (h : Hom X Y) (a : Y.V) : Set ℕ :=
  {n | ∃ p : List (Y.E × Bool), p.length = n ∧ ∃ x : X.V, IsPath Y.src Y.tgt p a (h.onV x)}

/-- The distance from a vertex of `Y` to the image of `X`. -/
def imDist (h : Hom X Y) (a : Y.V) : ℕ := sInf (imReach h a)

variable (h : Hom X Y) (hconn : IsConnected Y) (x₀ : X.V)


include hconn x₀ in
theorem imDist_mem (a : Y.V) : imDist h a ∈ imReach h a :=
  Nat.sInf_mem (by
    obtain ⟨p, hp⟩ := hconn a (h.onV x₀)
    exact ⟨p.length, p, rfl, x₀, hp⟩)

theorem imDist_le {a : Y.V} {p : List (Y.E × Bool)} {x : X.V}
    (hp : IsPath Y.src Y.tgt p a (h.onV x)) : imDist h a ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, x, hp⟩

theorem imDist_image (x : X.V) : imDist h (h.onV x) = 0 :=
  Nat.le_zero.1 (imDist_le h (p := []) (x := x) rfl)

include hconn x₀ in
theorem exists_pre {a : Y.V} (hz : imDist h a = 0) : ∃ x : X.V, a = h.onV x := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  simp_all

/-- A choice of preimage of a vertex at distance zero from the image. -/
def imPre {a : Y.V} (hz : imDist h a = 0) : X.V :=
  Classical.choose (exists_pre h hconn x₀ hz)

theorem imPre_spec {a : Y.V} (hz : imDist h a = 0) :
    a = h.onV (imPre h hconn x₀ hz) :=
  Classical.choose_spec (exists_pre h hconn x₀ hz)

include hconn x₀ in
/-- A vertex not in the image has a neighbour one step closer to the image. -/
theorem imDist_step {a : Y.V} (ha : imDist h a ≠ 0) :
    ∃ g : Y.E × Bool, germSrc Y.src Y.tgt g = a ∧
      imDist h (germTgt Y.src Y.tgt g) + 1 = imDist h a := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  have hne : p ≠ [] := by
    intro hp0
    subst hp0
    exact ha (by simpa using hlen.symm)
  obtain ⟨g, q, rfl⟩ : ∃ (g : Y.E × Bool) (q : List (Y.E × Bool)), p = g :: q := by
    cases p with
    | nil => simp_all
    | cons g q => simp
  obtain ⟨hgs, hq⟩ := hp
  refine ⟨g, hgs.symm, ?_⟩
  have h1  := imDist_le h hq
  have h2 : imDist h a ≤ imDist h (germTgt Y.src Y.tgt g) + 1 := by
    obtain ⟨q', hlen', x', hq'⟩ := imDist_mem h hconn x₀ (germTgt Y.src Y.tgt g)
    have hpath : IsPath Y.src Y.tgt (g :: q') a (h.onV x') := ⟨hgs, hq'⟩
    have := imDist_le h hpath
    simpa [hlen'] using this
  have h3 : q.length + 1 = imDist h a := by
    simp at hlen
    omega
  omega

/-- The edge towards the image chosen at a vertex outside the image. -/
def upChoice {a : Y.V} (ha : imDist h a ≠ 0) : Y.E × Bool :=
  Classical.choose (imDist_step h hconn x₀ ha)

theorem upChoice_src {a : Y.V} (ha : imDist h a ≠ 0) :
    germSrc Y.src Y.tgt (upChoice h hconn x₀ ha) = a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).1

theorem upChoice_dist {a : Y.V} (ha : imDist h a ≠ 0) :
    imDist h (germTgt Y.src Y.tgt (upChoice h hconn x₀ ha)) + 1 = imDist h a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).2

/-! ### The extended height and the extended tree edges -/

variable (T : SpanningTree X)

/-- The height function of the extended tree: the old height on the image, and one more than
the height of the next vertex towards the image elsewhere. -/
def extHt (a : Y.V) : ℕ :=
  if hz : imDist h a = 0 then T.ht (imPre h hconn x₀ hz)
  else extHt (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1
  termination_by imDist h a
  decreasing_by
    have := upChoice_dist h hconn x₀ hz
    omega

theorem extHt_of_zero {a : Y.V} (hz : imDist h a = 0) :
    extHt h hconn x₀ T a = T.ht (imPre h hconn x₀ hz) := by
  rw [extHt, dif_pos hz]

theorem extHt_of_ne {a : Y.V} (hz : imDist h a ≠ 0) :
    extHt h hconn x₀ T a =
      extHt h hconn x₀ T (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1 := by
  rw [extHt]
  exact dif_neg hz

include hconn x₀ in
theorem extHt_image (hV : Function.Injective h.onV) (x : X.V) :
    extHt h hconn x₀ T (h.onV x) = T.ht x := by
  have hz  := imDist_image h x
  rw [extHt_of_zero h hconn x₀ T hz]
  have := (imPre_spec h hconn x₀ hz).symm
  rw [hV this]

theorem imPre_ne_root {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    imPre h hconn x₀ hz ≠ T.root := fun hr =>
  ha ((imPre_spec h hconn x₀ hz).trans (congrArg h.onV hr))

/-- The tree edge of the extended tree. -/
def extUp (a : Y.V) (ha : a ≠ h.onV T.root) : Y.E × Bool :=
  if hz : imDist h a = 0 then
    (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
      (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).2)
  else upChoice h hconn x₀ hz

theorem extUp_of_zero {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    extUp h hconn x₀ T a ha =
      (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
        (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).2) := by
  rw [extUp, dif_pos hz]

theorem extUp_of_ne {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a ≠ 0) :
    extUp h hconn x₀ T a ha = upChoice h hconn x₀ hz := by
  rw [extUp]
  exact dif_neg hz

/-- The extension of a spanning tree of a subcomplex to the ambient complex. -/
def extend (hV : Function.Injective h.onV) : SpanningTree Y where
  root := h.onV T.root
  ht := extHt h hconn x₀ T
  isTree := fun e => ∃ (a : Y.V) (ha : a ≠ h.onV T.root), (extUp h hconn x₀ T a ha).1 = e
  up := extUp h hconn x₀ T
  ht_root := by rw [extHt_image h hconn x₀ T hV, T.ht_root]
  ht_eq_zero := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extHt_of_zero h hconn x₀ T hz] at ha
      exact (imPre_spec h hconn x₀ hz).trans (congrArg h.onV (T.ht_eq_zero _ ha))
    · rw [extHt_of_ne h hconn x₀ T hz] at ha
      omega
  up_src := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz, germSrc_onE h, T.up_src]
      exact (imPre_spec h hconn x₀ hz).symm
    · rw [extUp_of_ne h hconn x₀ T ha hz]
      exact upChoice_src h hconn x₀ hz
  up_ht := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz, germTgt_onE h,
        extHt_image h hconn x₀ T hV, extHt_of_zero h hconn x₀ T hz]
      exact T.up_ht _ _
    · rw [extUp_of_ne h hconn x₀ T ha hz, extHt_of_ne h hconn x₀ T hz]
  isTree_iff := fun _ => Iff.rfl

include hconn x₀ in
/-- **A spanning tree of a subcomplex extends to a spanning tree of the ambient complex.**
The extension has the image of the old root as root, and an edge of the subcomplex is an edge
of the extension exactly when it was an edge of the old tree. -/
theorem exists_extension (hV : Function.Injective h.onV) (hE : Function.Injective h.onE) :
    ∃ T' : SpanningTree Y, T'.root = h.onV T.root ∧
      ∀ e : X.E, (T'.isTree (h.onE e) ↔ T.isTree e) := by
  refine ⟨extend h hconn x₀ T hV, rfl, ?_⟩
  intro e
  constructor
  · rintro ⟨a, ha, hae⟩
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz] at hae
      exact (T.isTree_iff e).2 ⟨_, imPre_ne_root h hconn x₀ T ha hz, hE hae⟩
    · exfalso
      apply hz
      rw [extUp_of_ne h hconn x₀ T ha hz] at hae
      have hsrc := upChoice_src h hconn x₀ hz
      revert hae hsrc
      generalize upChoice h hconn x₀ hz = g
      obtain ⟨e', b⟩ := g
      intro hae hsrc
      simp only at hae
      subst hae
      rw [← hsrc, germSrc_onE h (e, b)]
      exact imDist_image h _
  · intro he
    obtain ⟨x, hx, hxe⟩ := (T.isTree_iff e).1 he
    have hne  := fun hc => hx (hV hc)
    refine ⟨h.onV x, hne, ?_⟩
    have hz  := imDist_image h x
    rw [extUp_of_zero h hconn x₀ T hne hz]
    have key : ∀ (y : X.V) (hy : y ≠ T.root), y = x → (T.up y hy).1 = e := by
      rintro y hy rfl
      exact hxe
    exact congrArg h.onE (key _ _ (hV (imPre_spec h hconn x₀ hz)).symm)

end Extension

/-! ### The induced inclusion of the collapsed presentations -/

section Presentation

variable {h : Hom X Y} {T : SpanningTree X} {T' : SpanningTree Y}
  (hiff : ∀ e : X.E, T'.isTree (h.onE e) ↔ T.isTree e)

/-- The generators of the collapse of `X` are generators of the collapse of `Y`, as soon as the
spanning tree of `Y` meets `X` exactly in the spanning tree of `X`. -/
def nonTreeIncl (e : NonTree T) : NonTree T' :=
  ⟨h.onE e.1, fun hc => e.2 ((hiff e.1).1 hc)⟩

@[simp] theorem nonTreeIncl_coe (e : NonTree T) : (nonTreeIncl hiff e : Y.E) = h.onE e.1 := rfl

theorem nonTreeIncl_injective (hE : Function.Injective h.onE) :
    Function.Injective (nonTreeIncl hiff) := by
  intro a b hab
  exact Subtype.ext (hE (congrArg Subtype.val hab))

/-- The letter spelled by an oriented edge is transported by the inclusion of generators. -/
theorem germWord_onE (g : X.E × Bool) :
    germWord T' (h.onE g.1, g.2) = FreeGroup.map (nonTreeIncl hiff) (germWord T g) := by
  obtain ⟨e, b⟩ := g
  by_cases hT : T.isTree e
  · have hT'  := (hiff e).2 hT
    simp [germWord, hT, hT']
  · have hT' : ¬ T'.isTree (h.onE e) := fun hc => hT ((hiff e).1 hc)
    cases b <;> simp [germWord, hT, hT', nonTreeIncl]

/-- **The word spelled by an edge path is transported by the inclusion of generators.** -/
theorem pathWord_mapPath (l : List (X.E × Bool)) :
    pathWord T' (mapPath h l) = FreeGroup.map (nonTreeIncl hiff) (pathWord T l) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
      have hcons : mapPath h (g :: l) = (h.onE g.1, g.2) :: mapPath h l := rfl
      rw [hcons, pathWord_cons, ih, germWord_onE hiff g, pathWord_cons, map_mul]

/-- **The relators of the collapse of `X` are relators of the collapse of `Y`.**  Together with
`FiniteChains.Comb.SpanningTree.nonTreeIncl_injective` this exhibits the collapse of `X` as a
subpresentation of the collapse of `Y`, in the sense used by `FiniteChains.PresChain`. -/
theorem treeRel_onF (f : X.F) :
    treeRel T' (h.onF f) = FreeGroup.map (nonTreeIncl hiff) (treeRel T f) := by
  have hatt : Y.att (h.onF f) = mapPath h (X.att f) := h.att_onF f
  rw [treeRel, hatt, pathWord_mapPath hiff, treeRel]

end Presentation

end SpanningTree
end Comb
end FiniteChains

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-! ### Compatible spanning trees along a chain -/

/-- **A spanning tree of the first stage of a chain extends to all stages**, each tree meeting
the previous stage exactly in the previous tree. -/
theorem exists_compatible_trees (X : ℕ → Complex2.{u}) (inc : ∀ r, Hom (X r) (X (r + 1)))
    (hconn : ∀ r, IsConnected (X r)) (hV : ∀ r, Function.Injective (inc r).onV)
    (hE : ∀ r, Function.Injective (inc r).onE) (T₀ : SpanningTree (X 0)) :
    ∃ T : ∀ r, SpanningTree (X r), T 0 = T₀ ∧
      ∀ (r : ℕ) (e : (X r).E), (T (r + 1)).isTree ((inc r).onE e) ↔ (T r).isTree e := by
  have step : ∀ r (Tr : SpanningTree (X r)), ∃ T' : SpanningTree (X (r + 1)),
      ∀ e : (X r).E, T'.isTree ((inc r).onE e) ↔ Tr.isTree e := by
    intro r Tr
    obtain ⟨T', -, hT'⟩ :=
      exists_extension (inc r) (hconn (r + 1)) Tr.root Tr (hV r) (hE r)
    exact ⟨T', hT'⟩
  choose next hnext using step
  refine ⟨fun r => Nat.rec T₀ (fun r Tr => next r Tr) r, rfl, ?_⟩
  simp_all

/-! ### Chains of two-complexes -/




variable {K : Complex2.{u}} (T₀ : SpanningTree K)
variable [Fintype (NonTree T₀)] [DecidableEq (NonTree T₀)] [Fintype K.F] [DecidableEq K.F]

/-! ### Non-vacuity -/

end SpanningTree
end Comb
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

/-! ### Cancelling a common prefix and suffix from a homotopy -/

/-- A homotopy between two paths conjugated by a fixed prefix and suffix comes from a homotopy
between the paths themselves. -/
theorem htpy_of_congr_append {X : Complex2.{u}} {a b c d : X.V}
    {r s p q : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d)
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X c d (r ++ p ++ s) (r ++ q ++ s)) : Htpy X a b p q := by
  have key : ∀ l : List (X.E × Bool), IsPath X.src X.tgt l a b →
      Htpy X a b (revPath r ++ (r ++ l ++ s) ++ revPath s) l := by
    intro l hl
    have hrl  := (isPath_revPath hr).append hr
    have hss  := hs.append (isPath_revPath hs)
    have hlss  := hl.append hss
    have e1 : revPath r ++ (r ++ l ++ s) ++ revPath s
        = (revPath r ++ r) ++ (l ++ (s ++ revPath s)) := by
      simp [List.append_assoc]
    have h1  :=
      Htpy.append_congr hrl hlss (htpy_revPath_append hr) (Htpy.refl _)
    have h2  :=
      Htpy.append_congr hl hss (Htpy.refl _) (htpy_append_revPath hs)
    rw [e1]
    refine h1.trans ?_
    simpa using h2
  have h' := h.congr_append (isPath_revPath hr) (isPath_revPath hs)
  exact ((key p hp).symm.trans h').trans (key q hq)

namespace SpanningTree

variable {K : Complex2.{u}} (T : SpanningTree K)
variable [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F]

/-- The relator subgroup of the collapsed presentation. -/
abbrev relTree : Subgroup (FreeGroup (NonTree T)) := relSub (treeRel T)

/-- The universal cover of `K`, in the algebraic model: the cover attached to the relator
subgroup of the collapsed presentation. -/
abbrev treeUniv : Complex2.{u} :=
  treeCover T (relTree T) (rel_mem_relSub (treeRel T))

/-! ### The element of `π₁(K)` spelled by a vertex of the homotopy-theoretic cover -/

variable {T}

/-- The element of `π₁(K) = ⟨E ∖ T | r⟩` spelled by a homotopy class of edge paths. -/
def uvQ {x₀ : K.V} : UV K x₀ → CovQ T (relTree T) :=
  Quotient.lift (fun p : PathFrom K x₀ => wordQ T (relTree T) p.1)
    (fun _ _ h => wordClass_htpy T h)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
@[simp] theorem uvQ_mk {x₀ : K.V} (p : PathFrom K x₀) :
    uvQ (T := T) (UV.mk p) = wordQ T (relTree T) p.1 := rfl

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_extend {x₀ : K.V} {c : UV K x₀} {eb : K.E × Bool}
    (h : endV c = germSrc K.src K.tgt eb) :
    uvQ (T := T) (Comb.extend eb c) = uvQ (T := T) c * germQ T (relTree T) eb := by
  induction c using UV.ind with
  | h p =>
      have hp  := h
      rw [extend_mk, uvQ_mk, extendP_pos hp, uvQ_mk, wordQ_append]
      congr 1
      rw [show ([eb] : List (K.E × Bool)) = eb :: [] from rfl, wordQ_cons, wordQ_nil, mul_one]

/-! ### The two-chain map is injective: `uvQ` separates classes with the same endpoint -/

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvQ_conjPath {x₀ b : K.V} {l : List (K.E × Bool)} (hl : IsPath K.src K.tgt l x₀ b) :
    pi1ToPres T (loopOf T hl) = wordQ T (relTree T) l := by
  show wordClass T (conjPath T l x₀ b) = _
  rw [conjPath, wordClass_append, wordClass_append]
  have h₁ : wordClass T (T.treePath x₀) = 1 := by
    show QuotientGroup.mk (pathWord T (T.treePath x₀)) = 1
    rw [pathWord_treePath]; rfl
  have h₂ : wordClass T (revPath (T.treePath b)) = 1 := by
    show QuotientGroup.mk (pathWord T (revPath (T.treePath b))) = 1
    rw [pathWord_revPath, pathWord_treePath]
    simp
  rw [h₁, h₂, one_mul, mul_one]
  rfl

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Two homotopy classes of paths with the same endpoint spelling the same element of
`π₁(K)` are equal.**  This is the injectivity half of the computation of `π₁`. -/
theorem uvQ_injective {x₀ : K.V} {c d : UV K x₀} (hq : uvQ (T := T) c = uvQ (T := T) d)
    (he : endV c = endV d) : c = d := by
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hpe : endpt K x₀ p.1 = endpt K x₀ q.1 := he
      have hp  := p.2
      have hq' : IsPath K.src K.tgt q.1 x₀ (endpt K x₀ p.1) := by
        rw [hpe]; exact q.2
      have hloop : loopOf T hp = loopOf T hq' := by
        refine (pi1EquivPres T).injective ?_
        show pi1ToPres T (loopOf T hp) = pi1ToPres T (loopOf T hq')
        rw [uvQ_conjPath hp, uvQ_conjPath hq']
        exact hq
      have hhtpy  := Quotient.exact hloop
      refine Quotient.sound ?_
      exact htpy_of_congr_append (T.treePath_isPath x₀)
        (isPath_revPath (T.treePath_isPath (endpt K x₀ p.1))) hp hq' hhtpy

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **Every element of `π₁(K)` is spelled by a path to every vertex.** -/
theorem exists_uvQ (x₀ : K.V) (g : CovQ T (relTree T)) (a : K.V) :
    ∃ c : UV K x₀, uvQ (T := T) c = g ∧ endV c = a := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := relTree T) g
  obtain ⟨L, hL, hLw⟩ := exists_loop_spelling T w
  set l : List (K.E × Bool) := revPath (T.treePath x₀) ++ L ++ T.treePath a with hldef
  have hl  :=
    ((isPath_revPath (T.treePath_isPath x₀)).append hL).append (T.treePath_isPath a)
  have hend  := endpt_eq_of_isPath hl
  refine ⟨UV.mk ⟨l, by rw [hend]; exact hl⟩, ?_, ?_⟩
  · show wordQ T (relTree T) l = _
    rw [hldef, wordQ_append, wordQ_append, wordQ_treePath]
    have hrev : wordQ T (relTree T) (revPath (T.treePath x₀)) = 1 := by
      show QuotientGroup.mk (pathWord T (revPath (T.treePath x₀))) = 1
      rw [pathWord_revPath, pathWord_treePath]
      simp
    rw [hrev, one_mul, mul_one]
    show QuotientGroup.mk (pathWord T L) = _
    rw [hLw]
  · show endpt K x₀ l = a
    exact hend

/-! ### The cellular map to the algebraic model -/

variable (T)

/-- The map of edges: the edge `(c, e)` of the homotopy-theoretic cover goes to the edge
`(uvQ c, e)` of the algebraic one. -/
def uvEdge {x₀ : K.V} (E : UE K x₀) : (treeUniv T).E := (uvQ (T := T) E.1.1, E.1.2)

/-- The map of two-cells. -/
def uvFace {x₀ : K.V} (F : UF K x₀) : (treeUniv T).F := (uvQ (T := T) F.1.1, F.1.2)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **The lifts of an edge path in the two models agree.** -/
theorem map_uLiftPath_tree {x₀ : K.V} : ∀ (L : List (K.E × Bool)) (c : UV K x₀) (w : K.V),
    IsPath K.src K.tgt L (endV c) w →
      (uLiftPath L c).map (fun Eb => (uvEdge T Eb.1, Eb.2))
        = liftK T (relTree T) L (uvQ (T := T) c) := by
  intro L
  induction L with
  | nil => simp
  | cons eb t ih =>
      intro c w hL
      obtain ⟨e, b⟩ := eb
      cases b with
      | true =>
          have hc  := hL.1
          have hnext : IsPath K.src K.tgt t (endV (Comb.extend (e, true) c)) w := by
            rw [endV_extend hc]; exact hL.2
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih (Comb.extend (e, true) c) w hnext, uvQ_extend hc]
          congr 1
      | false =>
          have hc  := hL.1
          have hnext : IsPath K.src K.tgt t (endV (Comb.extend (e, false) c)) w := by
            rw [endV_extend hc]; exact hL.2
          rw [uLiftPath_cons hc, List.map_cons, liftK_cons,
            ih (Comb.extend (e, false) c) w hnext, uvQ_extend hc]
          congr 1
          show ((uvQ (T := T) (Comb.extend (e, false) c), e), false)
            = SpanningTree.liftGerm T (relTree T) (uvQ (T := T) c) (e, false)
          rw [uvQ_extend hc]
          simp [SpanningTree.liftGerm]

/-- **The homotopy-theoretic universal cover of `K` is the algebraic one.** -/
def treeUnivHom (x₀ : K.V) : Hom (uCover K x₀) (treeUniv T) where
  onV c := (uvQ (T := T) c, endV c)
  onE := uvEdge T
  onF := uvFace T
  src_onE E := by
    show covSrc T (relTree T) (uvQ (T := T) E.1.1, E.1.2) = (uvQ (T := T) E.1.1, endV E.1.1)
    show (uvQ (T := T) E.1.1, K.src E.1.2) = (uvQ (T := T) E.1.1, endV E.1.1)
    rw [E.2]
  tgt_onE E := by
    show covTgt T (relTree T) (uvQ (T := T) E.1.1, E.1.2)
      = (uvQ (T := T) (Comb.extend (E.1.2, true) E.1.1), endV (Comb.extend (E.1.2, true) E.1.1))
    rw [uvQ_extend (eb := (E.1.2, true)) E.2, endV_extend (eb := (E.1.2, true)) E.2]
    rfl
  base_onF F := by
    show (uvQ (T := T) F.1.1, K.base F.1.2) = (uvQ (T := T) F.1.1, endV F.1.1)
    rw [F.2]
  att_onF F := by
    have hbase : endV F.1.1 = K.base F.1.2 := F.2
    have hatt : IsPath K.src K.tgt (K.att F.1.2) (endV F.1.1) (K.base F.1.2) := by
      rw [hbase]; exact K.att_isLoop F.1.2
    show liftK T (relTree T) (K.att F.1.2) (uvQ (T := T) F.1.1)
      = (uLiftPath (K.att F.1.2) F.1.1).map (fun Eb => (uvEdge T Eb.1, Eb.2))
    rw [map_uLiftPath_tree T (K.att F.1.2) F.1.1 (K.base F.1.2) hatt]

/-! ### The map is bijective -/


omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_injective {x₀ : K.V} : Function.Injective (uvFace T (x₀ := x₀)) := by
  rintro ⟨⟨c, f⟩, hc⟩ ⟨⟨d, f'⟩, hd⟩ hEq
  have h1  := congrArg Prod.fst hEq
  have h2 : f = f' := congrArg Prod.snd hEq
  subst h2
  have hend : endV c = endV d := by rw [hc, hd]
  exact Subtype.ext (Prod.ext (uvQ_injective h1 hend) rfl)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
theorem uvFace_surjective {x₀ : K.V} :
    Function.Surjective (uvFace T (x₀ := x₀)) := by
  rintro ⟨g, f⟩
  obtain ⟨c, hc, hend⟩ := exists_uvQ x₀ g (K.base f)
  exact ⟨⟨(c, f), hend⟩, by simp [uvFace, hc]⟩

/-! ### `π₂` is the same in the two models -/

omit [Fintype (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- **A two-chain of the homotopy-theoretic universal cover of `K` is a cycle exactly when the
corresponding two-chain of the universal cover of the collapsed presentation complex is.**
Collapsing a spanning tree does not change `π₂`. -/
theorem mem_pi2_iff_bdry2_univCover {x₀ : K.V} (u : (uCover K x₀).F →₀ ℤ) :
    u ∈ Pi2 K x₀ ↔
      bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u) = 0 := by
  have hkey : bdry2 (univCover (treeRel T)) (chain2 (treeUnivHom T x₀) u)
      = piE T (relTree T) (chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u)) := by
    rw [← bdry2_chain2 (treeUnivHom T x₀) u]
    exact (piE_bdry2 (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
      (chain2 (treeUnivHom T x₀) u)).symm
  constructor
  · intro hu
    have h0  := hu
    rw [hkey, h0, map_zero, map_zero]
  · intro hu
    set z := chain1 (treeUnivHom T x₀) (bdry2 (uCover K x₀) u) with hz
    have hze : piE T (relTree T) z = 0 := by rw [hz, ← hkey]; exact hu
    have hbz : bdry1 (treeUniv T) z = 0 := by
      rw [hz, ← bdry2_chain2 (treeUnivHom T x₀) u]
      exact bdry1_bdry2 _
    have hzero  :=
      treeChain_eq_zero (T := T) (N := relTree T) (hN := rel_mem_relSub (treeRel T))
        (support_isTree_of_piE_eq_zero (T := T) (N := relTree T) hze) hbz
    have hinj : Function.Injective (chain1 (treeUnivHom T x₀)) :=
      Finsupp.mapDomain_injective (by
        rintro ⟨⟨c, e⟩, hc⟩ ⟨⟨d, e'⟩, hd⟩ hEq
        have h1  := congrArg Prod.fst hEq
        have h2 : e = e' := congrArg Prod.snd hEq
        subst h2
        have hend : endV c = endV d := by rw [hc, hd]
        exact Subtype.ext (Prod.ext (uvQ_injective h1 hend) rfl))
    exact hinj (by rw [← hz, hzero, map_zero])

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F] in
/-- Every two-chain of the universal cover of the collapsed presentation complex comes from a
two-chain of the homotopy-theoretic universal cover of `K`. -/
theorem chain2_treeUnivHom_surjective {x₀ : K.V} :
    Function.Surjective (chain2 (treeUnivHom T x₀)) := by
  intro v
  obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (M := ℤ) (uvFace_surjective T (x₀ := x₀)) v
  exact ⟨u, hu⟩

end SpanningTree
end Comb
end FiniteChains
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

/-! ### Naturality of the identification of the two models -/

section Naturality

variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
variable [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
variable [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F]
variable {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)

omit [Fintype (NonTree TX)] [DecidableEq (NonTree TX)] [Fintype X.F] [DecidableEq X.F]
  [Fintype (NonTree TY)] [DecidableEq (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- The element of `π₁` spelled by the image of a path is the image of the element spelled by
the path. -/
theorem uvQ_univLiftV {x₀ : X.V} (c : UV X x₀) :
    uvQ (T := TY) (univLiftV x₀ h c)
      = presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
          (treeRel_onF hiff) (uvQ (T := TX) c) := by
  induction c using UV.ind with
  | h p =>
      show QuotientGroup.mk (pathWord TY (mapPath h p.1)) = _
      rw [pathWord_mapPath hiff]
      rfl

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The identification of the two models of the universal cover is natural in a subcomplex
inclusion: on two-cells it carries the lift of the inclusion to the inclusion of the universal
covers of the collapsed presentation complexes. -/
theorem uvFace_univLiftF (hE : Function.Injective h.onE) {x₀ : X.V} (F : UF X x₀) :
    uvFace TY (univLiftF x₀ h F)
      = (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
          (treeRel TY) h.onF (treeRel_onF hiff)).onF (uvFace TX F) := by
  show (uvQ (T := TY) (univLiftV x₀ h F.1.1), h.onF F.1.2)
    = Prod.map (presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
        (treeRel_onF hiff)) h.onF (uvQ F.1.1, F.1.2)
  rw [uvQ_univLiftV hiff]
  rfl

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)]
  [Fintype Y.F] [DecidableEq Y.F] in
/-- The square of two-chains commutes. -/
theorem chain2_treeUnivHom_square (hE : Function.Injective h.onE) {x₀ : X.V}
    (u : (uCover X x₀).F →₀ ℤ) :
    chain2 (treeUnivHom TY (h.onV x₀)) (chain2 (univLift X h x₀) u)
      = chain2 (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
          (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)) (chain2 (treeUnivHom TX x₀) u) := by
  show Finsupp.mapDomain (uvFace TY) (Finsupp.mapDomain (univLiftF x₀ h) u)
    = Finsupp.mapDomain (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
        (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)).onF (Finsupp.mapDomain (uvFace TX) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (fun k => Finsupp.mapDomain k u) ?_
  funext F
  exact uvFace_univLiftF hiff hE F

omit [Fintype (NonTree TX)] [Fintype X.F] [DecidableEq X.F] [Fintype (NonTree TY)] [Fintype Y.F] [DecidableEq Y.F] in
/-- **If a subcomplex inclusion is zero on `π₂`, so is the induced inclusion of the collapsed
presentation complexes.**  This is the dictionary that turns the topological form of condition
(1) of Theorem A into the algebraic one used in Section 2 of the paper. -/
theorem zeroPi2_presInclHom_of_zeroPi2 (hE : Function.Injective h.onE) (hzero : ZeroPi2 h) :
    ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
      (treeRel TY) h.onF (treeRel_onF hiff)) := by
  refine (Comb.zeroPi2_presInclHom_iff (ρ := treeRel TX) (nonTreeIncl hiff)
    (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).2 ?_
  intro v hv
  obtain ⟨u, rfl⟩ := chain2_treeUnivHom_surjective TX (x₀ := TX.root) v
  have hu  := (mem_pi2_iff_bdry2_univCover TX u).2 hv
  rw [← chain2_treeUnivHom_square hiff hE u, hzero TX.root u hu, map_zero]

end Naturality

/-! ### Chains of two-complexes with the topological hypothesis -/



variable {K : Complex2.{u}} (T₀ : SpanningTree K)
variable [Fintype (NonTree T₀)] [DecidableEq (NonTree T₀)] [Fintype K.F] [DecidableEq K.F]

end SpanningTree

/-! ### The statement without spanning trees -/




/-! ### Non-vacuity -/

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {D K : Complex2.{u}} {p : Hom D K} {x₀ : K.V} {d₀ : D.V}

/-! ### Endpoints of lifted paths -/

variable (p d₀) in
/-- `LiftsTo p d₀ q v`: the edge path `q` of the base lifts to an edge path from `d₀` to `v`. -/
def LiftsTo (q : List (K.E × Bool)) (v : D.V) : Prop :=
  ∃ m : List (D.E × Bool), IsPath D.src D.tgt m d₀ v ∧ mapPath p m = q

theorem exists_liftsTo (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    ∃ v, LiftsTo p d₀ q.1 v := by
  obtain ⟨m, c, hm, hmap⟩ :=
    exists_liftPathAt hcov q.1 d₀ (endpt K x₀ q.1) (by rw [hd]; exact q.2)
  exact ⟨c, m, hm, hmap⟩

theorem liftsTo_unique (hcov : IsCovering p) {q : List (K.E × Bool)} {v w : D.V}
    (hv : LiftsTo p d₀ q v) (hw : LiftsTo p d₀ q w) : v = w := by
  obtain ⟨m, hm, hmap⟩ := hv
  obtain ⟨m', hm', hmap'⟩ := hw
  have hmm  := liftPath_unique hcov m m' d₀ v w hm hm' (by rw [hmap, hmap'])
  subst hmm
  exact isPath_endpoint_eq hm hm'

/-- The endpoint of a lift only depends on the homotopy class of the path. -/
theorem liftsTo_htpy (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q q' : List (K.E × Bool)}
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

/-- The lift of the universal cover on vertices: the class of a path from `x₀` goes to the
endpoint of the lift of that path at `d₀`. -/
def coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) : D.V :=
  Quotient.liftOn c (fun q => Classical.choose (exists_liftsTo hcov hd q)) (by
    intro q q' hqq'
    exact liftsTo_unique hcov
      (liftsTo_htpy hcov hd (Classical.choose_spec (exists_liftsTo hcov hd q)) hqq')
      (Classical.choose_spec (exists_liftsTo hcov hd q')))

theorem coverV_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (q : PathFrom K x₀) :
    LiftsTo p d₀ q.1 (coverV hcov hd (UV.mk q)) :=
  Classical.choose_spec (exists_liftsTo hcov hd q)

theorem coverV_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {q : PathFrom K x₀} {v : D.V}
    (h : LiftsTo p d₀ q.1 v) : coverV hcov hd (UV.mk q) = v :=
  liftsTo_unique hcov (coverV_spec hcov hd q) h

theorem coverV_base (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    coverV hcov hd (UV.base K x₀) = d₀ :=
  coverV_eq hcov hd ⟨[], rfl, rfl⟩

/-- The lift covers the projection of the universal cover. -/
theorem onV_coverV (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (c : UV K x₀) :
    p.onV (coverV hcov hd c) = endV c := by
  induction c using UV.ind with
  | h q =>
      obtain ⟨m, hm, hmap⟩ := coverV_spec hcov hd q
      have hpath  :=
        isPath_mapPath p hm
      rw [hmap, hd] at hpath
      exact (endpt_eq_of_isPath hpath).symm

/-- Extending a class by an oriented edge moves the lift along the lifted edge. -/
theorem coverV_extend (hcov : IsCovering p) (hd : p.onV d₀ = x₀) {c : UV K x₀}
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

theorem coverE_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc K.src K.tgt (ce.1.2, true) = p.onV (coverV hcov hd ce.1.1) := by
  rw [onV_coverV]
  exact ce.2.symm

/-- The lift, at the image of its initial vertex, of the oriented edge underlying an edge of
the universal cover. -/
def coverGerm (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.E × Bool :=
  Classical.choose (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))

theorem coverGerm_spec (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    germSrc D.src D.tgt (coverGerm hcov hd ce) = coverV hcov hd ce.1.1 ∧
      (p.onE (coverGerm hcov hd ce).1, (coverGerm hcov hd ce).2) = (ce.1.2, true) :=
  (Classical.choose_spec
    (exists_unique_liftGerm hcov (coverV hcov hd ce.1.1) (coverE_cond hcov hd ce))).1

theorem coverGerm_snd (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    (coverGerm hcov hd ce).2 = true :=
  congrArg Prod.snd (coverGerm_spec hcov hd ce).2

/-- The lift of the universal cover on edges. -/
def coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) : D.E :=
  (coverGerm hcov hd ce).1

theorem onE_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    p.onE (coverE hcov hd ce) = ce.1.2 :=
  congrArg Prod.fst (coverGerm_spec hcov hd ce).2

theorem coverGerm_eq (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    coverGerm hcov hd ce = (coverE hcov hd ce, true) := by
  rw [coverE, ← coverGerm_snd hcov hd ce]

theorem src_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.src (coverE hcov hd ce) = coverV hcov hd ce.1.1 := by
  have h := (coverGerm_spec hcov hd ce).1
  rwa [coverGerm_eq hcov hd ce, germSrc_true] at h

theorem tgt_coverE (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (ce : UE K x₀) :
    D.tgt (coverE hcov hd ce) = coverV hcov hd (extend (ce.1.2, true) ce.1.1) := by
  have hcond  := ce.2
  have h := coverV_extend hcov hd (c := ce.1.1) (eb := (ce.1.2, true)) hcond
    (x := coverGerm hcov hd ce) (coverGerm_spec hcov hd ce).1 (coverGerm_spec hcov hd ce).2
  rw [h, coverGerm_eq hcov hd ce, germTgt_true]

/-! ### The lift on two-cells -/

theorem coverF_cond (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    K.base cf.1.2 = p.onV (coverV hcov hd cf.1.1) := by
  rw [onV_coverV]
  exact cf.2.symm

/-- The lift of the universal cover on two-cells. -/
def coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) : D.F :=
  Classical.choose (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))

theorem onF_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    p.onF (coverF hcov hd cf) = cf.1.2 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.1

theorem base_coverF (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (cf : UF K x₀) :
    D.base (coverF hcov hd cf) = coverV hcov hd cf.1.1 :=
  (Classical.choose_spec (exists_unique_liftCell hcov cf.1.2 (coverF_cond hcov hd cf))).1.2

/-! ### Paths -/

/-- The image of an edge path of the universal cover. -/
def mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (L : List (UE K x₀ × Bool)) :
    List (D.E × Bool) :=
  L.map (fun x => (coverE hcov hd x.1, x.2))



theorem isPath_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) :
    ∀ (L : List (UE K x₀ × Bool)) (a b : UV K x₀),
      IsPath (uCover K x₀).src (uCover K x₀).tgt L a b →
        IsPath D.src D.tgt (mapUP hcov hd L) (coverV hcov hd a) (coverV hcov hd b) := by
  intro L
  induction L with
  | nil => intro a b h; exact congrArg (coverV hcov hd) h
  | cons x L ih =>
      intro a b h
      refine ⟨?_, ?_⟩
      · rw [(show germSrc D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germSrc (uCover K x₀).src (uCover K x₀).tgt x) by
        obtain ⟨ce, b⟩ := x
        cases b with
        | true => exact src_coverE hcov hd ce
        | false => exact tgt_coverE hcov hd ce), h.1]
      · have := ih (germTgt (uCover K x₀).src (uCover K x₀).tgt x) b h.2
        rwa [← (show germTgt D.src D.tgt (coverE hcov hd x.1, x.2)
      = coverV hcov hd (germTgt (uCover K x₀).src (uCover K x₀).tgt x) by
          obtain ⟨ce, b⟩ := x
          cases b with
          | true => exact tgt_coverE hcov hd ce
          | false => exact src_coverE hcov hd ce)] at this

theorem mapPath_mapUP (hcov : IsCovering p) (hd : p.onV d₀ = x₀) (L : List (UE K x₀ × Bool)) :
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
  src_onE := fun ce => src_coverE hcov hd ce
  tgt_onE := fun ce => tgt_coverE hcov hd ce
  base_onF := fun cf => base_coverF hcov hd cf
  att_onF := fun cf => by
    have hloop := uAtt_isLoop (X := K) (x₀ := x₀) cf
    have hA : IsPath D.src D.tgt (mapUP hcov hd (uAtt cf)) (coverV hcov hd cf.1.1)
        (coverV hcov hd cf.1.1) := isPath_mapUP hcov hd _ _ _ hloop
    have hproj : mapPath p (mapUP hcov hd (uAtt cf)) = K.att (p.onF (coverF hcov hd cf)) := by
      rw [mapPath_mapUP, onF_coverF]
      exact ((univProj K x₀).att_onF cf).symm
    exact (eq_att_of_lift hcov hA (base_coverF hcov hd cf) hproj).symm

/-! ### Acyclic covers force the Cockcroft property -/

end Comb
end FiniteChains
end

namespace FiniteChains
namespace Comb

universe u

/-! ### Uniqueness of lifts along a covering -/

section Unique

variable {X Z W : Complex2.{u}}

theorem mapPath_comp (g : Hom Z W) (h : Hom X Z) (l : List (X.E × Bool)) :
    mapPath g (mapPath h l) = mapPath (g.comp h) l := by
  simp [mapPath, List.map_map, Function.comp_def, Hom.comp]

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
    simp only [mapPath, List.map_map, Function.comp_def]
    exact List.map_congr_left fun eb _ => by rw [hE eb.1]
  have hlists := liftPath_unique hq (mapPath A m) (mapPath B m) (A.onV x) _ _ hA hB hmap
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
      = (q.onE (B.onE e, true).1, (B.onE e, true).2) := by rw [hE e]
  exact congrArg Prod.fst (liftGerm_unique hq h1 h2 h3)

/-- **Uniqueness of lifts, on two-cells.** -/
theorem lift_onF_eq (hq : IsCovering q) (hF : ∀ f, q.onF (A.onF f) = q.onF (B.onF f))
    (hV : ∀ v, A.onV v = B.onV v) : ∀ f, A.onF f = B.onF f := by
  intro f
  have hv : W.base (q.onF (A.onF f)) = q.onV (A.onV (X.base f)) := by
    rw [q.base_onF, A.base_onF]
  obtain ⟨g, -, huniq⟩ := exists_unique_liftCell hq (q.onF (A.onF f)) hv
  rw [huniq (A.onF f) ⟨rfl, A.base_onF f⟩,
    huniq (B.onF f) ⟨(hF f).symm, by rw [B.base_onF f, hV]⟩]

end Unique

/-! ### The lifting criterion -/

section Lift

variable {D Y : Complex2.{u}}

theorem mapPath_revPath (f : Hom D Y) (m : List (D.E × Bool)) :
    mapPath f (revPath m) = revPath (mapPath f m) := by
  simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]

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
  have hcomb : Htpy Y (f.onV a) (f.onV b) (mapPath f m ++ []) ([] ++ mapPath f m') := by
    refine step1.symm.trans ?_
    rw [← List.append_assoc]
    exact step2
  simpa using hcomb

variable (f : Hom D Y) (hconn : IsConnected D) (d₀ : D.V)

/-- A chosen edge path from the base vertex. -/
def cPath (v : D.V) : List (D.E × Bool) := (hconn d₀ v).choose

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
  rw [extendP_pos hend]
  simp [mapPath, pathFromMap]

variable (f d₀)

/-- The lift of a `π₁`-trivial map to the universal cover, on edges. -/
def liftE (e : D.E) : UE Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.src e), f.onE e), by rw [endV_liftV, f.src_onE]⟩

/-- The lift of a `π₁`-trivial map to the universal cover, on two-cells. -/
def liftF (g : D.F) : UF Y (f.onV d₀) :=
  ⟨(liftV f hconn d₀ (D.base g), f.onF g), by rw [endV_liftV, f.base_onF]⟩

variable {f d₀}

theorem uTgt_liftE (htriv : Pi1Trivial f) (e : D.E) :
    uTgt (liftE f hconn d₀ e) = liftV f hconn d₀ (D.tgt e) :=
  (liftV_extend hconn htriv (e, true)).symm

/-- The lift sends edge paths to edge paths of the universal cover. -/
theorem isPath_map_liftE (htriv : Pi1Trivial f) :
    ∀ (m : List (D.E × Bool)) (a b : D.V), IsPath D.src D.tgt m a b →
      IsPath (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
        (m.map fun eb => (liftE f hconn d₀ eb.1, eb.2))
        (liftV f hconn d₀ a) (liftV f hconn d₀ b) := by
  intro m
  induction m with
  | nil => intro a b hab; exact congrArg _ hab
  | cons eb t ih =>
      intro a b hab
      obtain ⟨ha, hrest⟩ := hab
      refine ⟨?_, ?_⟩
      · obtain ⟨e, s⟩ := eb
        cases s with
        | true => rw [ha]; rfl
        | false =>
            show liftV f hconn d₀ a = uTgt (liftE f hconn d₀ e)
            rw [uTgt_liftE hconn htriv, ha]
            rfl
      · have hgerm : germTgt (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
            (liftE f hconn d₀ eb.1, eb.2) = liftV f hconn d₀ (germTgt D.src D.tgt eb) := by
          obtain ⟨e, s⟩ := eb
          cases s with
          | true => exact uTgt_liftE hconn htriv e
          | false => rfl
        rw [hgerm]
        exact ih _ b hrest

/-- **The lifting criterion.**  A cellular map of a connected complex which kills `π₁` lifts
to the universal cover of its target. -/
def liftHom (htriv : Pi1Trivial f) : Hom D (uCover Y (f.onV d₀)) where
  onV := liftV f hconn d₀
  onE := liftE f hconn d₀
  onF := liftF f hconn d₀
  src_onE := fun _ => rfl
  tgt_onE := fun e => uTgt_liftE hconn htriv e
  base_onF := fun _ => rfl
  att_onF := fun g => by
    have hbase : endV (liftV f hconn d₀ (D.base g)) = Y.base (f.onF g) := by
      rw [endV_liftV, f.base_onF]
    have hpath : IsPath (uCover Y (f.onV d₀)).src (uCover Y (f.onV d₀)).tgt
        ((D.att g).map fun eb => (liftE f hconn d₀ eb.1, eb.2))
        (liftV f hconn d₀ (D.base g)) (liftV f hconn d₀ (D.base g)) :=
      isPath_map_liftE hconn htriv (D.att g) _ _ (D.att_isLoop g)
    have hproj : mapPath (univProj Y (f.onV d₀))
        ((D.att g).map fun eb => (liftE f hconn d₀ eb.1, eb.2)) = Y.att (f.onF g) := by
      rw [f.att_onF g]
      simp [mapPath, List.map_map, Function.comp_def, univProj, liftE]
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
    (liftHom hconn htriv).onV d₀ = UV.base Y (f.onV d₀) := (liftV_eq hconn htriv (m := []) rfl)

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
  have hV := lift_onV_eq hq isConnected_univCover hqE hbase
  have hFeq := lift_onF_eq hq hqF hV
  have hcycle : bdry2 D (chain2 F c) = 0 := by
    rw [bdry2_chain2 F c]
    have h : bdry2 (uCover K (p.onV d₀)) c = 0 := hc
    rw [h, map_zero]
  have hzero : chain2 F c = 0 := hD.h2 (by rw [hcycle, map_zero])
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

variable {c : ℕ → Complex2.{u}}

end Comb
end FiniteChains

namespace FiniteChains.Comb

universe u

variable {K : Complex2.{u}} {x y : K.V} {a : List (K.E × Bool)}
  (ha : IsPath K.src K.tgt a x y)

/-- Prefix the actual path from `x` to `y` to a path starting at `y`. -/
def pathTransportP (p : PathFrom K y) : PathFrom K x :=
  ⟨a ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath ha]
    exact ha.append p.2⟩

theorem endpt_pathTransportP (p : PathFrom K y) :
    endpt K x (pathTransportP ha p).1 = endpt K y p.1 := by grind [endpt_append, endpt_eq_of_isPath, pathTransportP]

/-- Prefixing descends to homotopy classes of paths. -/
def pathTransportV (c : UV K y) : UV K x :=
  Quotient.map (pathTransportP ha) (by
    intro p q hpq
    change Htpy K x (endpt K x (pathTransportP ha p).1)
      (pathTransportP ha p).1 (pathTransportP ha q).1
    rw [endpt_pathTransportP]
    exact Htpy.append_congr ha p.2 (Htpy.refl _) hpq) c

@[simp] theorem pathTransportV_mk (p : PathFrom K y) :
    pathTransportV ha (UV.mk p) = UV.mk (pathTransportP ha p) := rfl

@[simp] theorem endV_pathTransportV (c : UV K y) :
    endV (pathTransportV ha c) = endV c := by
  induction c using UV.ind with
  | h p => exact endpt_pathTransportP ha p

/-- Prefixing commutes with extending a path by an edge, including the
convention that an edge with the wrong source leaves a path unchanged. -/
theorem extend_pathTransportV (eb : K.E × Bool) (c : UV K y) :
    extend eb (pathTransportV ha c) = pathTransportV ha (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (pathTransportP ha p)).1 =
          (pathTransportP ha (extendP eb p)).1 := by
        by_cases h : endpt K y p.1 = germSrc K.src K.tgt eb
        · have h' : endpt K x (pathTransportP ha p).1 = germSrc K.src K.tgt eb := by
            rw [endpt_pathTransportP]
            exact h
          rw [extendP_pos h']
          change (a ++ p.1) ++ [eb] = a ++ (extendP eb p).1
          rw [extendP_pos h]
          exact List.append_assoc _ _ _
        · have h' : ¬ endpt K x (pathTransportP ha p).1 = germSrc K.src K.tgt eb := by
            rw [endpt_pathTransportP]
            exact h
          rw [extendP_neg h']
          change a ++ p.1 = a ++ (extendP eb p).1
          rw [extendP_neg h]
      apply UV.sound
      rw [hl]
      exact Htpy.refl _

/-- Transport an edge by prefixing the path attached to its initial vertex. -/
def pathTransportE (e : UE K y) : UE K x :=
  ⟨(pathTransportV ha e.1.1, e.1.2), by rw [endV_pathTransportV]; exact e.2⟩

/-- Transport a face by prefixing the path attached to its base vertex. -/
def pathTransportF (t : UF K y) : UF K x :=
  ⟨(pathTransportV ha t.1.1, t.1.2), by rw [endV_pathTransportV]; exact t.2⟩


theorem uLiftPath_pathTransportV :
    ∀ (p : List (K.E × Bool)) (c : UV K y) (z : K.V),
      IsPath K.src K.tgt p (endV c) z →
        uLiftPath p (pathTransportV ha c) =
          (uLiftPath p c).map (fun eb => (pathTransportE ha eb.1, eb.2)) := by
  intro p
  induction p with
  | nil => simp
  | cons eb p ih =>
      intro c z hp
      have h  := hp.1
      have h' : endV (pathTransportV ha c) = germSrc K.src K.tgt eb := by
        rw [endV_pathTransportV]
        exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons,
        (show liftGerm (pathTransportV ha c) eb h' =
      (pathTransportE ha (liftGerm c eb h).1, (liftGerm c eb h).2) by
          obtain ⟨e, b⟩ := eb
          cases b with
          | true => rfl
          | false =>
              refine Prod.ext ?_ rfl
              apply Subtype.ext
              exact Prod.ext (extend_pathTransportV ha (e, false) c) rfl), extend_pathTransportV ha eb c,
        ih (extend eb c) z (by rw [endV_extend h]; exact hp.2)]

/-- The actual cellular change of universal-cover base along `a : x ⟶ y`. -/
def uCoverPathTransport : Hom (uCover K y) (uCover K x) where
  onV := pathTransportV ha
  onE := pathTransportE ha
  onF := pathTransportF ha
  src_onE := fun _ => rfl
  tgt_onE := fun e => extend_pathTransportV ha (e.1.2, true) e.1.1
  base_onF := fun _ => rfl
  att_onF := by
    intro t
    change uLiftPath (K.att t.1.2) (pathTransportV ha t.1.1) = _
    apply uLiftPath_pathTransportV
    rw [t.2]
    exact K.att_isLoop t.1.2

theorem uCoverPathTransport_base :
    (uCoverPathTransport ha).onV (UV.base K y) =
      UV.mk ⟨a, by rw [endpt_eq_of_isPath ha]; exact ha⟩ := by
  apply congrArg UV.mk
  exact Subtype.ext (List.append_nil a)

/-- Prefix transport intertwines the deck actions by conjugation along the same path. -/
theorem uCoverPathTransport_deckV (γ : Pi1 K y) (c : UV K y) :
    (uCoverPathTransport ha).onV (deckV γ c) =
      deckV (pi1Conj ha γ) ((uCoverPathTransport ha).onV c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          apply UV.sound
          change Htpy K x (endpt K x (a ++ (g.1 ++ p.1)))
            (a ++ (g.1 ++ p.1)) ((a ++ g.1 ++ revPath a) ++ (a ++ p.1))
          rw [endpt_append, endpt_eq_of_isPath ha,
            endpt_append, endpt_eq_of_isPath g.2]
          have h := (htpy_revPath_append ha).congr_append (ha.append g.2) p.2
          simpa using h.symm

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {o a b : X.V}

/-- Path extension commutes with every actual deck transformation. -/
theorem extendList_deckV (g : Pi1 X o) (p : List (X.E × Bool)) (v : UV X o) :
    extendList p (deckV g v) = deckV g (extendList p v) := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih => rw [extendList_cons, extend_deckV, ih, extendList_cons]

/-- A loop acting on the base cover vertex is its actual lifted endpoint. -/
theorem deckV_loop_base (l : Loop X o) :
    deckV (Pi1.mk l) (UV.base X o) = extendList l.1 (UV.base X o) := by
  let r : PathFrom X o := ⟨l.1, by rw [endpt_eq_of_isPath l.2]; exact l.2⟩
  have h : extendList l.1 (UV.base X o) = UV.mk r :=
    extendList_mk l.2 rfl
  rw [h]
  apply Quotient.sound
  change Htpy X o (endpt X o (l.1 ++ [])) (l.1 ++ []) l.1
  simp
  exact Htpy.refl _

/-- The endpoint after a path is the translated reference endpoint at its target. -/
theorem extendList_reference_gauge
    {r p s : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r o a) (hp : IsPath X.src X.tgt p a b)
    (hs : IsPath X.src X.tgt s o b) :
    extendList p (extendList r (UV.base X o)) =
      deckV (Pi1.mk ⟨r ++ p ++ revPath s, (hr.append hp).append (isPath_revPath hs)⟩)
        (extendList s (UV.base X o)) := by
  rw [← extendList_deckV, deckV_loop_base, ← extendList_append, ← extendList_append]
  have h : Htpy X o b (r ++ p) ((r ++ p ++ revPath s) ++ s) := by
    have hc := Htpy.append_congr (hr.append hp)
      ((isPath_revPath hs).append hs) (Htpy.refl (r ++ p)) (htpy_revPath_append hs)
    simpa using hc.symm
  exact extendList_htpy (hr.append hp) h

end FiniteChains.Comb
end

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)

def mappedTreeReference (a : K.V) : UV Y (f.onV T.root) :=
  extendList (mapPath f (T.treePath a)) (UV.base Y (f.onV T.root))

theorem mappedTreeReference_end (a : K.V) :
    endV (mappedTreeReference T f a) = f.onV a :=
  endV_extendList (isPath_mapPath f (T.treePath_isPath a))

/-- The geometric comparison reference paths have exactly the translation read by the tree. -/
theorem mappedTreeReference_path {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    extendList (mapPath f p) (mappedTreeReference T f a) =
      deckV (pi1Map f T.root (freeToPi1 T (pathWord T p)))
        (mappedTreeReference T f b) := by
  rw [freeToPi1_pathWord T hp]
  have h := extendList_reference_gauge
    (isPath_mapPath f (T.treePath_isPath a)) (isPath_mapPath f hp)
    (isPath_mapPath f (T.treePath_isPath b))
  have he : mapPath f (conjPath T p a b) =
      mapPath f (T.treePath a) ++ mapPath f p ++ revPath (mapPath f (T.treePath b)) := by
    rw [conjPath, mapPath_append, mapPath_append, mapPath_revPath]
  have hv : pi1Map f T.root (loopOf T hp) =
      Pi1.mk ⟨mapPath f (T.treePath a) ++ mapPath f p ++ revPath (mapPath f (T.treePath b)),
        ((isPath_mapPath f (T.treePath_isPath a)).append (isPath_mapPath f hp)).append
          (isPath_revPath (isPath_mapPath f (T.treePath_isPath b)))⟩ := by
    apply congrArg Pi1.mk
    apply Subtype.ext
    exact he
  rw [hv]
  exact h

end FiniteChains.Comb.SpanningTree

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))

def receiverVertex (g : G) (a : K.V) : UV Y (f.onV T.root) :=
  deckV (ψ g) (mappedTreeReference T f a)

theorem receiverVertex_end (g : G) (a : K.V) :
    endV (receiverVertex T f ψ g a) = f.onV a := by
  rw [receiverVertex, endV_deckV, mappedTreeReference_end]

variable (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

include hψ in
theorem receiver_word (w : FreeGroup (NonTree T)) :
    ψ (φ (QuotientGroup.mk w)) = pi1Map f T.root (SpanningTree.freeToPi1 T w) :=
  DFunLike.congr_fun hψ (QuotientGroup.mk w)

include hψ in
/-- The actual geometric endpoint changes by exactly the received tree word. -/
theorem receiverVertex_path (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    extendList (mapPath f p) (receiverVertex T f ψ g a) =
      receiverVertex T f ψ (g * wordValue T φ p) b := by grind [extendList_deckV, mappedTreeReference_path, map_mul, deckV_mul, wordValue, receiver_word, receiverVertex]

def receiverEdge (g : G) (e : K.E) : UE Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.src e), f.onE e), by
    rw [receiverVertex_end, f.src_onE]⟩

include hψ in
theorem receiverEdge_tgt (g : G) (e : K.E) :
    uTgt (receiverEdge T f ψ g e) =
      receiverVertex T f ψ (g * germValue T φ (e, true)) (K.tgt e) := by
  have h := receiverVertex_path T f φ ψ hψ g (isPath_single (e, true))
  simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
    wordValue_cons, wordValue_nil, mul_one, receiverEdge, uTgt, germSrc, germTgt, if_true] using h

def receiverFace (g : G) (t : K.F) : UF Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.base t), f.onF t), by
    rw [receiverVertex_end, f.base_onF]⟩

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

def receiverGerm (e : (G × K.E) × Bool) : UE Y (f.onV T.root) × Bool :=
  (receiverEdge T f ψ e.1.1 e.1.2, e.2)


include hψ in
/-- Every actual lifted edge path has the claimed geometric image. -/
theorem comparison_liftPath (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    (liftPath T φ p g).map (receiverGerm T f ψ) =
      uLiftPath (mapPath f p) (receiverVertex T f ψ g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    have hs : endV (receiverVertex T f ψ g (germSrc K.src K.tgt e)) =
        germSrc Y.src Y.tgt (f.onE e.1, e.2) := by
      rw [receiverVertex_end, germSrc_onE]
    have he : extend (f.onE e.1, e.2)
        (receiverVertex T f ψ g (germSrc K.src K.tgt e)) =
        receiverVertex T f ψ (g * germValue T φ e) (germTgt K.src K.tgt e) := by
      have h := receiverVertex_path T f φ ψ hψ g (isPath_single e)
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using h
    rw [liftPath_cons, List.map_cons]
    change receiverGerm T f ψ (liftGerm T φ g e) :: _ =
      uLiftPath ((f.onE e.1, e.2) :: mapPath f p) _
    rw [uLiftPath_cons hs, he]
    apply congrArg₂ List.cons
    · exact (by
      obtain ⟨e, b⟩ := e
      cases b with
      | true => rfl
      | false =>
        have h := receiverVertex_path T f φ ψ hψ g (isPath_single (e, false))
        have he : extend (f.onE e, false) (receiverVertex T f ψ g (K.tgt e)) =
            receiverVertex T f ψ (g * germValue T φ (e, false)) (K.src e) := by
          simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
            wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using h
        apply Prod.ext
        · apply Subtype.ext
          apply Prod.ext
          · exact he.symm
          · rfl
        · rfl)
    · grind

/-- The comparison is an actual cellular map, not a postulated chain map. -/
def comparison : Hom (cover T φ) (uCover Y (f.onV T.root)) where
  onV x := receiverVertex T f ψ x.1 x.2
  onE x := receiverEdge T f ψ x.1 x.2
  onF x := receiverFace T f ψ x.1 x.2
  src_onE _ := rfl
  tgt_onE x := receiverEdge_tgt T f φ ψ hψ x.1 x.2
  base_onF _ := rfl
  att_onF x := by
    change uLiftPath (Y.att (f.onF x.2)) (receiverVertex T f ψ x.1 (K.base x.2)) =
      (liftPath T φ (K.att x.2) x.1).map (receiverGerm T f ψ)
    rw [f.att_onF]
    exact (comparison_liftPath T f φ ψ hψ x.1 (K.att_isLoop x.2)).symm

theorem comparison_bdry2 (c : (G × K.F) →₀ ℤ) :
    bdry2 (uCover Y (f.onV T.root)) (chain2 (comparison T f φ ψ hψ) c) =
      chain1 (comparison T f φ ψ hψ) (bdry2 (cover T φ) c) :=
  bdry2_chain2 (comparison T f φ ψ hψ) c

/-- For the receiving group pi1(Y), the compatibility triangle is an identity.
This gives the genuine comparison without an extra mathematical assumption. -/
def canonicalReceiver : PresGroup (treeRel T) →* Pi1 Y (f.onV T.root) :=
  (pi1Map f T.root).comp (SpanningTree.presToPi1 T)

end FiniteChains.Comb.ReceivedTree

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

theorem comparison_pathChain (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    chain1 (comparison T f φ ψ hψ) (pathChain (liftPath T φ p g)) =
      pathChain (uLiftPath (mapPath f p) (receiverVertex T f ψ g a)) := by
  change Finsupp.mapDomain (comparison T f φ ψ hψ).onE
    (pathChain (liftPath T φ p g)) = _
  erw [← pathChain_map (comparison T f φ ψ hψ)]
  exact congrArg pathChain (comparison_liftPath T f φ ψ hψ g hp)

variable {I : Type u}

/-- The translated marked paths in the actual path-class universal cover of Y. -/
def geometricMarkedChainMap (p : I → Loop K T.root) :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((uCover Y (f.onV T.root)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain
    (uLiftPath (mapPath f (p x.2).1) (receiverVertex T f ψ x.1 T.root)))

theorem comparison_markedChainMap (p : I → Loop K T.root) (c : (G × I) →₀ ℤ) :
    chain1 (comparison T f φ ψ hψ) (markedChainMap T φ (fun i => (p i).1) c) =
      geometricMarkedChainMap T f ψ p c := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd => simp_all
  | single x n =>
    obtain ⟨g, i⟩ := x
    erw [markedChainMap_single, map_smul, comparison_pathChain T f φ ψ hψ g (p i).2,
      geometricMarkedChainMap, Finsupp.linearCombination_single]

variable [Fintype I] [DecidableEq (NonTree T)]

/-- The coordinate condition alone gives a genuine two-chain with exactly the
specified translated marked boundary in the geometric universal cover. The
receiver compatibility is explicit; injectivity is not inferred from it. -/
theorem comparison_relative_boundary (p : I → Loop K T.root)
    (γ : I → MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ)
    (hc : ∀ z : NonTree T, cellCoefficient z.1 (bdry2 (cover T φ) c) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1))) :
    bdry2 (uCover Y (f.onV T.root)) (chain2 (comparison T f φ ψ hψ) c) =
      geometricMarkedChainMap T f ψ p ((cellCoordinates I).symm γ) := by
  erw [comparison_bdry2, bdry2_eq_markedChain_of_coordinates T φ p γ c hc]
  exact comparison_markedChainMap T f φ ψ hψ p _

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- The four signed actual incidence edges for one letter of the attaching circle. -/
def relatorCircleLetterChain (k : Fin (w j).length) :
    StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  Finsupp.single (relatorCircleEdge0 w j k) 1 -
    Finsupp.single (relatorCircleEdge1 w j k) 1 +
    Finsupp.single (relatorCircleEdge2 w j k) 1 -
    Finsupp.single (relatorCircleEdge3 w j k) 1

theorem relatorCircleLetterChain_boundary (k : Fin (w j).length) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleLetterChain w j k) =
      Finsupp.single (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) 1 -
      Finsupp.single (relatorCirclePoint w j k CPos.cor) 1 := by
  simp only [relatorCircleLetterChain, map_add, map_sub, Comb.bdry1_single (X := strictOrderCx (RelatorCircle w j)), one_smul]
  simp [strictOrderCx,
    relatorCircleEdge0, relatorCircleEdge1, relatorCircleEdge2, relatorCircleEdge3]

/-- The genuine finite attaching-circle fundamental chain. -/
def relatorCircleFundamentalChain : StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  ∑ k : Fin (w j).length, relatorCircleLetterChain w j k

theorem relatorCircleLetterChain_edge0 (l k : Fin (w j).length) :
    relatorCircleLetterChain w j l (relatorCircleEdge0 w j k) = if l = k then 1 else 0 := by
  by_cases h : l = k
  · subst l
    simp [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1,
      relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
      RelatorCircle, StrictOrdEdge, TCirc]
  · have hv : l.val ≠ k.val := fun he => h (Fin.ext he)
    simp [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1,
      relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
      RelatorCircle, StrictOrdEdge, TCirc, hv, h]

theorem relatorCircleFundamentalChain_cycle :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleFundamentalChain w j) = 0 := by
  rw [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_boundary]
  rw [Finset.sum_sub_distrib]
  let e  := Equiv.ofBijective
    (relatorCircleNext w j) ⟨relatorCircleNext_injective w j,
      Finite.surjective_of_injective (relatorCircleNext_injective w j)⟩
  have he := e.sum_comp (fun k =>
    Finsupp.single (relatorCirclePoint w j k CPos.cor) (1 : ℤ))
  rw [show (∑ k, Finsupp.single
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) 1) =
      ∑ k, Finsupp.single (relatorCirclePoint w j k CPos.cor) (1 : ℤ) from he, sub_self]

theorem relatorCircleFundamentalChain_edge0 (k : Fin (w j).length) :
    relatorCircleFundamentalChain w j (relatorCircleEdge0 w j k) = 1 := by
  simp [relatorCircleFundamentalChain, relatorCircleLetterChain_edge0]

/-- Every actual attaching-circle cycle is the corresponding integer multiple of
its genuine fundamental chain. -/
theorem relatorCircle_cycle_eq_smul_fundamental
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) :
    c = c (relatorCircleEdge0 w j ⟨0, hpos⟩) • relatorCircleFundamentalChain w j := by
  refine relatorCircle_cycle_ext w j c _ hc ?_ hpos ?_
  · rw [map_smul, relatorCircleFundamentalChain_cycle, smul_zero]
  · simp [relatorCircleFundamentalChain_edge0]

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) : PresPos w := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

theorem relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j) :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α : Type u}

def roseBaseEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.base, Rose.edg i b), lt_of_le_of_ne (Rose.base_le_edg i b) (by intro h; cases h)⟩

def roseMidEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.mid i, Rose.edg i b), lt_of_le_of_ne (Rose.mid_le_edg i b) (by intro h; cases h)⟩

/-- The actual strict rose edges are exactly the two half-incidences for each generator end. -/
theorem rose_strict_edge_cases (e : StrictOrdEdge (Rose α)) :
    ∃ i b, e = roseBaseEdge i b ∨ e = roseMidEdge i b := by
  rcases e with ⟨⟨a, b⟩, h⟩
  have hl := h.le
  have hn := h.ne
  cases a with
  | base =>
    cases b with
    | base => exact (hn rfl).elim
    | mid i => exact hl.elim
    | edg i b => exact ⟨i, b, Or.inl (Subtype.ext rfl)⟩
  | mid i =>
    cases b with
    | base => exact hl.elim
    | mid k =>
      subst k
      exact (hn rfl).elim
    | edg k b =>
      subst k
      exact ⟨i, b, Or.inr (Subtype.ext rfl)⟩
  | edg i s =>
    cases b with
    | base => exact hl.elim
    | mid k => exact hl.elim
    | edg k c =>
      rcases hl with ⟨rfl, rfl⟩
      exact (hn rfl).elim

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Read an actual universal-cover vertex from its actual path class. -/
def readVertex : UV (orderCx P) a → G :=
  Quotient.lift (fun p : PathFrom (orderCx P) a => c.readPath p.val)
    (fun _ _ h => c.readPath_htpy h)

@[simp] theorem readVertex_mk (p : PathFrom (orderCx P) a) :
    c.readVertex a (UV.mk p) = c.readPath p.val := rfl

@[simp] theorem readVertex_base : c.readVertex a (UV.base (orderCx P) a) = 1 := rfl

/-- The actual vertex reading is equivariant for the actual path-class deck action. -/
theorem readVertex_deck (g : Pi1 (orderCx P) a) (p : UV (orderCx P) a) :
    c.readVertex a (deckV g p) = c.monodromy a g * c.readVertex a p := by
  induction g using Quotient.inductionOn with
  | h g =>
    induction p using Quotient.inductionOn with
    | h p => exact c.readPath_append g.val p.val

/-- Appending an actual oriented edge multiplies the actual vertex reading by its cocycle value. -/
theorem readVertex_extend (e : (orderCx P).E × Bool) (p : UV (orderCx P) a)
    (h : endV p = germSrc (orderCx P).src (orderCx P).tgt e) :
    c.readVertex a (extend e p) = c.readVertex a p * c.readGerm e := by
  induction p using Quotient.inductionOn with
  | h p =>
    change c.readPath (extendP e p).val = c.readPath p.val * c.readGerm e
    rw [extendP_pos h, c.readPath_append]
    simp

/-- Faithful monodromy makes actual vertex reading injective on each actual endpoint fibre. -/
theorem readVertex_fibre_injective (hc : Function.Injective (c.monodromy a))
    (p q : UV (orderCx P) a) (he : endV p = endV q)
    (hr : c.readVertex a p = c.readVertex a q) : p = q := by
  obtain ⟨g, hg, _⟩ := (isRegular_univProj).simply_transitive p q he
  change deckV g p = q at hg
  have hm := c.readVertex_deck a g p
  rw [hg, ← hr] at hm
  have hone  := mul_right_cancel
    (hm.symm.trans (one_mul (c.readVertex a p)).symm)
  have hg1  := hc (hone.trans (map_one (c.monodromy a)).symm)
  rw [hg1, deckV_one] at hg
  exact hg

/-- Surjective monodromy makes vertex reading surjective on every inhabited actual endpoint fibre. -/
theorem readVertex_fibre_surjective (hc : Function.Surjective (c.monodromy a))
    (p : UV (orderCx P) a) (z : G) :
    ∃ q : UV (orderCx P) a, endV q = endV p ∧ c.readVertex a q = z := by
  obtain ⟨g, hg⟩ := hc (z * (c.readVertex a p)⁻¹)
  refine ⟨deckV g p, endV_deckV g p, ?_⟩
  rw [c.readVertex_deck, hg]
  simp [mul_assoc]

end FiniteChains.Comb.OrdCocycle
end

namespace FiniteChains.Comb
universe u

/-- A null loop obtained by closing a path with a reverse path proves the two paths homotopic. -/
theorem htpy_of_append_rev_null {X : Complex2.{u}} {a b : X.V}
    {p q : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a b)
    (hq : IsPath X.src X.tgt q a b) (h : Htpy X a a (p ++ revPath q) []) :
    Htpy X a b p q := by
  have hc := (htpy_revPath_append hq).congr_append hp (show IsPath X.src X.tgt [] b b from rfl)
  have hh := h.congr_append (show IsPath X.src X.tgt [] a a from rfl) hq
  have hc' : Htpy X a b ((p ++ revPath q) ++ q) p := by
    simpa using hc
  have hh' : Htpy X a b ((p ++ revPath q) ++ q) q := by
    simpa using hh
  exact hc'.symm.trans hh'

/-- Every actual path below a fixed apex is homotopic to the two-edge path through that apex. -/
theorem htpy_path_through_upper_bound {P : Type u} [Preorder P]
    (d : P) {a b : P} (ha : a ≤ d) (hb : b ≤ d)
    {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hs : PathIn (fun x => x ≤ d) p) :
    Htpy (orderCx P) a b p [ordPos ha, ordNeg hb] := by
  have hq : IsPath (orderCx P).src (orderCx P).tgt [ordPos ha, ordNeg hb] a b :=
    ⟨rfl, rfl, rfl⟩
  have hqs : PathIn (fun x => x ≤ d) [ordPos ha, ordNeg hb] :=
    pathIn_cons ⟨ha, le_refl d⟩ (pathIn_cons ⟨hb, le_refl d⟩ (pathIn_nil _))
  apply htpy_of_append_rev_null hp hq
  exact htpy_nil_of_pathIn_le d ha (hp.append (isPath_revPath hq))
    (pathIn_append hs (pathIn_revPath hqs))

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- An actual order isomorphism is surjective on based fundamental groups. -/
theorem orderIso_pi1_surjective (e : P ≃o Q) (a : P) :
    Function.Surjective (pi1Map (orderCxMap e e.monotone) a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have hp : IsPath (orderCx P).src (orderCx P).tgt
        (mapPath (orderCxMap e.symm e.symm.monotone) p.val) a a := by
      simpa using
        isPath_mapPath (orderCxMap e.symm e.symm.monotone) p.property
    refine ⟨Pi1.mk ⟨_, hp⟩, Quotient.sound ?_⟩
    change Htpy (orderCx Q) (e a) (e a)
      (mapPath (orderCxMap e e.monotone)
        (mapPath (orderCxMap e.symm e.symm.monotone) p.val)) p.val
    rw [mapPath_comp_eq_self e.symm.monotone e.monotone e.apply_symm_apply]
    exact Htpy.refl _

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {o a b c : X.V}

/-- The actual based loop obtained by joining a path to chosen paths from the root. -/
def rootedPathLoop (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a)
    (p : List (X.E × Bool)) (hp : IsPath X.src X.tgt p a b)
    (s : List (X.E × Bool)) (hs : IsPath X.src X.tgt s o b) : Loop X o :=
  ⟨r ++ p ++ revPath s, (hr.append hp).append (isPath_revPath hs)⟩

/-- Actual rooted path classes multiply by concatenation; the intermediate root path cancels. -/
theorem rootedPathLoop_append (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a)
    (p : List (X.E × Bool)) (hp : IsPath X.src X.tgt p a b)
    (s : List (X.E × Bool)) (hs : IsPath X.src X.tgt s o b)
    (q : List (X.E × Bool)) (hq : IsPath X.src X.tgt q b c)
    (t : List (X.E × Bool)) (ht : IsPath X.src X.tgt t o c) :
    Pi1.mk (rootedPathLoop r hr (p ++ q) (hp.append hq) t ht) =
      Pi1.mk (rootedPathLoop r hr p hp s hs) *
        Pi1.mk (rootedPathLoop s hs q hq t ht) := by
  apply Quotient.sound
  have h := (htpy_revPath_append hs).congr_append (hr.append hp)
    (hq.append (isPath_revPath ht))
  change Htpy X o o ((r ++ (p ++ q)) ++ revPath t)
    ((r ++ p ++ revPath s) ++ (s ++ q ++ revPath t))
  simpa using h.symm

/-- Closing the empty actual path at a vertex gives the trivial based loop. -/
theorem rootedPathLoop_nil (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a) :
    Pi1.mk (rootedPathLoop r hr [] rfl r hr) = 1 := by
  apply Quotient.sound
  change Htpy X o o _ _
  simpa only [rootedPathLoop, List.append_nil] using htpy_append_revPath hr

/-- Close an actual oriented edge by actual paths from the root to its endpoints. -/
def rootedGermLoop (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v) (e : X.E × Bool) : Loop X o :=
  rootedPathLoop (r (germSrc X.src X.tgt e)) (hr _) [e] (isPath_single e)
    (r (germTgt X.src X.tgt e)) (hr _)

/-- Every actual rooted path class factors into its actual rooted single-edge classes. -/
theorem rootedPathLoop_eq_prod (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v)
    (p : List (X.E × Bool)) (a b : X.V) (hp : IsPath X.src X.tgt p a b) :
    Pi1.mk (rootedPathLoop (r a) (hr a) p hp (r b) (hr b)) =
      (p.map (fun e => Pi1.mk (rootedGermLoop r hr e))).prod := by
  induction p generalizing a with
  | nil =>
    subst b
    exact rootedPathLoop_nil _ _
  | cons e p ih =>
    obtain ⟨he, hp⟩ := hp
    subst a
    have h := rootedPathLoop_append (r (germSrc X.src X.tgt e)) (hr _)
      [e] (isPath_single e) (r (germTgt X.src X.tgt e)) (hr _) p hp (r b) (hr b)
    simpa only [List.singleton_append, List.map_cons, List.prod_cons,
      rootedGermLoop, ih _ hp] using h

/-- Reversing an actual rooted germ inverts its actual loop class. -/
theorem rootedGermLoop_rev (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v) (e : X.E × Bool) :
    Pi1.mk (rootedGermLoop r hr (revGerm e)) =
      (Pi1.mk (rootedGermLoop r hr e))⁻¹ := by
  apply Quotient.sound
  simp only [rootedGermLoop, rootedPathLoop, germSrc_revGerm, germTgt_revGerm,
    revPath_append, revPath_revPath, revPath_cons, revPath_nil,
    List.nil_append, List.append_assoc]
  exact Htpy.refl _

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α : Type u}

/-- Concrete paths from the rose base along the chosen spanning tree. -/
def roseRootPath : Rose α → List ((orderCx (Rose α)).E × Bool)
  | .base => []
  | .mid i => [ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false)]
  | .edg i b => [ordPos (Rose.base_le_edg i b)]

theorem roseRootPath_isPath (v : Rose α) :
    IsPath (orderCx (Rose α)).src (orderCx (Rose α)).tgt (roseRootPath v) Rose.base v := by
  cases v with
  | base => rfl
  | mid i => exact ⟨rfl, rfl, rfl⟩
  | edg i b => exact ⟨rfl, rfl⟩

/-- The actual four-edge generator loop in the rose. -/
def roseGeneratorLoop (i : α) : Loop (orderCx (Rose α)) Rose.base :=
  ⟨[ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false),
    ordPos (Rose.mid_le_edg i true), ordNeg (Rose.base_le_edg i true)],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Every rooted base incidence is a tree loop and has trivial actual class. -/
theorem roseRooted_base (i : α) (b : Bool) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.base_le_edg i b))) = 1 := by
  apply Quotient.sound
  exact htpy_append_revPath (isPath_ordPos (Rose.base_le_edg i b))

/-- The remaining tree incidence at the midpoint has trivial actual class. -/
theorem roseRooted_mid_false (i : α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.mid_le_edg i false))) = 1 := by
  apply Quotient.sound
  have h := (htpy_revPath_append (isPath_ordPos (Rose.mid_le_edg i false))).congr_append
    (isPath_ordPos (Rose.base_le_edg i false))
    (isPath_revPath (isPath_ordPos (Rose.base_le_edg i false)))
  have h' : Htpy (orderCx (Rose α)) Rose.base Rose.base
      [ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false),
        ordPos (Rose.mid_le_edg i false), ordNeg (Rose.base_le_edg i false)]
      [ordPos (Rose.base_le_edg i false), ordNeg (Rose.base_le_edg i false)] := by
    simpa using h
  exact h'.trans (htpy_append_revPath (isPath_ordPos (Rose.base_le_edg i false)))

/-- The non-tree midpoint incidence closes to the concrete generator loop. -/
theorem roseRooted_mid_true (i : α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.mid_le_edg i true))) = Pi1.mk (roseGeneratorLoop i) := rfl

/-- Reflexive actual rose edges contribute no rooted loop class. -/
theorem roseRooted_self (v : Rose α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (le_refl v))) = 1 := by
  apply Quotient.sound
  have h := (htpy_ordSelf_nil v).congr_append (roseRootPath_isPath v)
    (isPath_revPath (roseRootPath_isPath v))
  have h' : Htpy (orderCx (Rose α)) Rose.base Rose.base
      (roseRootPath v ++ [ordPos (le_refl v)] ++ revPath (roseRootPath v))
      (roseRootPath v ++ revPath (roseRootPath v)) := by
    simpa using h
  exact h'.trans (htpy_append_revPath (roseRootPath_isPath v))

/-- Every positive actual rose germ class is in the image of the concrete generator map. -/
theorem roseRooted_positive_mem_range (e : OrdEdge (Rose α)) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath (e, true)) ∈
      (loopHom (roseGeneratorLoop (α := α))).range := by
  rcases e with ⟨⟨a, b⟩, h⟩
  by_cases hab : a = b
  · subst b
    change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (le_refl a))) ∈ _
    rw [roseRooted_self]
    exact Subgroup.one_mem _
  · let d : StrictOrdEdge (Rose α) := ⟨(a, b), lt_of_le_of_ne h hab⟩
    obtain ⟨i, c, hd | hd⟩ := rose_strict_edge_cases d
    · have he : ⟨(a, b), h⟩ =
          (ordPos (Rose.base_le_edg i c)).1 :=
        Subtype.ext (congrArg (fun z : StrictOrdEdge (Rose α) => z.val) hd)
      rw [he]
      change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
        (ordPos (Rose.base_le_edg i c))) ∈ _
      rw [roseRooted_base]
      exact Subgroup.one_mem _
    · have he : ⟨(a, b), h⟩ =
          (ordPos (Rose.mid_le_edg i c)).1 :=
        Subtype.ext (congrArg (fun z : StrictOrdEdge (Rose α) => z.val) hd)
      change Pi1.mk (rootedGermLoop (X := orderCx (Rose α)) roseRootPath roseRootPath_isPath
        (⟨(a, b), h⟩, true)) ∈ _
      rw [he]
      change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
        (ordPos (Rose.mid_le_edg i c))) ∈ _
      cases c
      · rw [roseRooted_mid_false]
        exact Subgroup.one_mem _
      · rw [roseRooted_mid_true]
        exact ⟨FreeGroup.of i, loopHom_of _ _⟩

/-- Every oriented actual rose germ class lies in the image of its generator map. -/
theorem roseRooted_mem_range (e : (orderCx (Rose α)).E × Bool) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath e) ∈
      (loopHom (roseGeneratorLoop (α := α))).range := by
  rcases e with ⟨e, b⟩
  cases b
  · have h := rootedGermLoop_rev roseRootPath roseRootPath_isPath (e, true)
    change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath (e, false)) = _ at h
    rw [h]
    exact Subgroup.inv_mem _ (roseRooted_positive_mem_range e)
  · exact roseRooted_positive_mem_range e

/-- The actual rose fundamental group is generated by its concrete generator loops. -/
theorem roseLoopHom_surjective :
    Function.Surjective (loopHom (roseGeneratorLoop (α := α))) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have h := rootedPathLoop_eq_prod roseRootPath roseRootPath_isPath p.val
      Rose.base Rose.base p.property
    simp only [rootedPathLoop, roseRootPath, revPath_nil (X := orderCx (Rose α)), List.nil_append,
      List.append_nil] at h
    have hm : (p.val.map (fun e =>
        Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath e))).prod ∈
        (loopHom (roseGeneratorLoop)).range := by
      induction p.val with
      | nil => simp
      | cons e l ih =>
        exact Subgroup.mul_mem _ (roseRooted_mem_range e) ih
    rw [← h] at hm
    exact hm

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Consecutive actual circle corners lie in the same actual edge-path component. -/
theorem relatorCircle_corner_component_next (k : Fin (w j).length) :
    orderComponentLabel (RelatorCircle w j)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
    orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j k CPos.cor) :=
  (orderComponentLabel_eq_of_le (relatorCircleEdge3 w j k).property.le).trans
    ((orderComponentLabel_eq_of_le (relatorCircleEdge2 w j k).property.le).symm.trans
      ((orderComponentLabel_eq_of_le (relatorCircleEdge1 w j k).property.le).trans
        (orderComponentLabel_eq_of_le (relatorCircleEdge0 w j k).property.le).symm))

/-- Every actual circle corner is connected to the actual initial corner. -/
theorem relatorCircle_corner_component_zero (hpos : 0 < (w j).length)
    (k : Fin (w j).length) :
    orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j k CPos.cor) =
      orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
  have h : ∀ n hn,
      orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j ⟨n, hn⟩ CPos.cor) =
        orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hn' : n < (w j).length := by omega
      have he : relatorCircleNext w j ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
        ext
        exact Nat.mod_eq_of_lt hn
      exact (he ▸ relatorCircle_corner_component_next w j ⟨n, hn'⟩).trans (ih hn')
  simp_all

/-- Each nonempty genuine relator circle is connected by actual order-complex edge paths. -/
theorem relatorCircle_isConnected (hpos : 0 < (w j).length) :
    IsConnected (orderCx (RelatorCircle w j)) := by
  have h : ∀ x : RelatorCircle w j,
      orderComponentLabel (RelatorCircle w j) x =
        orderComponentLabel (RelatorCircle w j) (relatorCirclePoint w j ⟨0, hpos⟩ CPos.cor) := by
    rintro ⟨⟨j', k, t⟩, hj, hk⟩
    change j' = j at hj
    subst j'
    let n : Fin (w j).length := ⟨k, hk⟩
    have hc := relatorCircle_corner_component_zero w j hpos n
    cases t with
    | cor => exact hc
    | cmid =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge1 w j n).property.le).trans
          ((orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc)
    | cedgL =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc
    | cedgR =>
        exact (orderComponentLabel_eq_of_le (relatorCircleEdge2 w j n).property.le).symm.trans
          ((orderComponentLabel_eq_of_le (relatorCircleEdge1 w j n).property.le).trans
            ((orderComponentLabel_eq_of_le (relatorCircleEdge0 w j n).property.le).symm.trans hc))
  intro x y
  exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Actual mapped circle paths remain below their actual presentation apex. -/
theorem relatorCirclePath_below_apex (l : List ((orderCx (RelatorCircle w j)).E × Bool)) :
    PathIn (fun p => p ≤ apexOf w j)
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(relatorCirclePresInclusion_lt_apex w j r.1.val.1).le,
    (relatorCirclePresInclusion_lt_apex w j r.1.val.2).le⟩

/-- Actual mapped circle paths stay in the actual cylinder part of the presentation poset. -/
theorem relatorCirclePath_in_cylinder (l : List ((orderCx (RelatorCircle w j)).E × Bool)) :
    PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨⟨cylOuter (aHom w) r.1.val.1.val, rfl⟩,
    ⟨cylOuter (aHom w) r.1.val.2.val, rfl⟩⟩

/-- An actual two-edge apex excursion can be replaced by an actual path in the cylinder. -/
theorem exists_presCone_excursion_replacement (hpos : 0 < (w j).length)
    (x y : RelatorCircle w j) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l (iCirc w x.val) (iCirc w y.val) ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) (iCirc w x.val) (iCirc w y.val)
        [ordPos (relatorCirclePresInclusion_lt_apex w j x).le,
          ordNeg (relatorCirclePresInclusion_lt_apex w j y).le] l := by
  obtain ⟨l, hl⟩ := relatorCircle_isConnected w j hpos x y
  let I := orderCxMap (relatorCirclePresInclusion w j)
    (relatorCirclePresInclusion_strictMono w j).monotone
  refine ⟨mapPath I l, isPath_mapPath I hl, relatorCirclePath_in_cylinder w j l, ?_⟩
  exact (htpy_path_through_upper_bound (apexOf w j)
    (relatorCirclePresInclusion_lt_apex w j x).le
    (relatorCirclePresInclusion_lt_apex w j y).le
    (isPath_mapPath I hl) (relatorCirclePath_below_apex w j l)).symm

/-- Every genuine apex excursion, with arbitrary actual strict lower endpoints, has a cylinder replacement. -/
theorem exists_presCone_strict_excursion_replacement (hpos : 0 < (w j).length)
    (x y : PresPos w) (hx : x < apexOf w j) (hy : y < apexOf w j) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l x y ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) x y [ordPos hx.le, ordNeg hy.le] l := by
  obtain ⟨a, ha⟩ := relatorCircleToBelow_surjective w j ⟨x, hx⟩
  obtain ⟨b, hb⟩ := relatorCircleToBelow_surjective w j ⟨y, hy⟩
  have hax : iCirc w a.val = x := congrArg Subtype.val ha
  have hby : iCirc w b.val = y := congrArg Subtype.val hb
  subst x
  subst y
  exact exists_presCone_excursion_replacement w j hpos a b

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Actual relator apices are maximal vertices in the actual presentation poset. -/
theorem presCone_apex_maximal (p : PresPos w) (h : apexOf w j ≤ p) : p = apexOf w j := by
  cases p with
  | inl p => exact h.elim
  | inr k => exact congrArg Sum.inr h.symm

/-- A strict actual incidence cannot have an apex as its lower endpoint. -/
theorem presCone_strictEdge_source_ne_apex (e : StrictOrdEdge (PresPos w)) :
    e.val.1 ≠ apexOf w j := by
  intro h
  have ht := presCone_apex_maximal w j e.val.2 (h ▸ e.property.le)
  grind

/-- Every actual strict germ leaving an apex is a reversed incoming incidence. -/
theorem presCone_strictGerm_from_apex (e : (strictOrderCx (PresPos w)).E × Bool)
    (h : germSrc (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e = apexOf w j) :
    e.2 = false ∧ e.1.val.2 = apexOf w j := by
  rcases e with ⟨e, b⟩
  cases b with
  | false => exact ⟨rfl, h⟩
  | true => exact (presCone_strictEdge_source_ne_apex w j e h).elim

/-- Every actual strict germ entering an apex is a positive incoming incidence. -/
theorem presCone_strictGerm_to_apex (e : (strictOrderCx (PresPos w)).E × Bool)
    (h : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e = apexOf w j) :
    e.2 = true ∧ e.1.val.2 = apexOf w j := by
  rcases e with ⟨e, b⟩
  cases b with
  | false => exact (presCone_strictEdge_source_ne_apex w j e h).elim
  | true => exact ⟨rfl, h⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- An actual strict-edge excursion through a relator apex has a genuine cylinder path replacement. -/
theorem exists_presCone_strictEdge_excursion_replacement (hpos : 0 < (w j).length)
    (e d : StrictOrdEdge (PresPos w)) (he : e.val.2 = apexOf w j) (hd : d.val.2 = apexOf w j) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l e.val.1 d.val.1 ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) e.val.1 d.val.1
        (mapPath (strictOrderIncl (PresPos w)) [(e, true), (d, false)]) l := by
  have hx  := he ▸ e.property
  have hy  := hd ▸ d.property
  obtain ⟨l, hl, hc, hh⟩ := exists_presCone_strict_excursion_replacement w j hpos e.val.1 d.val.1 hx hy
  refine ⟨l, hl, hc, ?_⟩
  have hE : (strictOrderIncl (PresPos w)).onE e =
      ⟨(e.val.1, apexOf w j), hx.le⟩ :=
    Subtype.ext (Prod.ext rfl he)
  have hD : (strictOrderIncl (PresPos w)).onE d =
      ⟨(d.val.1, apexOf w j), hy.le⟩ :=
    Subtype.ext (Prod.ext rfl hd)
  simpa only [mapPath, List.map_cons, List.map_nil, hE, hD, ordPos, ordNeg] using hh

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Every strict lower vertex of an actual relator apex belongs to the actual cylinder. -/
theorem presCone_lower_mem_cylinder (j : J) (x : PresPos w) (hx : x < apexOf w j) :
    x ∈ coneAdjBaseSet (S := circSet w) := by
  obtain ⟨k, t, _, he⟩ := (presPos_lt_apex_iff w j x).mp hx
  exact ⟨cylOuter (aHom w) (TCirc.pt w j k t), he.symm⟩

/-- An included strict germ with cylinder endpoints lies in the actual cylinder. -/
theorem presStrictGerm_in_cylinder (e : (strictOrderCx (PresPos w)).E × Bool)
    (hs : germSrc (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w))
    (ht : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w)) :
    PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (strictOrderIncl (PresPos w)) [e]) := by
  rcases e with ⟨e, b⟩
  cases b <;> exact pathIn_cons (by constructor <;> assumption) (pathIn_nil _)

/-- Every actual strict presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presStrictPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    (p : List ((strictOrderCx (PresPos w)).E × Bool))
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w)) (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt p a b) :
    ∃ q : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt q a b ∧
      PathIn (fun x => x ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b (mapPath (strictOrderIncl (PresPos w)) p) q := by
  induction p using (measure List.length).wf.induction generalizing a b with
  | h p ih =>
    cases p with
    | nil =>
      subst b
      exact ⟨[], rfl, pathIn_nil _, Htpy.refl _⟩
    | cons e p =>
      obtain ⟨hea, hp⟩ := hp
      have hsingle : IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt
          [e] a (germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e) := ⟨hea, rfl⟩
      cases ht : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e with
      | inl t =>
        have hm : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w) :=
          ⟨t, ht.symm⟩
        obtain ⟨q, hq, hqc, hh⟩ := ih p (by change p.length < _; simp) _ b hm hb hp
        have hec := presStrictGerm_in_cylinder w e (hea ▸ ha) hm
        refine ⟨mapPath (strictOrderIncl (PresPos w)) [e] ++ q,
          (isPath_mapPath _ hsingle).append hq, pathIn_append hec hqc, ?_⟩
        simpa only [mapPath, List.map_cons, List.map_nil, List.singleton_append, strictOrderIncl, id_eq] using
          Htpy.append_congr (isPath_mapPath (strictOrderIncl (PresPos w)) hsingle)
            (isPath_mapPath (strictOrderIncl (PresPos w)) hp) (Htpy.refl _) hh
      | inr j =>
        cases p with
        | nil =>
          have hbe  := hp.symm.trans ht
          obtain ⟨t, htb⟩ := hb
          have hn  := htb.trans hbe
          cases hn
        | cons d p =>
          obtain ⟨hds, hp⟩ := hp
          have hed := presCone_strictGerm_to_apex w j e ht
          have hdd := presCone_strictGerm_from_apex w j d (hds.symm.trans ht)
          rcases e with ⟨e, es⟩
          rcases d with ⟨d, ds⟩
          obtain ⟨rfl, he⟩ := hed
          obtain ⟨rfl, hd⟩ := hdd
          have hdc  := presCone_lower_mem_cylinder w j d.val.1 (hd ▸ d.property)
          obtain ⟨q, hq, hqc, hh⟩ := ih p (by change p.length < _; simp) d.val.1 b hdc hb hp
          obtain ⟨r, hr, hrc, hhr⟩ := exists_presCone_strictEdge_excursion_replacement w j (hpos j) e d he hd
          subst a
          refine ⟨r ++ q, hr.append hq, pathIn_append hrc hqc, ?_⟩
          simpa only [mapPath, List.map_cons, List.map_nil, List.cons_append, List.nil_append, strictOrderIncl, strictOrderCx, germSrc, if_true, id_eq] using
            Htpy.append_congr
              (isPath_mapPath (strictOrderIncl (PresPos w))
                (show IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt
                  [(e, true), (d, false)] e.val.1 d.val.1 from ⟨rfl, he.trans hd.symm, rfl⟩))
              (isPath_mapPath (strictOrderIncl (PresPos w)) hp) hhr hh

/-- Every actual weak presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    (p : List ((orderCx (PresPos w)).E × Bool))
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w))
    (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt p a b) :
    ∃ q : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt q a b ∧
      PathIn (fun x => x ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b p q := by
  obtain ⟨q, hq, hc, hh⟩ := exists_presStrictPath_cylinder_reduction w hpos
    (normalizeOrdPath p) a b ha hb (normalizeOrdPath_isPath hp)
  exact ⟨q, hq, hc, (normalizeOrdPath_htpy hp).symm.trans hh⟩

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The actual cylinder inclusion is surjective on the actual presentation fundamental group. -/
theorem presCylinder_pi1_surjective
    (a : {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}) :
    Function.Surjective (pi1Map (subposetHom (coneAdjBaseSet (S := circSet w))) a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq, hqc, hh⟩ := exists_presPath_cylinder_reduction w hpos p.val a.val a.val
      a.property a.property p.property
    let r := liftPathIn q hqc
    have hr  :=
      isPath_liftPathIn q hqc a.property a.property hq
    refine ⟨Pi1.mk ⟨r, hr⟩, Quotient.sound ?_⟩
    change Htpy (orderCx (PresPos w)) a.val a.val
      (mapPath (subposetHom (coneAdjBaseSet)) (liftPathIn q hqc)) p.val
    erw [mapPath_liftPathIn]
    exact hh.symm

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The concrete cylinder inclusion surjects onto the presentation fundamental group. -/
theorem presCylinderInclusion_pi1_surjective (a : CylP (aHom w)) :
    Function.Surjective (pi1Map
      (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a) := by
  let e : coneAdjBaseSet (S := circSet w) ≃o CylP (aHom w) := coneAdjBaseOrderIso
  let b  := e.symm a
  intro z
  obtain ⟨q, hq⟩ := presCylinder_pi1_surjective w hpos b z
  obtain ⟨p, hp⟩ := orderIso_pi1_surjective e.symm a q
  refine ⟨p, ?_⟩
  erw [← hp] at hq
  have hmap : pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a p =
      pi1Map (subposetHom (coneAdjBaseSet)) b
        (pi1Map (orderCxMap e.symm e.symm.monotone) a p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      have heq : mapPath (orderCxMap (ConeAdj.inc) (fun _ _ h => h)) r.val =
          mapPath (subposetHom (coneAdjBaseSet))
            (mapPath (orderCxMap e.symm e.symm.monotone) r.val) := by
        simp only [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose]
        rfl
      change Htpy (orderCx (PresPos w)) (ConeAdj.inc (S := circSet w) a) (ConeAdj.inc (S := circSet w) a)
        (mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) r.val)
        (mapPath (subposetHom (coneAdjBaseSet (S := circSet w)))
          (mapPath (orderCxMap e.symm e.symm.monotone) r.val))
      rw (config := { transparency := .default }) [heq]
      exact Htpy.refl _
  exact hmap.trans hq

include hpos in
/-- Every actual presentation loop class comes from the actual rose. -/
theorem presRoseInclusion_pi1_surjective (x : Rose α) :
    Function.Surjective (pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x) := by
  intro z
  obtain ⟨q, hq⟩ := presCylinderInclusion_pi1_surjective w hpos (cylIn (aHom w) x) z
  obtain ⟨p, hp⟩ := cylinder_pi1_surjective (aHom w) x q
  refine ⟨p, ?_⟩
  erw [← hp] at hq
  have he : pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x p =
      pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h))
        (cylIn (aHom w) x)
        (pi1Map (orderCxMap (cylIn (aHom w)) (cylIn_monotone (aHom w))) x p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      change Htpy (orderCx (PresPos w)) (iRose w x) (iRose w x)
        (mapPath (orderCxMap (iRose w) _) r.val)
        (mapPath (orderCxMap (ConeAdj.inc) _)
          (mapPath (orderCxMap (cylIn (aHom w)) _) r.val))
      simpa only [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose] using
        (Htpy.refl
          (mapPath (orderCxMap (iRose w)
            (iRose_monotone w)) r.val))
  exact he.trans hq

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Inclusion of the genuine rose generator map is the actual marked free-group map. -/
theorem roseLoopHom_inclusion :
    (pi1Map (orderCxMap (iRose w) (iRose_monotone w)) Rose.base).comp
      (loopHom (roseGeneratorLoop (α := α))) = alphaFree w := by
  apply FreeGroup.ext_hom
  intro i
  rw [MonoidHom.comp_apply, loopHom_of]
  exact (show (pi1Map (orderCxMap (iRose w) (iRose_monotone w)) Rose.base)
    (Pi1.mk (roseGeneratorLoop i)) = genClass w i from rfl).trans
      (alphaFree_of w i).symm

/-- The actual free-group marking surjects onto the presentation fundamental group. -/
theorem alphaFree_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaFree w) := by
  intro z
  obtain ⟨q, hq⟩ := presRoseInclusion_pi1_surjective w hpos Rose.base z
  obtain ⟨p, hp⟩ := roseLoopHom_surjective q
  refine ⟨p, ?_⟩
  have h := DFunLike.congr_fun (roseLoopHom_inclusion w) p
  rw [MonoidHom.comp_apply, hp, hq] at h
  exact h.symm

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- The marked presentation comparison is surjective for actual nonempty relator words. -/
theorem alphaHomW_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaHomW ρ w hw) := by
  intro z
  obtain ⟨p, hp⟩ := alphaFree_surjective w hpos z
  exact ⟨QuotientGroup.mk p, hp⟩

/-- Reading and marking are actual inverse maps on the presentation fundamental group. -/
theorem alphaHomW_readingPresW (hpos : ∀ j, 0 < (w j).length)
    (z : Pi1 (orderCx (PresPos w)) (ptBase w)) :
    alphaHomW ρ w hw (readingPresW ρ w hw z) = z := by
  obtain ⟨p, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  rw [readingPresW_alphaHomW]

/-- The actual presentation reading is injective, without a group-comparison premise. -/
theorem readingPresW_injective (hpos : ∀ j, 0 < (w j).length) :
    Function.Injective (readingPresW ρ w hw) :=
  Function.LeftInverse.injective (alphaHomW_readingPresW w ρ hw hpos)

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- Evaluating a word in the presentation group is its actual quotient image. -/
theorem presGroup_wordVal (l : List (α × Bool)) :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) l =
      QuotientGroup.mk (FreeGroup.mk l) := by
  have h : (FreeGroup.lift fun i : α =>
      (QuotientGroup.mk (FreeGroup.of i))) = QuotientGroup.mk' (relSub ρ) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun h (FreeGroup.mk l)

include hw in
/-- The relator words evaluate to one in their actual presentation group. -/
theorem presGroup_wordVal_eq_one (j : J) :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) (w j) = 1 := by
  have hlift : (FreeGroup.lift fun i : α =>
      (QuotientGroup.mk (FreeGroup.of i))) = QuotientGroup.mk' (relSub ρ) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  change FreeGroup.lift _ (FreeGroup.mk (w j)) = 1
  rw [hlift, hw j]
  exact (QuotientGroup.eq_one_iff _).2
    (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨j, rfl⟩))

/-- The genuine presentation cocycle with values in its actual presentation group. -/
def presGroupCocycle : OrdCocycle (PresPos w) (PresGroup ρ) :=
  presCoc w (fun i => QuotientGroup.mk (FreeGroup.of i)) (presGroup_wordVal_eq_one ρ w hw)

@[simp] theorem presGroupCocycle_monodromy :
    (presGroupCocycle ρ w hw).monodromy (ptBase w) = readingPresW ρ w hw := rfl

/-- The actual universal-cover reading separates vertices in every endpoint fibre. -/
theorem presUniversal_reading_injective (hpos : ∀ j, 0 < (w j).length)
    (p q : UV (orderCx (PresPos w)) (ptBase w)) (he : endV p = endV q)
    (hr : (presGroupCocycle ρ w hw).readVertex (ptBase w) p =
      (presGroupCocycle ρ w hw).readVertex (ptBase w) q) : p = q :=
  (presGroupCocycle ρ w hw).readVertex_fibre_injective (ptBase w)
    (readingPresW_injective w ρ hw hpos) p q he hr

/-- Reading gives genuine group coordinates on every actual endpoint fibre of the universal cover. -/
def presUniversalFibreGroupEquiv (hpos : ∀ j, 0 < (w j).length)
    (v : PresPos w) :
    {p : UV (orderCx (PresPos w)) (ptBase w) // endV p = v} ≃ PresGroup ρ :=
  Equiv.ofBijective (fun p => (presGroupCocycle ρ w hw).readVertex (ptBase w) p.val) ⟨by
    intro p q h
    apply Subtype.ext
    exact presUniversal_reading_injective ρ w hw hpos p.val q.val
      (p.property.trans q.property.symm) h, by
    intro z
    obtain ⟨p, hp⟩ := endV_surjective
      (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j))) v
    obtain ⟨q, hq, hz⟩ := (presGroupCocycle ρ w hw).readVertex_fibre_surjective
      (ptBase w) (readingPresW_surjective ρ w hw) p z
    exact ⟨⟨q, hq.trans hp⟩, hz⟩⟩

end FiniteChains.PresModel

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
/-- **The augmentation of the coordinates is the pushforward to the base.**  Summing the
coefficients of a cellular two-chain of the cover over a fibre is the same as augmenting its
coordinate vector. -/
theorem augQ_coords (v : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ) (j : J) :
    augQ (relSub ρ) (coords (relSub ρ) J v j) = Finsupp.mapDomain Prod.snd v j := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add, Finsupp.mapDomain_add]
      simp at *
      rw [hv, hw]
  | single qj n =>
      obtain ⟨q, j₀⟩ := qj
      rw [coords_single, Finsupp.mapDomain_single]
      by_cases h : j = j₀
      · subst h
        simp
      · simp_all

end Comb
end FiniteChains

namespace FiniteChains.Comb
open scoped Classical

 theorem coverCycles_cockcroft_iff {α J : Type} [Fintype α] [DecidableEq α] [Fintype J]
    (ρ : J → FreeGroup α) :
    (∀ c : (univCover ρ).F →₀ ℤ, bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain Prod.snd c = 0) ↔ _root_.FiniteChains.IsCockcroft ρ := by
  constructor
  · intro h v hv j
    let c := (coords (relSub ρ) J).symm v
    have hcoords : coords (relSub ρ) J c = v := LinearEquiv.apply_symm_apply _ v
    have hcycle : bdry2 (univCover ρ) c = 0 := by
      apply (univCover_bdry2_eq_zero_iff ρ c).mpr
      intro i
      rw [hcoords]
      exact hv i
    have hz := h c hcycle
    have ha := augQ_coords ρ c j
    rw [hcoords, hz] at ha
    exact ha
  · intro h c hc
    have hv := (univCover_bdry2_eq_zero_iff ρ c).mp hc
    apply Finsupp.ext
    intro j
    rw [← augQ_coords ρ c j]
    exact h _ hv j
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

instance : Fintype (SpinePresentationGen q) := Fintype.ofFinite _
instance : Fintype (SpinePresentationRel q) := Fintype.ofFinite _
instance : Fintype (SpinePresentationRel q ⊕ (Fin q × Bool)) := Fintype.ofFinite _

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u v
variable {X : Complex2.{u}} {G : Type v} [Group G]

/-- The cellular self-map supplied by a deck transformation. -/
def DeckAction.cellHom (D : DeckAction X G) (g : G) : Hom X X where
  onV := D.smulV g
  onE := D.smulE g
  onF := D.smulF g
  src_onE := D.src_smul g
  tgt_onE := D.tgt_smul g
  base_onF := D.base_smul g
  att_onF := D.att_smul g

def DeckAction.faceChains (D : DeckAction X G) (g : G) :
    (X.F →₀ ℤ) →ₗ[ℤ] (X.F →₀ ℤ) := chain2 (D.cellHom g)

theorem DeckAction.faceChains_boundary (D : DeckAction X G) (g : G) (c : X.F →₀ ℤ) :
    bdry2 X (D.faceChains g c) = chain1 (D.cellHom g) (bdry2 X c) :=
  bdry2_chain2 _ _

theorem DeckAction.faceChains_mul (D : DeckAction X G) (g h : G) (c : X.F →₀ ℤ) :
    D.faceChains (g * h) c = D.faceChains g (D.faceChains h c) := by
  change Finsupp.mapDomain (D.smulF (g * h)) c =
    Finsupp.mapDomain (D.smulF g) (Finsupp.mapDomain (D.smulF h) c)
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun f => Finsupp.mapDomain f c) (funext (D.mul_smulF g h))

/-- Transport a concrete filling along a deck transformation. -/
theorem DeckAction.transport_filling (D : DeckAction X G) (g : G)
    (c : X.F →₀ ℤ) (p : List (X.E × Bool)) (hc : bdry2 X c = pathChain p) :
    bdry2 X (D.faceChains g c) = pathChain (mapPath (D.cellHom g) p) := by
  rw [D.faceChains_boundary, hc]
  exact (pathChain_map _ _).symm

/-- Forgetting the deck coordinate is invariant under the actual universal-cover action. -/
theorem hurewicz_deck_faceChains (a : X.V) (g : Pi1 X a)
    (c : (uCover X a).F →₀ ℤ) :
    hurewicz X a ((univDeck X a).faceChains g c) = hurewicz X a c := by
  change Finsupp.mapDomain (univProj X a).onF
    (Finsupp.mapDomain (deckF g) c) = Finsupp.mapDomain (univProj X a).onF c
  rw [← Finsupp.mapDomain_comp]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {M : Type v} [AddCommGroup M]
  (c : OrdCocycle P (Multiplicative M))

def chain1 : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun e => Multiplicative.toAdd (c.val e.1.1 e.1.2))

theorem chain1_pathChain (p : List ((orderCx P).E × Bool)) :
    c.chain1 (pathChain p) = Multiplicative.toAdd (c.readPath p) := by
  induction p with
  | nil => rfl
  | cons eb p ih =>
      rw [pathChain_cons, map_add, ih, readPath_cons]
      apply congrArg₂ (· + ·) _ rfl
      obtain ⟨e, b⟩ := eb
      cases b <;> simp [chain1, readGerm]

theorem chain1_bdry2 (d : (orderCx P).F →₀ ℤ) : c.chain1 (bdry2 (orderCx P) d) = 0 := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp_all
  | single t n => rw [bdry2_single, LinearMap.map_smul, chain1_pathChain, readPath_att]; simp

/-- Pull an actual order cocycle back along a monotone map. -/
def pullback {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f) :
    OrdCocycle Q (Multiplicative M) where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

theorem pullback_readPath {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f)
    (p : List ((orderCx Q).E × Bool)) :
    (c.pullback f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p with
  | nil => rfl
  | cons eb p ih =>
      simp only [mapPath, List.map_cons]
      rw [readPath_cons, readPath_cons, ih]
      congr 1

end FiniteChains.Comb.OrdCocycle
end

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G)

@[simp] theorem readPath_revPath (p : List ((orderCx P).E × Bool)) :
    c.readPath (revPath p) = (c.readPath p)⁻¹ := by
  induction p with
  | nil => simp
  | cons e p ih => simp_all

/-- On a combinatorially simply connected order complex, a cocycle reads one
on every closed edge path. -/
theorem readPath_eq_one_of_simplyConnected (h : SimplyConnected (orderCx P))
    {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) : c.readPath p = 1 :=
  c.readPath_htpy (h a p hp)

/-- Cocycle reading is independent of the edge path with prescribed endpoints. -/
theorem readPath_eq_of_simplyConnected (h : SimplyConnected (orderCx P))
    {a b : P} {p q : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hq : IsPath (orderCx P).src (orderCx P).tgt q a b) :
    c.readPath p = c.readPath q := by
  have hr := c.readPath_eq_one_of_simplyConnected h
    (isPath_append_iff.mpr ⟨b, hp, isPath_revPath hq⟩)
  rw [readPath_append, readPath_revPath] at hr
  exact mul_inv_eq_one.mp hr

/-- Every group-valued order cocycle on a connected simply connected order
complex has a normalized potential, with no commutativity assumption on the group. -/
theorem exists_potential_of_simplyConnected (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P)) (a : P) :
    ∃ k : P → G, k a = 1 ∧ ∀ {p q : P}, p ≤ q → k p * c.val p q = k q := by
  choose paths hpaths using hconn a
  let k  := fun p => c.readPath (paths p)
  refine ⟨k, c.readPath_eq_one_of_simplyConnected hsc (hpaths a), ?_⟩
  intro p q hpq
  have h := c.readPath_eq_of_simplyConnected hsc
    (isPath_append_iff.mpr ⟨p, hpaths p, isPath_single (ordPos hpq)⟩) (hpaths q)
  simpa using h

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G)

def IsFlatSection (s : P → Ω) : Prop :=
  ∀ {a b}, a ≤ b → c.val a b • s b = s a

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v w
variable {P : Type u} [PartialOrder P] [DecidableEq P]
  {G : Type v} [Group G] (c : OrdCocycle (NeSpx (cmpRel P)) G)

theorem edgeHop_comp_htpy {a b d : P} (hab : a ≤ b) (hbd : b ≤ d) :
    Htpy (orderCx (NeSpx (cmpRel P))) (spx1 a) (spx1 d)
      (edgeHop hab ++ edgeHop hbd) (edgeHop (hab.trans hbd)) := by
  apply htpy_of_loop_nil ((isPath_edgeHop hab).append (isPath_edgeHop hbd))
    (isPath_edgeHop (hab.trans hbd))
  apply htpy_nil_of_star d (starCh_spx1 (hab.trans hbd))
  · exact ((isPath_edgeHop hab).append (isPath_edgeHop hbd)).append
      (isPath_revPath (isPath_edgeHop (hab.trans hbd)))
  · exact pathIn_append
      (pathIn_append (pathIn_edgeHop hab (hab.trans hbd) hbd)
        (pathIn_edgeHop hbd hbd le_rfl))
      (pathIn_revPath (pathIn_edgeHop (hab.trans hbd) (hab.trans hbd) le_rfl))

def barycentricCocycle : OrdCocycle P G where
  val a b := if h : a ≤ b then c.readPath (edgeHop h) else 1
  comp hab hbd := by
    simp only [dif_pos hab, dif_pos hbd, dif_pos (hab.trans hbd)]
    exact (c.readPath_append _ _).symm.trans (c.readPath_htpy (edgeHop_comp_htpy hab hbd))

theorem barycentricCocycle_val {a b : P} (h : a ≤ b) :
    (barycentricCocycle c).val a b = c.readPath (edgeHop h) := by
  simp only [barycentricCocycle, dif_pos h]

theorem edgeHop_read_via {a b : P} (hab : a ≤ b) (σ : NeSpx (cmpRel P))
    (ha : a ∈ σ.1) (hb : b ∈ σ.1) :
    c.readPath (edgeHop hab) = c.val (spx1 a) σ * (c.val (spx1 b) σ)⁻¹ := by
  have hσ : spx2 hab ≤ σ := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    exacts [ha, hb]
  rw [← c.comp (spx1_le_spx2_left hab) hσ,
    ← c.comp (spx1_le_spx2_right hab) hσ]
  simp only [edgeHop, hop, OrdCocycle.readPath_cons, OrdCocycle.readPath_nil,
    OrdCocycle.readGerm_ordPos, OrdCocycle.readGerm_ordNeg, mul_one]
  group

variable {Ω : Type w} [MulAction G Ω]

def barycentricSection (s : P → Ω) (σ : NeSpx (cmpRel P)) : Ω :=
  (c.val (spx1 (chainMax σ)) σ)⁻¹ • s (chainMax σ)

/-- A flat section on the original face poset gives a flat section on the
actual subdivision, not merely an agreement on selected generators. -/
theorem barycentricSection_flat (s : P → Ω)
    (hs : (barycentricCocycle c).IsFlatSection s) :
    c.IsFlatSection (barycentricSection c s) := by
  intro σ τ hστ
  have hm : spx1 (chainMax σ) ≤ σ := by
    intro x hx
    simp at hx
    subst x
    exact chainMax_mem σ
  have hread := hs (chainMax_monotone hστ)
  rw [barycentricCocycle_val c (chainMax_monotone hστ),
    edgeHop_read_via c (chainMax_monotone hστ) τ
      (hστ (chainMax_mem σ)) (chainMax_mem τ)] at hread
  unfold barycentricSection
  rw [← c.comp hm hστ, mul_smul] at hread
  have he := congrArg (fun z => (c.val (spx1 (chainMax σ)) σ)⁻¹ • z) hread
  simpa only [mul_smul, inv_smul_smul] using he

theorem barycentricSection_spx1 (s : P → Ω) (a : P) :
    barycentricSection c s (spx1 a) = s a := by
  simp [barycentricSection]

end FiniteChains.Davis

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G) (s : P → Ω)

theorem flat_edge_trans {a b d : P} (hab : a ≤ b) (hbd : b ≤ d)
    (h₁ : c.val a b • s b = s a) (h₂ : c.val b d • s d = s b) :
    c.val a d • s d = s a := by
  rw [← c.comp hab hbd, mul_smul, h₂, h₁]

theorem flat_edge_of_top {a b d : P} (hab : a ≤ b) (hbd : b ≤ d)
    (h₁ : c.val a d • s d = s a) (h₂ : c.val b d • s d = s b) :
    c.val a b • s b = s a := by
  rw [← h₂, ← mul_smul, c.comp hab hbd, h₁]

theorem flat_edge_of_bottom {a b d : P} (hab : a ≤ b) (hbd : b ≤ d)
    (h₁ : c.val a b • s b = s a) (h₂ : c.val a d • s d = s a) :
    c.val b d • s d = s b := by
  calc
    c.val b d • s d = (c.val a b)⁻¹ • (c.val a d • s d) := by
      rw [← c.comp hab hbd, mul_smul, inv_smul_smul]
    _ = (c.val a b)⁻¹ • s a := by rw [h₂]
    _ = s b := by rw [← h₁, inv_smul_smul]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)

def collarValue (p : Fin M) : Ω :=
  c.val (cW hc p) (cD hc p) • ((c.val (cV hc p) (cD hc p))⁻¹ • rv (vc p))

/-- Values on all actual surface cells. The centre is chosen after proving
that the collar data propagate consistently through the fan. -/
def surfaceSection (centre : Ω) : SCell vc ec hc → Ω
  | .vtx v => rv v
  | .bed e => re e
  | .cvx p => collarValue hc c rv p
  | .ced p => (c.val (cW hc p) (cF hc p))⁻¹ • collarValue hc c rv p
  | .dia p => (c.val (cV hc p) (cD hc p))⁻¹ • rv (vc p)
  | .gdi p => (c.val (cV hc p) (cG hc p))⁻¹ • rv (vc p)
  | .tr1 p => (c.val (cE hc p) (cT1 hc p))⁻¹ • re (ec p)
  | .tr2 p => (c.val (cV hc p) (cT2 hc p))⁻¹ • rv (vc p)
  | .ctr => centre
  | .rad p => (c.val (cC hc) (cR hc p))⁻¹ • centre
  | .inn p => (c.val (cC hc) (cI hc p))⁻¹ • centre

variable (k : Ω)
local notation "s" => surfaceSection hc c rv re k

theorem v_d (p : Fin M) : c.val (cV hc p) (cD hc p) • s (cD hc p) = s (cV hc p) := smul_inv_smul _ _

theorem w_d (p : Fin M) : c.val (cW hc p) (cD hc p) • s (cD hc p) = s (cW hc p) := rfl

theorem v_g (p : Fin M) : c.val (cV hc p) (cG hc p) • s (cG hc p) = s (cV hc p) := smul_inv_smul _ _

theorem w_f (p : Fin M) : c.val (cW hc p) (cF hc p) • s (cF hc p) = s (cW hc p) := smul_inv_smul _ _

theorem e_t1 (p : Fin M) : c.val (cE hc p) (cT1 hc p) • s (cT1 hc p) = s (cE hc p) := smul_inv_smul _ _

theorem v_t2 (p : Fin M) : c.val (cV hc p) (cT2 hc p) • s (cT2 hc p) = s (cV hc p) := smul_inv_smul _ _

variable (hb : ∀ p : Fin M,
  c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
  c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

include hb in
theorem v_t1 (p : Fin M) : c.val (cV hc p) (cT1 hc p) • s (cT1 hc p) = s (cV hc p) :=
  c.flat_edge_trans s (cV_le_cE hc p) (cE_le_cT1 hc p)
    (hb p).1 (e_t1 hc c rv re k p)

include hb in
theorem v1_t1 (p : Fin M) :
    c.val (cV hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cV hc (p + 1)) :=
  c.flat_edge_trans s (cV1_le_cE hc p) (cE_le_cT1 hc p)
    (hb p).2 (e_t1 hc c rv re k p)

include hb in
theorem d1_t1 (p : Fin M) :
    c.val (cD hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cD hc (p + 1)) :=
  c.flat_edge_of_bottom s (cV_le_cD hc (p + 1)) (cD1_le_cT1 hc p)
    (v_d hc c rv re k (p + 1)) (v1_t1 hc c rv re k hb p)

include hb in
theorem w1_t1 (p : Fin M) :
    c.val (cW hc (p + 1)) (cT1 hc p) • s (cT1 hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW_le_cD hc (p + 1)) (cD1_le_cT1 hc p)
    (w_d hc c rv re k (p + 1)) (d1_t1 hc c rv re k hb p)

include hb in
theorem g_t1 (p : Fin M) : c.val (cG hc p) (cT1 hc p) • s (cT1 hc p) = s (cG hc p) :=
  c.flat_edge_of_bottom s (cV_le_cG hc p) (cG_le_cT1 hc p)
    (v_g hc c rv re k p) (v_t1 hc c rv re k hb p)

include hb in
theorem w1_g (p : Fin M) :
    c.val (cW hc (p + 1)) (cG hc p) • s (cG hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_of_top s (cW1_le_cG hc p) (cG_le_cT1 hc p)
    (w1_t1 hc c rv re k hb p) (g_t1 hc c rv re k hb p)

theorem d_t2 (p : Fin M) : c.val (cD hc p) (cT2 hc p) • s (cT2 hc p) = s (cD hc p) :=
  c.flat_edge_of_bottom s (cV_le_cD hc p) (cD_le_cT2 hc p)
    (v_d hc c rv re k p) (v_t2 hc c rv re k p)

theorem w_t2 (p : Fin M) : c.val (cW hc p) (cT2 hc p) • s (cT2 hc p) = s (cW hc p) :=
  c.flat_edge_trans s (cW_le_cD hc p) (cD_le_cT2 hc p)
    (w_d hc c rv re k p) (d_t2 hc c rv re k p)

theorem g_t2 (p : Fin M) : c.val (cG hc p) (cT2 hc p) • s (cT2 hc p) = s (cG hc p) :=
  c.flat_edge_of_bottom s (cV_le_cG hc p) (cG_le_cT2 hc p)
    (v_g hc c rv re k p) (v_t2 hc c rv re k p)

include hb in
theorem w1_t2 (p : Fin M) :
    c.val (cW hc (p + 1)) (cT2 hc p) • s (cT2 hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW1_le_cG hc p) (cG_le_cT2 hc p)
    (w1_g hc c rv re k hb p) (g_t2 hc c rv re k p)

theorem f_t2 (p : Fin M) : c.val (cF hc p) (cT2 hc p) • s (cT2 hc p) = s (cF hc p) :=
  c.flat_edge_of_bottom s (cW_le_cF hc p) (cF_le_cT2 hc p)
    (w_f hc c rv re k p) (w_t2 hc c rv re k p)

include hb in
theorem w1_f (p : Fin M) :
    c.val (cW hc (p + 1)) (cF hc p) • s (cF hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_of_top s (cW1_le_cF hc p) (cF_le_cT2 hc p)
    (w1_t2 hc c rv re k hb p) (f_t2 hc c rv re k p)

end FiniteChains.Davis.SurfaceSection

namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)

def radialValue (p : Fin M) : Ω :=
  c.val (cC hc) (cR hc p) •
    ((c.val (cW hc p) (cR hc p))⁻¹ • collarValue hc c rv p)

theorem bridge_to_top {a b r t : SCell vc ec hc}
    (har : a ≤ r) (hbr : b ≤ r) (hrt : r ≤ t) :
    c.val a r * (c.val b r)⁻¹ = c.val a t * (c.val b t)⁻¹ := by
  rw [← c.comp har hrt, ← c.comp hbr hrt]
  group

variable (hb : ∀ p : Fin M,
  c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
  c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))

include hb in
theorem radialValue_step (p : Fin M) : radialValue hc c rv p = radialValue hc c rv (p + 1) := by
  let f := surfaceSection hc c rv re (rv (vc p)) (cF hc p)
  have h₀ : c.val (cW hc p) (cF hc p) • f = collarValue hc c rv p :=
    w_f hc c rv re (rv (vc p)) p
  have h₁ : c.val (cW hc (p + 1)) (cF hc p) • f = collarValue hc c rv (p + 1) :=
    w1_f hc c rv re (rv (vc p)) hb p
  have left : radialValue hc c rv p =
      (c.val (cC hc) (cI hc p) * (c.val (cF hc p) (cI hc p))⁻¹) • f := by
    rw [radialValue, ← mul_smul,
      bridge_to_top hc c (cC_le_cR hc p) (cW_le_cR hc p) (cR_le_cI hc p),
      ← h₀, ← c.comp (cW_le_cF hc p) (cF_le_cI hc p), mul_inv_rev]
    simp only [mul_smul, inv_smul_smul]
  have right : radialValue hc c rv (p + 1) =
      (c.val (cC hc) (cI hc p) * (c.val (cF hc p) (cI hc p))⁻¹) • f := by
    rw [radialValue, ← mul_smul,
      bridge_to_top hc c (cC_le_cR hc (p + 1)) (cW_le_cR hc (p + 1)) (cR1_le_cI hc p),
      ← h₁, ← c.comp (cW1_le_cF hc p) (cF_le_cI hc p), mul_inv_rev]
    simp only [mul_smul, inv_smul_smul]
  exact left.trans right.symm

def centreValue : Ω := radialValue hc c rv (cyc M 0)


local notation "s" => surfaceSection hc c rv re (centreValue hc c rv)

theorem c_r (p : Fin M) : c.val (cC hc) (cR hc p) • s (cR hc p) = s (cC hc) := smul_inv_smul _ _

include hb in
theorem w_r (p : Fin M) : c.val (cW hc p) (cR hc p) • s (cR hc p) = s (cW hc p) := by
  change c.val _ _ • ((c.val _ _)⁻¹ • centreValue hc c rv) = collarValue hc c rv p
  rw [← (show radialValue hc c rv p = centreValue hc c rv by
    have hn : ∀ n : ℕ, radialValue hc c rv (cyc M n) = radialValue hc c rv (cyc M 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [cyc_succ, ← radialValue_step hc c rv re hb, ih]
    have hp : cyc M p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
    rw [centreValue, ← hp]
    exact hn p.val), radialValue, inv_smul_smul, smul_inv_smul]

theorem c_i (p : Fin M) : c.val (cC hc) (cI hc p) • s (cI hc p) = s (cC hc) := smul_inv_smul _ _

theorem r_i (p : Fin M) : c.val (cR hc p) (cI hc p) • s (cI hc p) = s (cR hc p) :=
  c.flat_edge_of_bottom s (cC_le_cR hc p) (cR_le_cI hc p)
    (c_r hc c rv re p) (c_i hc c rv re p)

theorem r1_i (p : Fin M) :
    c.val (cR hc (p + 1)) (cI hc p) • s (cI hc p) = s (cR hc (p + 1)) :=
  c.flat_edge_of_bottom s (cC_le_cR hc (p + 1)) (cR1_le_cI hc p)
    (c_r hc c rv re (p + 1)) (c_i hc c rv re p)

include hb in
theorem w_i (p : Fin M) : c.val (cW hc p) (cI hc p) • s (cI hc p) = s (cW hc p) :=
  c.flat_edge_trans s (cW_le_cR hc p) (cR_le_cI hc p)
    (w_r hc c rv re hb p) (r_i hc c rv re p)

include hb in
theorem w1_i (p : Fin M) :
    c.val (cW hc (p + 1)) (cI hc p) • s (cI hc p) = s (cW hc (p + 1)) :=
  c.flat_edge_trans s (cW_le_cR hc (p + 1)) (cR1_le_cI hc p)
    (w_r hc c rv re hb (p + 1)) (r1_i hc c rv re p)

include hb in
theorem f_i (p : Fin M) : c.val (cF hc p) (cI hc p) • s (cI hc p) = s (cF hc p) :=
  c.flat_edge_of_bottom s (cW_le_cF hc p) (cF_le_cI hc p)
    (w_f hc c rv re (centreValue hc c rv) p) (w_i hc c rv re hb p)

end FiniteChains.Davis.SurfaceSection

namespace FiniteChains.Davis.SurfaceSection
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (SCell vc ec hc) G) (rv : κ → Ω) (re : ι → Ω)
  (hb : ∀ p : Fin M,
    c.val (cV hc p) (cE hc p) • re (ec p) = rv (vc p) ∧
    c.val (cV hc (p + 1)) (cE hc p) • re (ec p) = rv (vc (p + 1)))


include hb in
/-- No new monodromy is introduced by the collar and the interior fan. All
flat boundary data extend for an arbitrary group action. -/
theorem exists_flat_section : ∃ s : SCell vc ec hc → Ω,
    c.IsFlatSection s ∧
    (∀ v, s (toS vc ec hc (.vtx v)) = rv v) ∧
    (∀ e, s (toS vc ec hc (.bed e)) = re e) :=
  ⟨surfaceSection hc c rv re (centreValue hc c rv), (by
    intro a b hab
    rcases hab with heq | h
    · simp_all
    cases a <;> cases b <;> simp only [plt] at h
    case vtx.bed v e =>
      obtain ⟨p, hp, hv⟩ := h
      subst e
      rcases hv with hv | hv
      · subst v; exact (hb p).1
      · subst v; exact (hb p).2
    case vtx.dia v p =>
      subst v
      exact v_d hc c rv re (centreValue hc c rv) p
    case vtx.gdi v p =>
      subst v
      exact v_g hc c rv re (centreValue hc c rv) p
    case cvx.ced x p =>
      rcases h with h | h
      · subst x; exact w_f hc c rv re (centreValue hc c rv) p
      · subst x; exact w1_f hc c rv re (centreValue hc c rv) hb p
    case cvx.dia x p =>
      subst x
      exact w_d hc c rv re (centreValue hc c rv) p
    case cvx.gdi x p =>
      subst x
      exact w1_g hc c rv re (centreValue hc c rv) hb p
    case cvx.rad x p =>
      subst x
      exact w_r hc c rv re hb p
    case ctr.rad p => exact c_r hc c rv re p
    case bed.tr1 e p =>
      subst e
      exact e_t1 hc c rv re (centreValue hc c rv) p
    case ced.tr2 x p =>
      subst x
      exact f_t2 hc c rv re (centreValue hc c rv) p
    case ced.inn x p =>
      subst x
      exact f_i hc c rv re hb p
    case dia.tr1 x p =>
      subst x
      exact d1_t1 hc c rv re (centreValue hc c rv) hb p
    case dia.tr2 x p =>
      subst x
      exact d_t2 hc c rv re (centreValue hc c rv) p
    case gdi.tr1 x p =>
      subst x
      exact g_t1 hc c rv re (centreValue hc c rv) hb p
    case gdi.tr2 x p =>
      subst x
      exact g_t2 hc c rv re (centreValue hc c rv) p
    case rad.inn x p =>
      rcases h with h | h
      · subst x; exact r_i hc c rv re p
      · subst x; exact r1_i hc c rv re p
    case vtx.tr1 v p =>
      rcases h with h | h
      · subst v; exact v_t1 hc c rv re (centreValue hc c rv) hb p
      · subst v; exact v1_t1 hc c rv re (centreValue hc c rv) hb p
    case vtx.tr2 v p =>
      subst v
      exact v_t2 hc c rv re (centreValue hc c rv) p
    case cvx.tr1 x p =>
      subst x
      exact w1_t1 hc c rv re (centreValue hc c rv) hb p
    case cvx.tr2 x p =>
      rcases h with h | h
      · subst x; exact w_t2 hc c rv re (centreValue hc c rv) p
      · subst x; exact w1_t2 hc c rv re (centreValue hc c rv) hb p
    case cvx.inn x p =>
      rcases h with h | h
      · subst x; exact w_i hc c rv re hb p
      · subst x; exact w1_i hc c rv re hb p
    case ctr.inn p => exact c_i hc c rv re p),
    fun _ => rfl, fun _ => rfl⟩

end FiniteChains.Davis.SurfaceSection

namespace FiniteChains.Davis
open RACG Mirror Comb Cell
universe u v w
variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  {G : Type v} [Group G] {Ω : Type w} [MulAction G Ω]
  (c : OrdCocycle (NeSpx (cmpRel (SCell vc ec hc))) G)
  (rv : κ → Ω) (re : ι → Ω)

end FiniteChains.Davis

namespace FiniteChains

variable {α β : Type*}

theorem groupRingMap_grp (φ : FreeGroup α →* FreeGroup β) (w : FreeGroup α) :
    MonoidAlgebra.mapDomainRingHom ℤ φ (grp w) = grp (φ w) := MonoidAlgebra.mapDomain_single

/-- A coordinate of a Fox derivative is preserved when the substituted
generators have the corresponding Kronecker derivatives. -/
theorem fox_subst_coordinate [DecidableEq α] [DecidableEq β]
    (φ : FreeGroup α →* FreeGroup β) (a : α) (b : β)
    (h : ∀ i, fox b (φ (FreeGroup.of i)) = if a = i then 1 else 0)
    (w : FreeGroup α) :
    fox b (φ w) = MonoidAlgebra.mapDomainRingHom ℤ φ (fox a w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => simp_all
  | inv_of i ih =>
      rw [map_inv, fox_inv, fox_inv, map_neg, map_mul, ih, groupRingMap_grp, map_inv]
  | mul u v hu hv =>
      rw [map_mul, fox_mul, fox_mul, map_add, hu, hv, map_mul, groupRingMap_grp]

namespace BlockFamily
universe u
variable {A S : Type u} {I Z : S → Type u}
  [DecidableEq A] [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- Substituting arbitrary old words for the markings retains every internal
Fox coordinate, before taking a quotient or an augmentation. -/
theorem fox_blockSubst_internal (u : ∀ s, I s → FreeGroup A) (s : S)
    (z : Z s) (w : FreeGroup (I s ⊕ Z s)) :
    fox (Sum.inr z) (blockSubst u s w) =
      MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) (fox (Sum.inr z) w) := by
  apply fox_subst_coordinate
  rintro (i | z')
  · rw [blockSubst_of_inl,
      fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl)]
    simp
  · simp

end BlockFamily
end FiniteChains

namespace FiniteChains.BlockFamily
universe u
variable {A Jr S : Type u} {I Z M : S → Type u}
  (ρ : Jr ⊕ S → FreeGroup A) (u : ∀ s, I s → FreeGroup A)
  (β : ∀ s, M s → FreeGroup (I s ⊕ Z s))

/-- The actual homomorphism from a marked block presentation to the substituted
group, obtained by substituting its markings and including its own generators. -/
def markedBlockHom (s : S) : PresGroup (β s) →*
    PresGroup (substPresF ρ (fun s m => blockSubst u s (β s m))) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ (fun s m => blockSubst u s (β s m))))).comp
      ((FreeGroup.map (genEmb s)).comp (blockSubst u s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))

@[simp] theorem markedBlockHom_mk (s : S) (w : FreeGroup (I s ⊕ Z s)) :
    markedBlockHom ρ u β s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (genEmb s) (blockSubst u s w)) := rfl

theorem markedBlockHom_coeff (s : S) (x : FreeGroupRing (I s ⊕ Z s)) :
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (quotRingHom ℤ (relSub (β s)) x) =
    quotRingHom ℤ (relSub (substPresF ρ (fun s m => blockSubst u s (β s m))))
      (freeRingMap (genEmb s) (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x)) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (β s))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ
      (QuotientGroup.mk' (relSub (substPresF ρ (fun s m => blockSubst u s (β s m)))))
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map (genEmb s))
        (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

variable [DecidableEq A] [DecidableEq S]
  [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- The internal column of the substituted presentation is precisely the block
column with its coefficients sent through the constructed block homomorphism. -/
theorem foxMatrix_markedBlock_internal (s : S) (z : Z s) (m : M s) :
    foxMatrixPres (substPresF ρ (fun s m => blockSubst u s (β s m)))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (foxMatrixPres (β s) (Sum.inr z) m) := by
  rw [foxMatrixPres, foxMatrixPres, markedBlockHom_coeff, substPresF_inr]
  change quotRingHom ℤ _
      (fox (genEmb s (Sum.inr z)) (FreeGroup.map (genEmb s) (blockSubst u s (β s m)))) = _
  rw [fox_map (genEmb s) (genEmb_injective s), fox_blockSubst_internal]

end FiniteChains.BlockFamily

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical

variable (q₀ : ℕ) [NeZero q₀]

/-- Reordering distinguished and internal generators in the actual presentation. -/
def spineReorderHom : PresGroup (namedSpinePresentation q₀) →*
    PresGroup (markedSpineBeta q₀) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (markedSpineBeta q₀))).comp (FreeGroup.map Sum.swap)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩))

theorem spineReorderHom_coeff (x : FreeGroupRing (NamedSpineGen q₀)) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q₀)
      (quotRingHom ℤ (relSub (namedSpinePresentation q₀)) x) =
    quotRingHom ℤ (relSub (markedSpineBeta q₀)) (freeRingMap Sum.swap x) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q₀)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (namedSpinePresentation q₀))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (markedSpineBeta q₀)))
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.swap) x)
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem spineReorderHom_fox_internal (z : SpinePresentationGen q₀) (m : NamedSpineRel q₀) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q₀)
      (foxMatrixPres (namedSpinePresentation q₀) (Sum.inl z) m) =
    foxMatrixPres (markedSpineBeta q₀) (Sum.inr z) m := by
  rw [foxMatrixPres, spineReorderHom_coeff, foxMatrixPres]
  change _ = quotRingHom ℤ _
    (fox (Sum.swap (Sum.inl z)) (FreeGroup.map Sum.swap (namedSpinePresentation q₀ m)))
  rw [fox_map Sum.swap (Equiv.sumComm _ _).injective]

variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

/-- The constructed receiver from the genuine named spine into the actual
simultaneously substituted group. No injectivity of this receiver is asserted. -/
def familySpineHom (s : S) : PresGroup (namedSpinePresentation (q s)) →*
    PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  (markedBlockHom ρ u (fun s => markedSpineBeta (q s)) s).comp (spineReorderHom (q s))


/-- The actual internal Fox boundary equals the boundary of the named spine
over precisely the group ring of the simultaneous substitution. -/
theorem familySpine_internalBoundary (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (z : SpinePresentationGen (q s)) :
    (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
    NamedPresentation.receivedFoxBoundary (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) β (Sum.inl z) := by
  unfold NamedPresentation.receivedFoxBoundary
  exact Finset.sum_congr (by ext; simp) (fun m _ => congrArg (β m * ·)
    (by
      have h := foxMatrix_markedBlock_internal
        ρ u (fun s => markedSpineBeta (q s)) s z m
      rw [← spineReorderHom_fox_internal, BlockMor.mapDomainRingHom_comp'] at h
      convert h using 1 <;>
        simp only [familyFiniteSpineWordBlock, finiteSpineWordBlock, blockSubst, familySpineHom] <;> rfl))

/-- The hypothesis on one block in B2 is exactly a prescribed marked boundary
in its original spine presentation, with the full group-ring coefficients. -/
theorem familySpine_internal_zero_iff (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) :
    (∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) ↔
    ∀ z : SpinePresentationGen (q s),
      (∑ j, β (Sum.inl j) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentation (q s) j))) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  simp only [familySpine_internalBoundary]
  exact NamedPresentation.receivedFoxBoundary_internal_zero_iff _ _ _ β

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical
variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

def receivedSpineWordReceiver (s : S) : PresGroup (spinePresentation (q s)) →*
    PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  (familySpineHom ρ q u s).comp
    (NamedPresentation.inclusion (spinePresentation (q s)) (spinePresentationMarkedWord (q s)))

abbrev receivedSpineCover (s : S) : Complex2 :=
  ReceivedTree.cover (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)

/-- Its word coefficients are exactly the coefficient map in the relative Fox
boundary already proved for the substituted family. -/
theorem receivedSpineWordReceiver_coeff (s : S) (x : FreeGroupRing (SpinePresentationGen (q s))) :
    MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (quotRingHom ℤ (relSub (spinePresentation (q s))) x) =
    NamedPresentation.receivedWordCoefficientMap (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) x := by
  unfold NamedPresentation.receivedWordCoefficientMap NamedPresentation.wordCoefficientMap
  change MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (spinePresentation (q s)))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (namedSpinePresentation (q s))))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem familySpineHom_marked (s : S) (i : Fin (q s) × Bool) :
    familySpineHom ρ q u s (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s i)) := by
  change QuotientGroup.mk (FreeGroup.map (genEmb s)
      (blockSubst u s (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr i))))) = _
  erw [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  have h : (FreeGroup.map (genEmb (α := A) s)).comp
      (FreeGroup.map (Sum.inl)) =
      FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg QuotientGroup.mk (DFunLike.congr_fun h (u s i))

/-- The old-face part of a named coefficient vector as an actual finite chain
in the constructed cover, with every group coefficient retained. -/
def receivedSpineFaceChain (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) :
    (receivedSpineCover ρ q u s).F →₀ ℤ :=
  (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).symm (fun j => β (Sum.inl j))

theorem receivedSpineFaceChain_coefficient (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) (j : SpinePresentationRel (q s)) :
    ReceivedTree.cellCoefficient j (receivedSpineFaceChain ρ q u s β) = β (Sum.inl j) :=
  ReceivedTree.cellCoefficient_coordinates_symm _ _ _

/-- The actual two-boundary of the old face chain has the prescribed marked-word
coordinates whenever the genuine B2 internal-coordinate condition holds. -/
theorem receivedSpineFaceChain_relative_boundary (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0)
    (z : SpinePresentationGen (q s)) :
    ReceivedTree.cellCoefficient z.1
      (Comb.bdry2 (receivedSpineCover ρ q u s) (receivedSpineFaceChain ρ q u s β)) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  erw [ReceivedTree.cellCoefficient_bdry2]
  simp only [receivedSpineFaceChain_coefficient, ReceivedTree.coefficientMap,
    RingHom.comp_apply]
  change (∑ j, β (Sum.inl j) * MonoidAlgebra.mapDomainRingHom ℤ
    (receivedSpineWordReceiver ρ q u s)
    (quotRingHom ℤ (relSub (spinePresentation (q s)))
      (fox z (spinePresentation (q s) j)))) = _
  simp only [receivedSpineWordReceiver_coeff]
  exact (familySpine_internal_zero_iff ρ q u s β).mp hβ z

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

def markedBoundaryPos (x : Fin q × Bool) (b : Bool) : Fin (8 * q) :=
  ⟨8 * x.1.val + (if x.2 then 2 else 0) + (if b then 1 else 0), by
    have := x.1.isLt
    cases x.2 <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

omit [NeZero q] in
theorem markedBoundaryPos_div (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val / 2 / 4 = x.1.val := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_mod (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val / 2 % 4 = if x.2 then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_par (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val % 2 = if b then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem gvc_markedBoundaryPos_false (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x false) = none := by
  rw [gvc, markedBoundaryPos_par]
  rfl

omit [NeZero q] in
theorem gvc_markedBoundaryPos_true (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x true) = some x := by
  rw [gvc, markedBoundaryPos_par]
  simp only [↓reduceIte, Nat.one_ne_zero]
  apply congrArg some
  apply Prod.ext
  · ext
    exact markedBoundaryPos_div q x true
  · rw [markedBoundaryPos_mod]
    cases x.2 <;> rfl

omit [NeZero q] in
theorem gec_markedBoundaryPos (x : Fin q × Bool) (b : Bool) :
    gec q (markedBoundaryPos q x b) = (x.1, x.2, b) := by
  apply Prod.ext
  · ext
    exact markedBoundaryPos_div q x b
  · change (decide ((markedBoundaryPos q x b).val / 2 % 4 % 2 = 1),
      xor (decide ((markedBoundaryPos q x b).val % 2 = 1))
        (decide (2 ≤ (markedBoundaryPos q x b).val / 2 % 4))) = (x.2, b)
    rw [markedBoundaryPos_mod, markedBoundaryPos_par]
    cases x.2 <;> cases b <;> rfl

theorem markedBoundaryPos_succ (x : Fin q × Bool) :
    markedBoundaryPos q x false + 1 = markedBoundaryPos q x true := by
  ext
  rw [fin_succ_val]
  have ht := (markedBoundaryPos q x true).isLt
  change (8 * x.1.val + (if x.2 then 2 else 0) + 0 + 1) % (8 * q) =
    8 * x.1.val + (if x.2 then 2 else 0) + 1
  change 8 * x.1.val + (if x.2 then 2 else 0) + 1 < 8 * q at ht
  simpa using Nat.mod_eq_of_lt ht

theorem gvc_markedBoundaryPos_end (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x true + 1) = none := by
  rw [gvc, if_pos]
  rw [fin_succ_val]
  have ht : (markedBoundaryPos q x true).val + 1 < 8 * q := by
    obtain ⟨h, t⟩ := x
    have := h.isLt
    cases t <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [Nat.mod_eq_of_lt ht]
  have hpar : (markedBoundaryPos q x true).val % 2 = 1 := markedBoundaryPos_par q x true
  omega

omit [NeZero q] in
theorem gvc_endpoint (p : Fin (8 * q)) :
    gvc q p = none ∨ gvc q p = some ((gec q p).1, (gec q p).2.1) := by
  unfold gvc
  split_ifs with hp
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gvc_succ_endpoint (p : Fin (8 * q)) :
    gvc q (p + 1) = none ∨ gvc q (p + 1) = some ((gec q p).1, (gec q p).2.1) := by
  have ht := p.isLt
  have hv := fin_succ_val p
  by_cases he : (p + 1).val % 2 = 0
  · exact Or.inl (by rw [gvc, if_pos he])
  · have hs : (p + 1).val = p.val + 1 := by
      rw [hv]
      apply Nat.mod_eq_of_lt
      by_contra hn
      have hn' : p.val + 1 = 8 * q := by omega
      rw [hv, hn', Nat.mod_self] at he
      exact he rfl
    have hp : p.val % 2 = 0 := by omega
    apply Or.inr
    rw [gvc, if_neg he]
    apply congrArg some
    apply Prod.ext
    · ext
      change (p + 1).val / 2 / 4 = p.val / 2 / 4
      omega
    · change decide ((p + 1).val / 2 % 4 % 2 = 1) = decide (p.val / 2 % 4 % 2 = 1)
      have hhalf : (p + 1).val / 2 = p.val / 2 := by omega
      rw [hhalf]

theorem gSig_boundary_path (x : Fin q × Bool) :
    gSig q (x.1.val, x.2) =
      bdEdge (gc q) (markedBoundaryPos q x false) ++ bdEdge (gc q) (markedBoundaryPos q x true) := by
  rw [gSig, Nat.mod_eq_of_lt x.1.isLt]
  change pPath (gc q) (8 * x.1.val + (if x.2 then 2 else 0)) = _
  rw [pPath_eq]
  have h₀ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0)) =
      markedBoundaryPos q x false := by
    ext
    have ht := (markedBoundaryPos q x false).isLt
    simpa only [cyc, markedBoundaryPos, Bool.false_eq_true, ↓reduceIte, add_zero] using
      Nat.mod_eq_of_lt ht
  have h₁ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0) + 1) =
      markedBoundaryPos q x true := by
    ext
    exact Nat.mod_eq_of_lt (markedBoundaryPos q x true).isLt
  rw [h₀, h₁]

universe v
variable {G : Type v} [Group G]
  (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

theorem read_bdEdge (p : Fin (8 * q)) :
    c.readPath (bdEdge (gc q) p) =
      (barycentricCocycle c).val (cV (gc q) p) (cE (gc q) p) *
        ((barycentricCocycle c).val (cV (gc q) (p + 1)) (cE (gc q) p))⁻¹ := by
  rw [bdEdge, OrdCocycle.readPath_append, ← revPath_edgeHop, OrdCocycle.readPath_revPath,
    barycentricCocycle_val c (cV_le_cE (gc q) p),
    barycentricCocycle_val c (cV1_le_cE (gc q) p)]

def boundaryMarkValue (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x : Fin q × Bool) : G :=
  d.val (.vtx none) (.bed (x.1, x.2, false)) *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, false)))⁻¹ *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, true)) *
      (d.val (.vtx none) (.bed (x.1, x.2, true)))⁻¹)

theorem read_gSig_boundaryMarkValue (x : Fin q × Bool) :
    c.readPath (gSig q (x.1.val, x.2)) = boundaryMarkValue q (barycentricCocycle c) x := by
  rw [gSig_boundary_path, OrdCocycle.readPath_append, read_bdEdge, read_bdEdge,
    markedBoundaryPos_succ]
  simp only [cV, cE, gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true,
    gvc_markedBoundaryPos_end, gec_markedBoundaryPos, boundaryMarkValue, toS]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
universe v w
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω]
  (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x₀ : Ω)

def boundaryVertexSection : KVtx q → Ω
  | none => x₀
  | some x => d.val (.vtx (some x)) (.bed (x.1, x.2, false)) •
      ((d.val (.vtx none) (.bed (x.1, x.2, false)))⁻¹ • x₀)

def boundaryEdgeSection (e : IEdg q) : Ω := (d.val (.vtx none) (.bed e))⁻¹ • x₀



theorem boundarySection_incident
    (hm : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀)
    (v : KVtx q) (e : IEdg q) (hv : v = none ∨ v = some (e.1, e.2.1)) :
    d.val (.vtx v) (.bed e) • boundaryEdgeSection q d x₀ e = boundaryVertexSection q d x₀ v := by
  rcases hv with rfl | rfl
  · exact (smul_inv_smul _ _)
  · exact (by
    obtain ⟨h, b, t⟩ := e
    cases t with
    | false => rfl
    | true =>
      have he := congrArg (fun z => d.val (.vtx (some (h, b))) (.bed (h, b, false)) •
        ((d.val (.vtx none) (.bed (h, b, false)))⁻¹ • z)) (hm (h, b))
      simpa only [boundaryMarkValue, boundaryVertexSection, boundaryEdgeSection,
        mul_smul, inv_smul_smul, smul_inv_smul] using he)

theorem boundarySection_compatible
    (hm : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀) (p : Fin (8 * q)) :
    d.val (cV (gc q) p) (cE (gc q) p) • boundaryEdgeSection q d x₀ (gec q p) =
      boundaryVertexSection q d x₀ (gvc q p) ∧
    d.val (cV (gc q) (p + 1)) (cE (gc q) p) • boundaryEdgeSection q d x₀ (gec q p) =
      boundaryVertexSection q d x₀ (gvc q (p + 1)) :=
  ⟨boundarySection_incident q d x₀ hm _ _ (gvc_endpoint q p),
    boundarySection_incident q d x₀ hm _ _ (gvc_succ_endpoint q p)⟩

variable (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

/-- A point fixed by the actual marked loops extends to a flat section on the
actual subdivided surface. This is a statement for every group action. -/
theorem genus_exists_flat_section
    (hm : ∀ x : Fin q × Bool, c.readPath (gSig q (x.1.val, x.2)) • x₀ = x₀) :
    ∃ s : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) → Ω,
      c.IsFlatSection s ∧ s (gBase q) = x₀ := by
  let d := barycentricCocycle c
  have hd : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀ := by
    intro x
    rw [← read_gSig_boundaryMarkValue q c x]
    exact hm x
  obtain ⟨s, hs, hv, _⟩ := SurfaceSection.exists_flat_section (gc q) d
    (boundaryVertexSection q d x₀) (boundaryEdgeSection q d x₀)
    (boundarySection_compatible q d x₀ hd)
  refine ⟨barycentricSection c s, barycentricSection_flat c s hs, ?_⟩
  rw [gBase, barycentricSection_spx1]
  change s (toS (gvc q) (gec q) (gc q) (.vtx (gvc q (cyc (8 * q) 0)))) = x₀
  rw [gvc_even q rfl]
  exact hv none

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]

structure ComparisonPoint (G : Type v) where
  val : G

instance : MulAction (G × G) (ComparisonPoint G) where
  smul g x := ⟨g.1 * x.val * g.2⁻¹⟩
  one_smul x := by
    change (⟨(1 : G) * x.val * (1 : G)⁻¹⟩ : ComparisonPoint G) = x
    cases x
    simp only [one_mul, inv_one, mul_one]
  mul_smul g h x := by
    change (⟨(g.1 * h.1) * x.val * (g.2 * h.2)⁻¹⟩ : ComparisonPoint G) =
      ⟨g.1 * (h.1 * x.val * h.2⁻¹) * g.2⁻¹⟩
    congr 1
    group

def comparisonOne : ComparisonPoint G := ⟨1⟩

theorem comparisonOne_fixed_iff (g h : G) :
    (g, h) • (comparisonOne : ComparisonPoint G) = comparisonOne ↔ g = h := by
  change (⟨g * 1 * h⁻¹⟩ : ComparisonPoint G) = ⟨1⟩ ↔ g = h
  rw [ComparisonPoint.mk.injEq, mul_one, mul_inv_eq_one]

def product (c d : OrdCocycle P G) : OrdCocycle P (G × G) where
  val a b := (c.val a b, d.val a b)
  comp hab hbd := Prod.ext (c.comp hab hbd) (d.comp hab hbd)


theorem product_readPath (c d : OrdCocycle P G) (p : List ((orderCx P).E × Bool)) :
    (product c d).readPath p = (c.readPath p, d.readPath p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [readPath_cons, (show (product c d).readGerm e = (c.readGerm e, d.readGerm e) by
      obtain ⟨e, b⟩ := e
      cases b <;> rfl), ih, readPath_cons, readPath_cons]
    rfl

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  (c d : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)


/-- The marked equalities give the actual vertex gauge needed to glue the old
and base cocycles along the surface in the geometric mapping cylinder. -/
theorem genus_cocycle_gauge_of_marked
    (hm : ∀ x : Fin q × Bool,
      c.readPath (gSig q (x.1.val, x.2)) = d.readPath (gSig q (x.1.val, x.2))) :
    ∃ k : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) → G,
      k (gBase q) = 1 ∧ ∀ {a b}, a ≤ b → c.val a b * k b = k a * d.val a b := by
  have hf : ∀ x : Fin q × Bool, (OrdCocycle.product c d).readPath (gSig q (x.1.val, x.2)) •
      (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) = OrdCocycle.comparisonOne := by
    intro x
    rw [OrdCocycle.product_readPath, OrdCocycle.comparisonOne_fixed_iff]
    exact hm x
  obtain ⟨s, hs, hb⟩ := genus_exists_flat_section q
    OrdCocycle.comparisonOne (OrdCocycle.product c d) hf
  refine ⟨fun a => (s a).val, congrArg OrdCocycle.ComparisonPoint.val hb, ?_⟩
  intro a b hab
  have h := congrArg OrdCocycle.ComparisonPoint.val (hs hab)
  exact (mul_inv_eq_iff_eq_mul).mp h

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P Q : Type u} [Preorder P] [Preorder Q]
  {G : Type v} [Group G] {H : Type w} [Group H]

theorem eq_of_val_eq {c d : OrdCocycle P G} (h : ∀ a b, c.val a b = d.val a b) :
    c = d := by
  cases c with
  | mk cv cc =>
    cases d with
    | mk dv dc =>
      have he  := funext (fun a => funext (h a))
      cases he
      rfl

theorem comap_readPath (c : OrdCocycle Q G) (f : P → Q) (hf : Monotone f)
    (p : List ((orderCx P).E × Bool)) :
    (c.comap f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [mapPath, List.map_cons]
    rw [readPath_cons, readPath_cons, ih]
    congr 1

def postcompose (c : OrdCocycle P G) (φ : G →* H) : OrdCocycle P H where
  val a b := φ (c.val a b)
  comp hab hbc := by rw [← map_mul, c.comp hab hbc]

theorem postcompose_readPath (c : OrdCocycle P G) (φ : G →* H)
    (p : List ((orderCx P).E × Bool)) :
    (c.postcompose φ).readPath p = φ (c.readPath p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rw [readPath_cons, readPath_cons, map_mul, ih]
    congr 1
    obtain ⟨e, b⟩ := e
    cases b <;> simp [readGerm, postcompose]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [Preorder X] {att : NeSpx A →o X}
  {G : Type v} [Group G]

def positiveOldSimplex (d : QOld A) (hd : d.1.sgn = 0) : NeSpx A :=
  ⟨d.1.spx, Finset.nonempty_iff_ne_empty.mpr (fun h => d.2 ⟨h, hd⟩),
    d.1.isSimplex⟩

theorem posQCube_positiveOldSimplex (d : QOld A) (hd : d.1.sgn = 0) :
    posQCube (positiveOldSimplex d hd) = d := by
  apply Subtype.ext
  apply QCube.ext'
  · rfl
  · intro z _
    exact (congrFun hd z).symm

omit [DecidableEq V] in
theorem positiveOldSimplex_posQCube (s : NeSpx A) :
    positiveOldSimplex (posQCube s) rfl = s := rfl

theorem positiveOld_upward {d e : QOld A} (hde : d ≤ e) (hd : d.1.sgn = 0) :
    e.1.sgn = 0 := by
  funext z
  by_cases hz : z ∈ e.1.spx
  · exact e.1.sgn_eq_zero z hz
  · rw [← hde.2 z hz]
    exact congrFun hd z

theorem new_le_positiveOld {x : X} {d : QOld A}
    (h : qNew (A := A) (att := att) x ≤ qOldIncl d) :
    x ≤ att (positiveOldSimplex d h.1) := by
  obtain ⟨_, hn, hx⟩ := h
  exact hx

variable (old : OrdCocycle (QOld A) G) (base : OrdCocycle X G)
  (k : NeSpx A → G)

def quotientCocycleValue : Qpos A X att → Qpos A X att → G
  | .inl d, .inl e => old.val d e
  | .inl _, .inr _ => 1
  | .inr x, .inl e => if he : e.1.sgn = 0 then
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹
    else 1
  | .inr x, .inr y => base.val x y

theorem quotientCocycleValue_mixed (x : X) (e : QOld A) (he : e.1.sgn = 0) :
    quotientCocycleValue (att := att) old base k (.inr x) (.inl e) =
      base.val x (att (positiveOldSimplex e he)) * (k (positiveOldSimplex e he))⁻¹ := by
  simp only [quotientCocycleValue, dif_pos he]

variable (hk : ∀ {s t : NeSpx A}, s ≤ t →
  old.val (posQCube s) (posQCube t) * k t = k s * base.val (att s) (att t))

include hk in
theorem quotientCocycleValue_comp {a b c : Qpos A X att} (hab : a ≤ b) (hbc : b ≤ c) :
    quotientCocycleValue old base k a b * quotientCocycleValue old base k b c =
      quotientCocycleValue old base k a c := by
  cases a with
  | inl d =>
    cases b with
    | inl e =>
      cases c with
      | inl f => exact old.comp hab hbc
      | inr z => exact False.elim hbc
    | inr y => exact False.elim hab
  | inr x =>
    cases b with
    | inl e =>
      cases c with
      | inr z => exact False.elim hbc
      | inl f =>
        have he  := hab.1
        have hf  := positiveOld_upward hbc he
        have hef : positiveOldSimplex e he ≤ positiveOldSimplex f hf := hbc.1
        have hx := new_le_positiveOld hab
        have hg := hk hef
        rw [posQCube_positiveOldSimplex, posQCube_positiveOldSimplex] at hg
        have ht : (k (positiveOldSimplex e he))⁻¹ * old.val e f =
            base.val (att (positiveOldSimplex e he)) (att (positiveOldSimplex f hf)) *
              (k (positiveOldSimplex f hf))⁻¹ := by
          calc
            _ = (k (positiveOldSimplex e he))⁻¹ *
                (old.val e f * k (positiveOldSimplex f hf)) *
                  (k (positiveOldSimplex f hf))⁻¹ := by group
            _ = _ := by rw [hg]; group
        rw [quotientCocycleValue_mixed old base k x e he,
          quotientCocycleValue_mixed old base k x f hf]
        change (base.val x (att (positiveOldSimplex e he)) *
            (k (positiveOldSimplex e he))⁻¹) * old.val e f = _
        rw [mul_assoc, ht, ← mul_assoc, base.comp hx (att.monotone hef)]
    | inr y =>
      cases c with
      | inr z => exact base.comp hab hbc
      | inl f =>
        have hf : f.1.sgn = 0 := hbc.1
        have hy := new_le_positiveOld hbc
        rw [quotientCocycleValue_mixed old base k y f hf,
          quotientCocycleValue_mixed old base k x f hf]
        change base.val x y * (base.val y (att (positiveOldSimplex f hf)) * _) = _
        rw [← mul_assoc, base.comp hab hy]

def gluedQuotientCocycle : OrdCocycle (Qpos A X att) G where
  val := quotientCocycleValue old base k
  comp := quotientCocycleValue_comp old base k hk

theorem gluedQuotientCocycle_old (d e : QOld A) :
    (gluedQuotientCocycle old base k hk).val
      (qOldIncl (att := att) d) (qOldIncl e) = old.val d e := rfl

theorem gluedQuotientCocycle_base (x y : X) :
    (gluedQuotientCocycle old base k hk).val
      (qNew (att := att) x) (qNew y) = base.val x y := rfl

theorem gluedQuotientCocycle_cylinder (s : NeSpx A) :
    (gluedQuotientCocycle old base k hk).val
      (qNew (att := att) (att s)) (qOldIncl (posQCube s)) = (k s)⁻¹ := by
  change quotientCocycleValue old base k (.inr (att s)) (.inl (posQCube s)) = _
  rw [quotientCocycleValue_mixed old base k (att s) (posQCube s) rfl,
    positiveOldSimplex_posQCube, base.val_refl, one_mul]

def quotientOldBasedInclusion (s : NeSpx A) :
    Pi1 (orderCx (QOld A)) (posQCube s) →*
      Pi1 (orderCx (Qpos A X att)) (qNew (att := att) (att s)) :=
  (pi1Conj (isPath_ordPos (qNew_att_le_qOldIncl (att := att) s))).comp
    (pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) (posQCube s))

/-- The normalized cylinder edge makes the reverse reading on the based old
inclusion equal to the original old reading, without a conjugation factor. -/
theorem monodromy_quotientOldBasedInclusion (s : NeSpx A)
    (c : OrdCocycle (Qpos A X att) G) (χ : Pi1 (orderCx (QOld A)) (posQCube s) →* G)
    (hcyl : c.val (qNew (att s)) (qOldIncl (posQCube s)) = 1)
    (hread : ∀ p : Loop (orderCx (QOld A)) (posQCube s),
      c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
        χ (Pi1.mk p)) :
    (c.monodromy (qNew (att s))).comp (quotientOldBasedInclusion (att := att) s) = χ := by
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath
    (([ordPos (qNew_att_le_qOldIncl s)] ++
      mapPath (orderCxMap (qOldIncl) qOldIncl_monotone) p.1) ++
      revPath [ordPos (qNew_att_le_qOldIncl s)]) = _
  simp only [OrdCocycle.readPath_append, OrdCocycle.readPath_revPath,
    OrdCocycle.readPath_cons, OrdCocycle.readPath_nil,
    OrdCocycle.readGerm_ordPos, hcyl, one_mul, mul_one, inv_one]
  exact hread p

theorem monodromy_quotientBaseInclusion (x : X)
    (c : OrdCocycle (Qpos A X att) G) (d : OrdCocycle X G)
    (hd : ∀ a b, c.val (qNew a) (qNew b) = d.val a b) :
    (c.monodromy (qNew x)).comp
      (pi1Map (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x) =
        d.monodromy x := by
  have he : c.comap (qNew) qNew_monotone = d :=
    OrdCocycle.eq_of_val_eq hd
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  change c.readPath (mapPath (orderCxMap (qNew) qNew_monotone) p.1) = _
  rw [← OrdCocycle.comap_readPath, he]
  rfl

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {X : Type} [Preorder X]
  (att : NeSpx (cmpRel (GenusVertex q)) →o X) {G : Type v} [Group G]
  (old : OrdCocycle (QOld (cmpRel (GenusVertex q))) G) (base : OrdCocycle X G)

/-- The actual standard marked equalities suffice to glue on Q, preserving
both original cocycles and giving value 1 to the base cylinder edge. -/
theorem exists_quotientCocycle_of_marked
    (hm : ∀ x : Fin q × Bool,
      old.readPath (mapPath (surfCx (cmpRel (GenusVertex q)))
        (gSig q (x.1.val, x.2))) =
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q)) X att) G,
      (∀ d e, c.val (qOldIncl d) (qOldIncl e) = old.val d e) ∧
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q))) (qOldIncl (posQCube (gBase q))) = 1 := by
  have hm' : ∀ x : Fin q × Bool,
      (old.comap posQCube posQCube_monotone).readPath (gSig q (x.1.val, x.2)) =
      (base.comap att att.monotone).readPath (gSig q (x.1.val, x.2)) := by
    intro x
    simpa only [OrdCocycle.comap_readPath, surfCx] using hm x
  obtain ⟨k, hb, hk⟩ := genus_cocycle_gauge_of_marked q
    (old.comap posQCube posQCube_monotone) (base.comap att att.monotone) hm'
  refine ⟨gluedQuotientCocycle old base k hk, ?_, ?_, ?_⟩
  · exact gluedQuotientCocycle_old old base k hk
  · exact gluedQuotientCocycle_base old base k hk
  · rw [gluedQuotientCocycle_cylinder, hb, inv_one]

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb.OrdCocycle
open SpanningTree
open scoped Classical
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (T : SpanningTree (orderCx P)) (φ : PresGroup (treeRel T) →* G)

def fromTreeReceiver : OrdCocycle P G where
  val a b := if hab : a ≤ b then φ (wordClass T [ordPos hab]) else 1
  comp := by
    intro a b c hab hbc
    simp only [dif_pos hab, dif_pos hbc, dif_pos (hab.trans hbc)]
    rw [← map_mul, ← wordClass_append]
    exact congrArg φ (wordClass_htpy T (htpy_orderCx_tri hab hbc))


theorem fromTreeReceiver_readPath (p : List ((orderCx P).E × Bool)) :
    (fromTreeReceiver T φ).readPath p = φ (wordClass T p) := by
  induction p with
  | nil => simp [wordClass, pathWord_nil]
  | cons e p ih =>
    rw [readPath_cons, (show (fromTreeReceiver T φ).readGerm e = φ (wordClass T [e]) by
      obtain ⟨⟨⟨a, b⟩, hab⟩, side⟩ := e
      cases side
      · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1)⁻¹ =
          φ (wordClass T [ordNeg hab])
        rw [dif_pos hab]
        have hr : wordClass T [ordNeg hab] = (wordClass T [ordPos hab])⁻¹ := by
          change QuotientGroup.mk (pathWord T [ordNeg hab]) =
            (QuotientGroup.mk (pathWord T [ordPos hab]))⁻¹
          rw [← QuotientGroup.mk_inv, ← pathWord_revPath]
          rfl
        rw [hr, map_inv]
      · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1) = _
        rw [dif_pos hab]
        rfl), ih, ← map_mul, ← wordClass_append]
    rfl

/-- Every actual fundamental-group homomorphism is realized by a cocycle.
The spanning tree is constructed from connectedness and has the prescribed root. -/
theorem exists_of_monodromy (hP : IsConnected (orderCx P)) (x : P)
    (ψ : Pi1 (orderCx P) x →* G) :
    ∃ c : OrdCocycle P G, ∀ p : Loop (orderCx P) x,
      c.readPath p.1 = ψ (Pi1.mk p) := by
  obtain ⟨T, hT⟩ := SpanningTree.exists_of_isConnected hP x
  subst x
  refine ⟨fromTreeReceiver T (ψ.comp (SpanningTree.presToPi1 T)), ?_⟩
  intro p
  rw [fromTreeReceiver_readPath]
  change ψ (SpanningTree.presToPi1 T (SpanningTree.pi1ToPres T (Pi1.mk p))) = _
  rw [SpanningTree.presToPi1_pi1ToPres]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
universe v
variable (q₀ : ℕ) [NeZero q₀] {G : Type v} [Group G]
  (φ : PresGroup (namedSpinePresentation q₀) →* G)

def oldSpineReceiver :
    Pi1 (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)) →* G :=
  φ.comp (namedSpineToOldEquiv q₀).symm.toMonoidHom


/-- The receiver is carried by an actual cocycle on the old geometric block;
the standard surface loops read the exact distinguished names. -/
theorem exists_oldSpineCocycle :
    ∃ c : OrdCocycle (QOld (cmpRel (GenusVertex q₀))) G,
      (∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)),
        c.readPath p.1 = oldSpineReceiver q₀ φ (Pi1.mk p)) ∧
      ∀ x : Fin q₀ × Bool,
        c.readPath (mapPath (surfCx (cmpRel (GenusVertex q₀)))
          (gSig q₀ (x.1.val, x.2))) =
          φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) := by
  letI : Nonempty (GenusVertex q₀) := ⟨cV (gc q₀) (cyc (8 * q₀) 0)⟩
  obtain ⟨c, hread⟩ := OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld
    (posQCube (gBase q₀))
    (oldSpineReceiver q₀ φ)
  refine ⟨c, hread, ?_⟩
  intro x
  rw [hread ⟨_, isPath_mapPath (surfCx _) (isPath_gSig q₀ (x.1.val, x.2))⟩]
  exact (by
    have hm := namedSpineToOld_marked q₀ x
    rw [spineMarkedLoop_toOld_class] at hm
    change φ ((namedSpineToOldEquiv q₀).symm _) = _
    rw [← hm, MulEquiv.symm_apply_apply])

/-- Given the actual readings of the base, the reverse receiver extends over
the whole geometric quotient and has the prescribed homomorphism on old loops. -/
theorem exists_quotientReceiver {X : Type} [Preorder X]
    (att : NeSpx (cmpRel (GenusVertex q₀)) →o X) (base : OrdCocycle X G)
    (hbase : ∀ x : Fin q₀ × Bool,
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q₀ (x.1.val, x.2))) =
        φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q₀)) X att) G,
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q₀))) (qOldIncl (posQCube (gBase q₀))) = 1 ∧
      ∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)),
        c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
          oldSpineReceiver q₀ φ (Pi1.mk p) := by
  obtain ⟨old, hread, hmark⟩ := exists_oldSpineCocycle q₀ φ
  obtain ⟨c, hcold, hcbase, hccyl⟩ := exists_quotientCocycle_of_marked q₀ att old base
    (fun x => (hmark x).trans (hbase x).symm)
  refine ⟨c, hcbase, hccyl, ?_⟩
  intro p
  have he : c.comap (qOldIncl (att := att)) qOldIncl_monotone = old :=
    OrdCocycle.eq_of_val_eq hcold
  rw [← OrdCocycle.comap_readPath, he]
  exact hread p

variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
universe v
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
  {G : Type v} [Group G] (j : PresGroup ρ →* G)

/-- The receiver on the named base presentation is the original receiver
after the proved elimination of the auxiliary names. -/
def namedBaseReceiver : PresGroup (namedPres ρ q u) →* G :=
  j.comp (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho)


def namedBaseCocycle :
    OrdCocycle (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q)
      (namedB (α := α) q) q)) G :=
  (presGroupCocycle (namedPres ρ q u)
    (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
    (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u))).postcompose
      (namedBaseReceiver ρ q u hrho j)


/-- Concrete gluing over the prescribed word model. All base relators and
the surface comparison are discharged by the original word relation and
the exact distinguished-name agreement, rather than assumed presentations. -/

abbrev namedQuotientPos :=
  Qpos (cmpRel (GenusVertex q))
    (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q))
    (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

abbrev namedQuotientBase : namedQuotientPos ρ q u :=
  qNew (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
    (gBase q))

def namedSpineIntoQuotient :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (quotientOldBasedInclusion (gBase q)).comp (namedSpineToOldEquiv q).toMonoidHom

/-- A reverse homomorphism on the actual geometric fundamental group, with
its full action on the named spine and on the base proved simultaneously.
This is stronger than agreement merely on distinguished marked generators. -/
theorem exists_namedQuotientReading
    (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp
        (pi1Map (orderCxMap (qNew (att := genusNonemptyAtt (namedPres ρ q u)
          (namedA (α := α) q) (namedB (α := α) q) q)) qNew_monotone)
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q))) =
        (namedBaseCocycle ρ q u hrho j).monodromy
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q)) := by
  obtain ⟨c, hb, he, ho⟩ := (by
    apply exists_quotientReceiver q φ _ (namedBaseCocycle ρ q u hrho j)
    intro x
    exact (show (namedBaseCocycle ρ q u hrho j).readPath
      (mapPath (orderCxMap
        (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB q) q)
        (genusNonemptyAtt (namedPres ρ q u) (namedA q) (namedB q) q).monotone)
        (gSig q (x.1.val, x.2))) = j (QuotientGroup.mk (u x)) by
      let ep := namedPres ρ q u
      let aa := namedA (α := α) q
      let bb := namedB (α := α) q
      let w := genusNonemptyW ep aa bb q
      have hh := (namedBaseCocycle ρ q u hrho j).readPath_htpy
        (genusNonempty_hread ep aa bb q PUnit.unit.{1} (x.1.val, x.2))
      simp at hh
      rw [hh]
      have hl : genusLw aa bb q PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] :=
        namedLw_eq q PUnit.unit x
      rw [hl]
      rw [namedBaseCocycle, OrdCocycle.postcompose_readPath]
      change namedBaseReceiver ρ q u hrho j
        (reading w (fun a => (QuotientGroup.mk (FreeGroup.of a) : PresGroup ep))
          (presGroup_wordVal_eq_one ep w (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))
          (genClass w (Sum.inr x))) = _
      rw [reading_genClass]
      exact (by
        change j (QuotientGroup.mk
          (SurfaceWordExpansion.foldNames u (FreeGroup.of (Sum.inr x)))) = _
        simp only [SurfaceWordExpansion.foldNames, FreeGroup.lift_apply_of, Sum.elim_inr])).trans (hm x).symm)
  refine ⟨c.monodromy (namedQuotientBase ρ q u), ?_, ?_⟩
  · have h := monodromy_quotientOldBasedInclusion (gBase q) c
      (oldSpineReceiver q φ) he ho
    change ((c.monodromy (namedQuotientBase ρ q u)).comp
      (quotientOldBasedInclusion (gBase q))).comp (namedSpineToOldEquiv q).toMonoidHom = φ
    rw [h]
    apply MonoidHom.ext
    intro z
    change φ ((namedSpineToOldEquiv q).symm ((namedSpineToOldEquiv q) z)) = φ z
    rw [MulEquiv.symm_apply_apply]
  · exact monodromy_quotientBaseInclusion _ c (namedBaseCocycle ρ q u hrho j) hb

end FiniteChains.Davis.Genus
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
theorem pi1Conj_empty_apply {K : Complex2} (a : K.V) (z : Pi1 K a) :
    pi1Conj (show IsPath K.src K.tgt [] a a from rfl) z = z := by
  refine Quotient.inductionOn z ?_
  intro p
  apply Quotient.sound
  simp [conjLoop]
end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe v w
variable {P : Type} [Preorder P] {G : Type v} [Group G] {H : Type w} [Group H]

theorem monodromy_baseEq (c : OrdCocycle P G) {a b : P} (h : a = b)
    (z : Pi1 (orderCx P) a) :
    c.monodromy b (pi1BaseEqEquiv h z) = c.monodromy a z := by
  subst b
  rfl

theorem postcompose_monodromy (c : OrdCocycle P G) (φ : G →* H) (a : P) :
    (c.postcompose φ).monodromy a = φ.comp (c.monodromy a) := by
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  exact postcompose_readPath c φ p.1

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}
  {X : Type} [Preorder X] {att : NeSpx A →o X}

theorem quotientOldBasedInclusion_surface (s : NeSpx A)
    (p : Loop (orderCx (NeSpx A)) s) :
    quotientOldBasedInclusion (att := att) s
      (Pi1.mk ⟨mapPath (surfCx A) p.1, isPath_mapPath (surfCx A) p.2⟩) =
      pi1Map (orderCxMap (qNew (att := att)) qNew_monotone) (att s)
        (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p.1,
          isPath_mapPath _ p.2⟩) := by
  let z := pi1Map (orderCxMap (qNew (att := att)) qNew_monotone) (att s)
    (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p.1, isPath_mapPath _ p.2⟩)
  have hpos := isPath_ordPos (qNew_att_le_qOldIncl (att := att) s)
  have hneg := isPath_ordNeg (qNew_att_le_qOldIncl (att := att) s)
  have hnat := htpy_loop_mapPath_le
    (qNew_monotone.comp att.monotone)
    (qOldIncl_monotone.comp posQCube_monotone)
    (fun t => qNew_att_le_qOldIncl t) p.2
  have he : pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) (posQCube s)
      (Pi1.mk ⟨mapPath (surfCx A) p.1, isPath_mapPath (surfCx A) p.2⟩) =
        pi1Conj hneg z := by
    apply Quotient.sound
    change Htpy (orderCx (Qpos A X att)) (qOldIncl (att := att) (posQCube s))
      (qOldIncl (att := att) (posQCube s)) _ _
    convert hnat using 1 <;>
      simp [z, conjLoop, mapPath, surfCx, orderCxMap, List.map_map, Function.comp_def]
  have he'  := congrArg (pi1Conj hpos) he
  erw [he', pi1Conj_pi1Conj]
  calc
    pi1Conj (hpos.append hneg) z = pi1Conj (isPath_nil' (qNew (att s))) z :=
      pi1Conj_congr _ _ (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl (att := att) s)) z
    _ = z := pi1Conj_empty_apply _ z

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedBasePos :=
  PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

abbrev namedAtt : NeSpx (cmpRel (GenusVertex q)) →o namedBasePos ρ q u :=
  genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q

theorem namedBasePos_isConnected : IsConnected (orderCx (namedBasePos ρ q u)) :=
  genusNonemptyW_isConnected (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q

def namedBaseAlpha : PresGroup (namedPres ρ q u) →*
    Pi1 (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
  (pi1BaseEqEquiv (genusNonemptyAtt_base (namedPres ρ q u)
    (namedA (α := α) q) (namedB (α := α) q) q).symm).toMonoidHom.comp
      (alphaHomW (namedPres ρ q u)
        (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
        (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))

def namedBaseIntoQuotient : PresGroup (namedPres ρ q u) →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (pi1Map (orderCxMap (qNew (att := namedAtt ρ q u)) qNew_monotone)
    (namedAtt ρ q u (gBase q))).comp (namedBaseAlpha ρ q u)

def sourceIntoNamedQuotient : PresGroup ρ →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (namedBaseIntoQuotient ρ q u).comp
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho)


theorem namedSpineIntoQuotient_marked (x : Fin q × Bool) :
    namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (u x)) := by
  change quotientOldBasedInclusion (gBase q)
    (namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
  erw [namedSpineToOld_marked, spineMarkedLoop_toOld_class,
    quotientOldBasedInclusion_surface (gBase q)
      ⟨gSig q (x.1.val, x.2), isPath_gSig q (x.1.val, x.2)⟩]
  erw [← (show namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk ⟨mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
        (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩ by
    let w := genusNonemptyW (namedPres ρ q u) (namedA q) (namedB q) q
    let p : Loop (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
      ⟨genLoop w (Sum.inr x), by
        erw [show namedAtt ρ q u (gBase q) = ptBase w from genusNonemptyAtt_base _ _ _ _]
        exact isPath_genLoop w (Sum.inr x)⟩
    have hp : namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
        Pi1.mk p := by
      erw [namedBaseAlpha, MonoidHom.comp_apply, alphaHomW_gen]
      exact pi1BaseEqEquiv_mk _ ⟨genLoop w (Sum.inr x), isPath_genLoop w (Sum.inr x)⟩ p rfl
    erw [hp]
    apply Quotient.sound
    have hh := genusNonempty_hread (namedPres ρ q u) (namedA q)
      (namedB q) q PUnit.unit.{1} (x.1.val, x.2)
    simp at hh
    have hl : genusLw (namedA q) (namedB (α := α) q) q
        PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] := namedLw_eq q PUnit.unit x
    erw [hl] at hh
    change Htpy (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q))
      (namedAtt ρ q u (gBase q)) (genLoop w (Sum.inr x))
      (mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
        (gSig q (x.1.val, x.2)))
    simpa [namedAtt, genusNonemptyAtt_base, wordLoop, letterLoop] using hh.symm)]
  exact congrArg (namedBaseIntoQuotient ρ q u)
    (SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x)

theorem namedBaseCocycle_alpha {G : Type} [Group G] (j : PresGroup ρ →* G)
    (z : PresGroup (namedPres ρ q u)) :
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u z) = namedBaseReceiver ρ q u hrho j z := by
  erw [namedBaseAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    OrdCocycle.monodromy_baseEq]
  erw [namedBaseCocycle, OrdCocycle.postcompose_monodromy,
    presGroupCocycle_monodromy, MonoidHom.comp_apply, readingPresW_alphaHomW]

/-- The reverse receiver constructed on Q is a left inverse on the whole
source presentation group, not just on its chosen generators. -/
theorem exists_namedQuotientReading_both {G : Type} [Group G]
    (j : PresGroup ρ →* G) (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp (sourceIntoNamedQuotient ρ q u hrho) = j := by
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading ρ q u hrho j φ hm
  refine ⟨ψ, ho, ?_⟩
  apply MonoidHom.ext
  intro z
  have hh := DFunLike.congr_fun hb
    (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z))
  erw [show ψ (sourceIntoNamedQuotient ρ q u hrho z) =
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z))
      from hh]
  erw [namedBaseCocycle_alpha]
  change j (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z)) = j z
  erw [SurfaceWordExpansion.elimination_inclusion]

section ComparisonMaps
variable {H : Type} [Group H] (j : PresGroup ρ →* H)
  (φ : PresGroup (namedSpinePresentation q) →* H)
  (hm : ∀ x : Fin q × Bool,
    φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x)))

def finiteSpineComparisonFree : FreeGroup (α ⊕ SpinePresentationGen q) →* H :=
  FreeGroup.lift (Sum.elim (fun a => j (QuotientGroup.mk (FreeGroup.of a)))
    (fun z => φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))

theorem finiteSpineComparisonFree_old (w : FreeGroup α) :
    finiteSpineComparisonFree ρ q j φ (FreeGroup.map Sum.inl w) =
      j (QuotientGroup.mk w) := by
  have h : (finiteSpineComparisonFree ρ q j φ).comp (FreeGroup.map Sum.inl) =
      j.comp (QuotientGroup.mk' (relSub ρ)) := by
    apply FreeGroup.ext_hom
    intro a
    simp [finiteSpineComparisonFree]
  exact DFunLike.congr_fun h w


def finiteSpineComparisonMaps :
    BlockMaps ρ (finiteSpineWordBlock q u) j where
  b _ := finiteSpineComparisonFree ρ q j φ
  mark _ a := by simp [finiteSpineComparisonFree]
  rel s m := by
    have h := DFunLike.congr_fun
      (show ((finiteSpineComparisonFree ρ q j φ).comp
      (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen q) (fun _ => u) s)).comp
      (FreeGroup.map Sum.swap) = φ.comp (QuotientGroup.mk' (relSub (namedSpinePresentation q))) by
        apply FreeGroup.ext_hom
        rintro (z | x)
        · simp [finiteSpineComparisonFree]
        · simp
          erw [finiteSpineComparisonFree_old]
          exact (hm x).symm) (namedSpinePresentation q m)
    change finiteSpineComparisonFree ρ q j φ
      (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen q) (fun _ => u) s
        (FreeGroup.map Sum.swap (namedSpinePresentation q m))) = 1
    simp only [MonoidHom.comp_apply] at h
    rw (config := { transparency := .default }) [h]
    have hz : (QuotientGroup.mk (namedSpinePresentation q m) :
        PresGroup (namedSpinePresentation q)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
    change φ (QuotientGroup.mk (namedSpinePresentation q m)) = 1
    rw (config := { transparency := .default }) [hz, map_one]

end ComparisonMaps

def finiteSpineToQuotient :
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) →*
      Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (finiteSpineComparisonMaps ρ q u (sourceIntoNamedQuotient ρ q u hrho)
    (namedSpineIntoQuotient ρ q u) (namedSpineIntoQuotient_marked ρ q u hrho)).psi

def singleSpineNamedReceiver : PresGroup (namedSpinePresentation q) →*
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) :=
  familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleSpineNamedReceiver_marked (x : Fin q × Bool) :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
        (QuotientGroup.mk (u x)) := familySpineHom_marked ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x

theorem singleSpineNamedReceiver_internal (z : SpinePresentationGen q) :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) =
      QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)) := rfl

theorem finiteSpineToQuotient_source :
    (finiteSpineToQuotient ρ q u hrho).comp
      (substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)) =
        sourceIntoNamedQuotient ρ q u hrho :=
  BlockMaps.psi_comp_substHomF _ (finiteSpineWordBlock_filled ρ q u hrho)

theorem finiteSpineToQuotient_internal (z : SpinePresentationGen q) :
    finiteSpineToQuotient ρ q u hrho
      (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))) =
      namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) := by simp_all [finiteSpineToQuotient, BlockMaps.psi_mk, FreeGroup.lift_apply_of, BlockMaps.gen_inr, finiteSpineComparisonMaps, finiteSpineComparisonFree, Sum.elim_inr]

/-- The same forward comparison transports the entire block receiver,
including its internal generators, to the genuine geometric block map. -/
theorem finiteSpineToQuotient_spine :
    (finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u) =
      namedSpineIntoQuotient ρ q u := by
  have h : ((finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u)).comp
      (QuotientGroup.mk' (relSub (namedSpinePresentation q))) =
      (namedSpineIntoQuotient ρ q u).comp
        (QuotientGroup.mk' (relSub (namedSpinePresentation q))) := by
    apply FreeGroup.ext_hom
    rintro (z | x)
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))) = _
      erw [singleSpineNamedReceiver_internal, finiteSpineToQuotient_internal]
      rfl
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
      erw [singleSpineNamedReceiver_marked ρ q u hrho]
      have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (u x))
      exact hs.trans (namedSpineIntoQuotient_marked ρ q u hrho x).symm
  apply MonoidHom.ext
  intro z
  refine QuotientGroup.induction_on z ?_
  intro w
  exact DFunLike.congr_fun h w

/-- The actual single substituted group has a left inverse to its geometric
comparison. In particular no extra injectivity premise is needed for the map
used to transport the full group-ring coefficients into the universal cover. -/

def finiteSpineCoefficientMap :
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))) →+*
      MonoidAlgebra ℤ (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineToQuotient ρ q u hrho)

/-- A polygon multiple found in the geometric group ring reflects back to
the original substituted group ring. The proved reverse group homomorphism
supplies the coefficient retraction; no flatness of coinvariants is assumed. -/
theorem finiteSpineCoefficientMap_reflect_multiple {I : Type}
    (β γ : I → MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (w : MonoidAlgebra ℤ
      (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)))
    (hβ : ∀ i, finiteSpineCoefficientMap ρ q u hrho (β i) =
      w * finiteSpineCoefficientMap ρ q u hrho (γ i)) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ i, β i = a * γ i := by
  obtain ⟨ψ, hψ⟩ := (show ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →*
        PresGroup (substPresF ρ (finiteSpineWordBlock q u)),
      ψ.comp (finiteSpineToQuotient ρ q u hrho) = MonoidHom.id _ by
    let j := substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
    let φ := singleSpineNamedReceiver ρ q u
    obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading_both ρ q u hrho j φ
      (singleSpineNamedReceiver_marked ρ q u hrho)
    refine ⟨ψ, ?_⟩
    have hfree : ((ψ.comp (finiteSpineToQuotient ρ q u hrho)).comp
        (QuotientGroup.mk' (relSub (substPresF ρ (finiteSpineWordBlock q u))))) =
        QuotientGroup.mk' (relSub (substPresF ρ (finiteSpineWordBlock q u))) := by
      apply FreeGroup.ext_hom
      rintro (a | ⟨s, z⟩)
      · have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
          (QuotientGroup.mk (FreeGroup.of a))
        change ψ (finiteSpineToQuotient ρ q u hrho
          (j (QuotientGroup.mk (FreeGroup.of a)))) = j (QuotientGroup.mk (FreeGroup.of a))
        erw [show finiteSpineToQuotient ρ q u hrho
          (j (QuotientGroup.mk (FreeGroup.of a))) =
          sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (FreeGroup.of a)) from hs]
        exact DFunLike.congr_fun hb (QuotientGroup.mk (FreeGroup.of a))
      · cases s
        change ψ (finiteSpineToQuotient ρ q u hrho
          (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)))) = _
        erw [finiteSpineToQuotient_internal]
        calc
          _ = φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) :=
            DFunLike.congr_fun ho _
          _ = _ := singleSpineNamedReceiver_internal ρ q u z
    apply MonoidHom.ext
    intro z
    refine QuotientGroup.induction_on z ?_
    intro w
    exact DFunLike.congr_fun hfree w)
  let r := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hr : ∀ z, r (finiteSpineCoefficientMap ρ q u hrho z) = z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp_all
    | single g n =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain ψ
        (Finsupp.mapDomain (finiteSpineToQuotient ρ q u hrho) (Finsupp.single g n)) = _
      erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      have hg := DFunLike.congr_fun hψ g
      erw [hg]
      rfl
  refine ⟨r w, ?_⟩
  grind

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem pi1Map_comp_apply (f : Hom K Y) (g : Hom Y Z) (a : K.V)
    (z : Pi1 K a) :
    pi1Map (g.comp f) a z = pi1Map g (f.onV a) (pi1Map f a z) := by
  refine Quotient.inductionOn z ?_
  intro p
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp only [mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem pi1Map_baseEq_apply (f : Hom K Y) {a b : K.V} (h : a = b)
    (z : Pi1 K a) :
    pi1Map f b (pi1BaseEqEquiv h z) =
      pi1BaseEqEquiv (congrArg f.onV h) (pi1Map f a z) := by
  subst b
  rfl

theorem pi1Conj_baseEq_end {a b c : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a c) (h : b = c)
    (hp' : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj hp (pi1BaseEqEquiv h z) = pi1Conj hp' z := by
  subst c
  rfl

theorem pi1Conj_reverse_cancel {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K b) :
    pi1Conj (isPath_revPath hp) (pi1Conj hp z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] b b from rfl)
    (htpy_revPath_append hp) z).trans
    (pi1Conj_empty_apply b z)

theorem pi1Conj_cancel_reverse {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) (z : Pi1 K a) :
    pi1Conj hp (pi1Conj (isPath_revPath hp) z) = z := by
  erw [pi1Conj_pi1Conj]
  exact (pi1Conj_congr _ (show IsPath K.src K.tgt [] a a from rfl)
    (htpy_append_revPath hp) z).trans
    (pi1Conj_empty_apply a z)

theorem chain1_comp_apply (f : Hom K Y) (g : Hom Y Z) (c : K.E →₀ ℤ) :
    chain1 (g.comp f) c = chain1 g (chain1 f c) := by
  change Finsupp.mapDomain (g.onE ∘ f.onE) c =
    Finsupp.mapDomain g.onE (Finsupp.mapDomain f.onE c)
  erw [Finsupp.mapDomain_comp]

theorem chain2_comp_apply (f : Hom K Y) (g : Hom Y Z) (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  erw [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical

variable (q : ℕ) [NeZero q]

def markedSpineToOld : Hom (markedSpineCx q)
    (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

theorem markedSpineToOld_root :
    (markedSpineToOld q).onV (markedSpineTree q).root = posQCube (gBase q) := by
  erw [markedSpineTree_root]
  rfl

/-- Naming the marked words does not change the geometric map from the
tree presentation of the connected spine. This identity holds on every word. -/
theorem namedSpineToOld_inclusion (z : PresGroup (spinePresentation q)) :
    namedSpineToOldEquiv q
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
    pi1BaseEqEquiv (markedSpineToOld_root q)
      (pi1Map (markedSpineToOld q) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z)) := by
  have hnamed : (namedSpinePi1Equiv q).symm
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      SpanningTree.presToPi1 (markedSpineTree q) z := by
    change (spinePresentationPi1Equiv q).symm
      ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
    erw [MulEquiv.symm_apply_apply]
    rfl
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          (NamedPresentation.inclusion (spinePresentation q)
            (spinePresentationMarkedWord q) z)))) = _
  erw [hnamed]
  erw [← pi1Map_comp_apply (componentIncl (genusSpineCx q) (spineBase q))
    (genusSpineToOld q) (markedSpineBase q)]
  exact pi1Map_baseEq_apply (markedSpineToOld q) (markedSpineTree_root q) _

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def markedSpineToNamedQuotient : Hom (markedSpineCx q)
    (orderCx (namedQuotientPos ρ q u)) :=
  (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone).comp
    (markedSpineToOld q)

theorem markedSpineToNamedQuotient_root :
    (markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root =
      qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q)) :=
  congrArg (qOldIncl (att := namedAtt ρ q u)) (markedSpineToOld_root q)

def spineQuotientCylinderPath :
    List ((orderCx (namedQuotientPos ρ q u)).E × Bool) :=
  [ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))]

theorem spineQuotientCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u)
      ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
  erw [markedSpineToNamedQuotient_root]
  exact isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))

/-- The geometric map on all spine words, with the actual cylinder path
accounting for the two different base vertices. -/

abbrev singleReceivedSpineCover : Complex2 :=
  receivedSpineCover ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

/-- The proved faithful comparison expressed at the old spine base vertex. -/
def finiteSpineOldRootReceiver :
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) →*
      Pi1 (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))).comp
    (finiteSpineToQuotient ρ q u hrho)

theorem finiteSpineOldRootReceiver_compatible :
    (finiteSpineOldRootReceiver q ρ u hrho).comp
      (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit) =
      (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := by
  apply MonoidHom.ext
  intro z
  change pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
    (finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q)
          (spinePresentationMarkedWord q) z))) = _
  have h := DFunLike.congr_fun (finiteSpineToQuotient_spine ρ q u hrho)
    (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
  erw [show finiteSpineToQuotient ρ q u hrho
      (singleSpineNamedReceiver ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)) =
      namedSpineIntoQuotient ρ q u
        (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z)
      from h]
  erw [(show namedSpineIntoQuotient ρ q u
      (NamedPresentation.inclusion (spinePresentation q) (spinePresentationMarkedWord q) z) =
      pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
        (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) by
    change pi1Conj (isPath_ordPos
        (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
      (pi1Map (orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone)
        (posQCube (gBase q))
        (namedSpineToOldEquiv q
          (NamedPresentation.inclusion (spinePresentation q)
            (spinePresentationMarkedWord q) z))) = _
    erw [namedSpineToOld_inclusion, pi1Map_baseEq_apply]
    erw [pi1Conj_baseEq_end
      (isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q)))
      (markedSpineToNamedQuotient_root q ρ u)
      (spineQuotientCylinderPath_isPath q ρ u)]
    erw [← pi1Map_comp_apply]
    rfl), pi1Conj_reverse_cancel]
  rfl

/-- A genuine cellular comparison, with compatibility now proved from the
actual substituted presentation instead of required as an extra hypothesis. -/
def receivedSpineToQuotientOldRoot :
    Hom (singleReceivedSpineCover q ρ u)
      (uCover (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root)) :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)

/-- The comparison now lands at the base vertex used by the old/star
relative filling theorem. The change of base is the actual cylinder path. -/
def receivedSpineToQuotient :
    Hom (singleReceivedSpineCover q ρ u)
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (receivedSpineToQuotientOldRoot q ρ u hrho)

/-- Exact geometric marked boundary, retaining every coefficient of the
actual single-block ring. Only the B2 coordinate equation is assumed. -/
theorem receivedSpineToQuotient_relative_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
      (chain2 (receivedSpineToQuotient q ρ u hrho)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)) =
      chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
        (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
          (treeMarkedSpineLoop q)
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  erw [receivedSpineToQuotient, chain2_comp_apply, bdry2_chain2]
  apply congrArg (chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)))
  apply ReceivedTree.comparison_relative_boundary
    (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineOldRootReceiver q ρ u hrho)
    (finiteSpineOldRootReceiver_compatible q ρ u hrho)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)
  intro z
  let βF : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ
        (familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u)))) := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit βF
  have hz := hz0 (by
      intro t
      with_reducible
        convert hβ t using 1
        congr
      all_goals first
        | exact Subsingleton.elim _ _
        | (funext m
           with_reducible congr 2
           all_goals first | exact Subsingleton.elim _ _ | rfl)) z
  refine hz.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x => βF (Sum.inr i) * x)
  exact (receivedSpineWordReceiver_coeff ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit (fox z (spinePresentationMarkedWord q i))).symm

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
variable {K Y : Complex2}

theorem univLift_pathChain (a : K.V) (f : Hom K Y) (v : UV K a)
    {p : List (K.E × Bool)} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 (univLift K f a) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) := by
  change Finsupp.mapDomain (univLift K f a).onE (pathChain _) = _
  erw [← pathChain_map]
  exact congrArg pathChain (uLiftPath_univLiftV a f p v b hp).symm

theorem uCoverPathTransport_pathChain {a b : K.V} {c : List (K.E × Bool)}
    (hc : IsPath K.src K.tgt c a b) (v : UV K b)
    {p : List (K.E × Bool)} {d : K.V}
    (hp : IsPath K.src K.tgt p (endV v) d) :
    chain1 (uCoverPathTransport hc) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p ((uCoverPathTransport hc).onV v)) := by
  change Finsupp.mapDomain (uCoverPathTransport hc).onE (pathChain _) = _
  erw [← pathChain_map]
  exact congrArg pathChain (uLiftPath_pathTransportV hc p v d hp).symm

theorem univDeck_pathChain (a : K.V) (g : Pi1 K a) (v : UV K a)
    {p : List (K.E × Bool)} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 ((univDeck K a).cellHom g) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p (deckV g v)) := by
  change Finsupp.mapDomain ((univDeck K a).cellHom g).onE (pathChain (uLiftPath p v)) = _
  erw [← pathChain_map ((univDeck K a).cellHom g)]
  exact congrArg pathChain (uLiftPath_deckV g p v b hp).symm

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical
variable (q : ℕ) [NeZero q]

abbrev spineOldBase := posQCube (gBase q)
abbrev spineOldCx := orderCx (QOld (cmpRel (GenusVertex q)))

def spineOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (genusSpineToOld q) (spineMarkedLoop q i).1

def surfaceOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (i.1.val, i.2))

theorem spineOldMarking_isPath (i : Fin q × Bool) :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (spineOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath (genusSpineToOld q) (spineMarkedLoop q i).2

theorem surfaceOldMarking_isPath (i : Fin q × Bool) :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (surfaceOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath (surfCx _) (isPath_gSig q (i.1.val, i.2))

theorem exists_spineOldMarkingCorrection (i : Fin q × Bool) :
    ∃ d : (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ,
      Comb.bdry2 _ d =
        pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
          pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) := by
  exact (htpy_uLiftPath
    (spineOldMarking_isPath q i) (spineMarkedLoop_toOld_htpy q i)).exists_boundary

def spineOldMarkingCorrection (i : Fin q × Bool) :
    (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ :=
  Classical.choose (exists_spineOldMarkingCorrection q i)

theorem spineOldMarkingCorrection_boundary (i : Fin q × Bool) :
    Comb.bdry2 _ (spineOldMarkingCorrection q i) =
      pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
        pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) :=
  Classical.choose_spec (exists_spineOldMarkingCorrection q i)

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def oldIntoNamedQuotient :
    Hom (spineOldCx q) (orderCx (namedQuotientPos ρ q u)) :=
  orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone

theorem oldCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u) ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) :=
  isPath_ordPos (qNew_att_le_qOldIncl (att := namedAtt ρ q u) (gBase q))

def quotientCylinderVertex :
    UV (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  UV.mk ⟨spineQuotientCylinderPath q ρ u, by
    rw (config := { transparency := .default }) [endpt_eq_of_isPath (oldCylinderPath_isPath q ρ u)]
    exact oldCylinderPath_isPath q ρ u⟩

theorem quotientCylinderVertex_end :
    endV (quotientCylinderVertex q ρ u) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) :=
  endpt_eq_of_isPath (oldCylinderPath_isPath q ρ u)

/-- Every face of this lift is an actual old face of the quotient. -/
def oldCoverToNamedQuotient :
    Hom (uCover (spineOldCx q) (spineOldBase q))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (oldCylinderPath_isPath q ρ u)).comp
    (univLift (spineOldCx q) (oldIntoNamedQuotient q ρ u) (spineOldBase q))

theorem oldCoverToNamedQuotient_pathChain
    {p : List ((spineOldCx q).E × Bool)} (b : (spineOldCx q).V)
    (hp : IsPath (spineOldCx q).src (spineOldCx q).tgt p (spineOldBase q) b) :
    chain1 (oldCoverToNamedQuotient q ρ u)
      (pathChain (uLiftPath p (UV.base (spineOldCx q) (spineOldBase q)))) =
      pathChain (uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) p)
        (quotientCylinderVertex q ρ u)) := by
  erw [oldCoverToNamedQuotient, chain1_comp_apply, univLift_pathChain _ _ _ hp]
  erw [uCoverPathTransport_pathChain _ _ (isPath_mapPath (oldIntoNamedQuotient q ρ u) hp)]
  congr 2

theorem receivedSpineToQuotient_root
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    (receivedSpineToQuotient q ρ u hrho).onV (g, (markedSpineTree q).root) =
      deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u) := by
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (deckV (finiteSpineOldRootReceiver q ρ u hrho g)
      (SpanningTree.mappedTreeReference (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root)) = _
  simp only [SpanningTree.mappedTreeReference, SpanningTree.treePath_root,
    mapPath, List.map_nil, extendList_nil]
  erw [uCoverPathTransport_deckV, uCoverPathTransport_base]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
      (finiteSpineToQuotient ρ q u hrho g))) (quotientCylinderVertex q ρ u) = _
  rw (config := { transparency := .default }) [pi1Conj_cancel_reverse]

def quotientMarkingCorrection
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains
    (finiteSpineToQuotient ρ q u hrho g)
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

/-- The correction is lifted in the old subcomplex before translation;
its boundary changes exactly the two chosen marking paths. -/
theorem quotientMarkingCorrection_boundary
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    Comb.bdry2 _ (quotientMarkingCorrection q ρ u hrho g i) =
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) -
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) := by
  erw [quotientMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  erw [oldCoverToNamedQuotient_pathChain q ρ u _ (spineOldMarking_isPath q i),
    oldCoverToNamedQuotient_pathChain q ρ u _ (surfaceOldMarking_isPath q i)]
  have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    erw [quotientCylinderVertex_end]
    exact isPath_mapPath _ (spineOldMarking_isPath q i)
  have hs : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    erw [quotientCylinderVertex_end]
    exact isPath_mapPath _ (surfaceOldMarking_isPath q i)
  erw [univDeck_pathChain _ _ _ hp, univDeck_pathChain _ _ _ hs]

def quotientMarkingCorrections :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => quotientMarkingCorrection q ρ u hrho x.1 x.2)

def quotientSpineMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

def quotientSurfaceMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

theorem quotientMarkingCorrections_boundary
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    Comb.bdry2 _ (quotientMarkingCorrections q ρ u hrho c) =
      quotientSpineMarkingChains q ρ u hrho c - quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      erw [map_add, map_add, hc, hd, map_add, map_add]
      abel
  | single x n =>
      simp only [quotientMarkingCorrections, quotientSpineMarkingChains,
        quotientSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul,
        quotientMarkingCorrection_boundary, smul_sub]


/-- The abstractly indexed marked chain map agrees exactly with the actual
translated lifted marking paths at the cylinder endpoint. -/
theorem quotientSpineMarkingChains_eq
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
      (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
        (treeMarkedSpineLoop q) c) = quotientSpineMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      obtain ⟨g, i⟩ := x
      erw [ReceivedTree.geometricMarkedChainMap, Finsupp.linearCombination_single,
        map_smul, quotientSpineMarkingChains, Finsupp.linearCombination_single]
      apply congrArg (fun z => n • z)
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1)
          (endV (ReceivedTree.receiverVertex (markedSpineTree q)
            (markedSpineToNamedQuotient q ρ u)
            (finiteSpineOldRootReceiver q ρ u hrho) g (markedSpineTree q).root))
          ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
        erw [ReceivedTree.receiverVertex_end]
        exact isPath_mapPath _ (treeMarkedSpineLoop q i).2
      erw [uCoverPathTransport_pathChain _ _ hp, (show mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1 =
      mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i) by
        erw [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
        rfl)]
      erw [receivedSpineToQuotient_root]

def quotientCorrectedRelativeChain
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  chain2 (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) -
      quotientMarkingCorrections q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))

/-- Starting with the actual B2 coordinate equation now gives an actual
old two-chain whose boundary lies on the attaching surface with exactly the
original marked coefficients. No absolute-cycle assumption is added. -/
theorem quotientCorrectedRelativeChain_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 _ (quotientCorrectedRelativeChain q ρ u hrho β) =
      quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  erw [quotientCorrectedRelativeChain, map_sub,
    receivedSpineToQuotient_relative_boundary q ρ u hrho β hβ,
    quotientSpineMarkingChains_eq, quotientMarkingCorrections_boundary]
  abel

end FiniteChains.Davis.Genus
end

namespace FiniteChains.TopologicalSingular


/-- The finite-support simplex and the barycentric-coordinate simplex have the same topology. -/
def simplexCoordinates (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext x
      simp [stdSimplex]))

@[simp] theorem simplexCoordinates_apply (n : ℕ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (simplexCoordinates n z).val = z.weights := rfl

/-- Barycentric coordinates commute with maps of vertex sets. -/
theorem simplexCoordinates_map {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexCoordinates m (Convexity.StdSimplex.map f z) =
      stdSimplex.map f (simplexCoordinates n z) := by
  apply Subtype.ext
  funext i
  change (Finsupp.mapDomain f z.weights) i = (FunOnFinite.linearMap ℝ ℝ f z.weights) i
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype, Finsupp.single_apply, Finset.sum_filter, eq_comm]

@[simp] theorem simplexCoordinates_symm_weights_apply (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ((simplexCoordinates n).symm z).weights i = z.val i := by
  exact congrArg (fun w : stdSimplex ℝ (Fin (n + 1)) => w.val i)
    ((simplexCoordinates n).apply_symm_apply z)

end FiniteChains.TopologicalSingular

namespace Whitehead
open scoped unitInterval Topology

/-- Covering maps reflect based homotopies of two-dimensional loops. -/

theorem mapSquare_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (mapSquare f p) (mapSquare f q) :=
  h.comp_continuousMap f

@[simp] theorem mapSquare_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapSquare f (GenLoop.const (x := x)) = GenLoop.const := rfl

/-- The continuous map induced on Mathlib's topological second homotopy quotient. -/
def pi2Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyGroup (Fin 2) X x → HomotopyGroup (Fin 2) Y (f x) :=
  Quotient.map (mapSquare f) (fun _ _ h => mapSquare_homotopic f h)

/-- Radial contraction of the square, used to construct covering lifts directly. -/
def radialSquare : C(I × (Fin 2 → I), Fin 2 → I) where
  toFun ta i := ta.1 * ta.2 i
  continuous_toFun := continuous_pi (fun i =>
    (continuous_fst.subtype_val.mul
      (((continuous_apply i).comp continuous_snd).subtype_val)).subtype_mk _)

/-- A based square lifts through a covering map, including its constant boundary. -/

theorem mapSquare_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) (g : C(X, Y)) {x : X}
    (a : GenLoop (Fin 2) X x) :
    mapSquare (f.comp g) a = mapSquare f (mapSquare g a) := rfl

/-- The square-map formulation in the challenge is exactly the zero-map condition on
Mathlib's topological homotopy group, not an auxiliary algebraic substitute. -/
theorem killsPi2_iff {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : KillsPi2 f ↔ ∀ x z, pi2Map f x z = 1 := by
  constructor
  · intro h x z
    induction z using Quotient.inductionOn with
    | _ p => exact Quotient.sound (h x p)
  · intro h x p
    exact Quotient.exact (h x (Quotient.mk _ p))

/-- Postcomposing with a covering reflects the zero-map condition on `π₂`. -/
theorem killsPi2_covering_postcomp_iff {Y E X : Type}
    [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
    (f : C(Y, E)) (p : C(E, X)) (hp : IsCoveringMap p) :
    KillsPi2 (p.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h y a
    apply (show GenLoop.Homotopic (mapSquare p (mapSquare f a)) (mapSquare p (GenLoop.const)) ↔ GenLoop.Homotopic (mapSquare f a) (GenLoop.const) by
      exact (hp.homotopicRel_iff_comp (f₀ := (mapSquare f a).1) (S := Cube.boundary (Fin 2))
        ⟨fun _ => 0, ⟨0, Or.inl rfl⟩,
          (GenLoop.boundary (mapSquare f a) _ ⟨0, Or.inl rfl⟩).trans (GenLoop.boundary (GenLoop.const) _ ⟨0, Or.inl rfl⟩).symm⟩).symm).mp
    have := h y a
    simp only [ContinuousMap.comp_apply, mapSquare_comp] at this
    simpa using this
  · intro h y a
    have he := mapSquare_homotopic p (h y a)
    simp only [← mapSquare_comp, ← ContinuousMap.comp_apply] at he
    simpa using he

/-- Surjective coverings also reflect the zero-map condition when precomposed. -/
theorem killsPi2_covering_precomp_iff {E X Y : Type}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(E, X)) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (f : C(X, Y)) : KillsPi2 (f.comp p) ↔ KillsPi2 f := by
  constructor
  · intro h x q
    obtain ⟨e, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := (show ∃ a : GenLoop (Fin 2) E e, mapSquare p a = q by
      let z : Fin 2 → I := fun _ => 0
      have hz : z ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
      let H  := q.1.comp radialSquare
      have H0 : ∀ t, H (0, t) = p e := by
        intro t
        change q (fun i => 0 * t i) = p e
        simpa using GenLoop.boundary q z hz
      let F := hp.liftHomotopy H (ContinuousMap.const _ e) H0
      let G  := F.comp ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩
      have hG : ∀ t, p (G t) = q t := by
        intro t
        have he := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (1, t)
        change p (F (1, t)) = q (fun i => 1 * t i) at he
        simp only [one_mul] at he
        exact he

      have hbase : G z = e := by
        have he := hp.const_of_comp
          (F.continuous.comp (continuous_id.prodMk continuous_const))
          (fun t s => by
            have ht := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (t, z)
            have hs := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (s, z)
            change p (F (t, z)) = q (fun i => t * z i) at ht
            change p (F (s, z)) = q (fun i => s * z i) at hs
            simp only [z, mul_zero] at ht hs
            exact ht.trans hs.symm) 1 0
        exact he.trans (hp.liftHomotopy_zero H (ContinuousMap.const _ e) H0 z)
      have hboundary : ∀ t ∈ Cube.boundary (Fin 2), G t = e := by
        intro t ht
        have he := hp.constOn_of_comp square_boundary_isPreconnected G.continuous.continuousOn
          (fun a ha b hb => (hG a).trans
            ((GenLoop.boundary q a ha).trans ((GenLoop.boundary q b hb).symm.trans (hG b).symm)))
          ht hz
        exact he.trans hbase
      refine ⟨⟨G, hboundary⟩, ?_⟩
      apply GenLoop.ext
      exact hG)
    have he := h e a
    change GenLoop.Homotopic (mapSquare f (mapSquare p a)) GenLoop.const at he
    rwa [ha] at he
  · intro h e a
    exact h (p e) (mapSquare p a)

end Whitehead

namespace Whitehead
open scoped unitInterval Topology

abbrev Square := Fin 2 → I

def squareOrigin : Square := fun _ => 0


/-- Distance from the nearest face of the square, in its standard coordinates. -/
def squareDepth (z : Square) : ℝ :=
  min (min (z 0 : ℝ) (1 - z 0)) (min (z 1 : ℝ) (1 - z 1))

theorem squareDepth_nonneg (z : Square) : 0 ≤ squareDepth z := by
  exact le_min (le_min (z 0).2.1 (sub_nonneg.mpr (z 0).2.2))
    (le_min (z 1).2.1 (sub_nonneg.mpr (z 1).2.2))



theorem squareDepth_boundary (z : Square) (hz : z ∈ Cube.boundary (Fin 2)) :
    squareDepth z = 0 := by
  apply le_antisymm _ (squareDepth_nonneg z)
  obtain ⟨i, hi | hi⟩ := hz
  · simpa only [hi, Set.Icc.coe_zero] using (show squareDepth z ≤ (z i : ℝ) by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _))
  · simpa only [hi, Set.Icc.coe_one, sub_self] using (show squareDepth z ≤ 1 - (z i) by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _))


theorem squareDepth_continuous : Continuous squareDepth := by
  unfold squareDepth
  fun_prop

theorem squareCollarDenom_pos (s : I) : 0 < 1 - (s : ℝ) / 2 := by grind

/-- The inner square expands to the whole square; points in the collar hit its boundary. -/
def squareCollarExpand (s : I) (z : Square) : Square := fun i =>
  Set.projIcc 0 1 zero_le_one (((z i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2))



theorem squareCollarExpand_boundary (s : I) (z : Square)
    (hz : squareDepth z ≤ (s : ℝ) / 4) :
    squareCollarExpand s z ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi | hi⟩ := (show ∃ i : Fin 2, squareDepth z = (z i) ∨ squareDepth z = 1 - (z i) by
    have hmin (a b : ℝ) : min a b = a ∨ min a b = b := by
      rcases le_total a b with h | h
      · simp_all
      · simp_all
    rcases hmin (min (z 0) (1 - z 0)) (min (z 1) (1 - z 1)) with h | h
    · exact ⟨0, (hmin (z 0) (1 - z 0)).imp (h.trans ·) (h.trans ·)⟩
    · exact ⟨1, (hmin (z 1) (1 - z 1)).imp (h.trans ·) (h.trans ·)⟩)
  · refine ⟨i, Or.inl ?_⟩
    apply projIcc_eq_zero.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact (squareCollarDenom_pos s).le
  · refine ⟨i, Or.inr ?_⟩
    apply projIcc_eq_one.mpr
    apply (le_div_iff₀ (squareCollarDenom_pos s)).mpr
    linarith

/-- Time stops at the collar, whose boundary is always at time zero. -/
def squareCollarTime (s : I) (z : Square) : I :=
  ⟨min (s : ℝ) (4 * squareDepth z),
    le_min s.2.1 (mul_nonneg (by norm_num) (squareDepth_nonneg z)),
    (min_le_left _ _).trans s.2.2⟩

theorem squareCollarTime_continuous :
    Continuous (fun sz : I × Square => squareCollarTime sz.1 sz.2) :=
  (continuous_fst.subtype_val.min
    (continuous_const.mul (squareDepth_continuous.comp continuous_snd))).subtype_mk _


theorem squareCollarTime_boundary (s : I) (z : Square)
    (hz : z ∈ Cube.boundary (Fin 2)) : squareCollarTime s z = 0 := by
  apply Subtype.ext
  simp only [squareCollarTime, squareDepth_boundary z hz, mul_zero]
  exact min_eq_right s.2.1

/-- Constant boundary values are allowed to depend on homotopy time. -/
def SquareConstantBoundary {X : Type*} [TopologicalSpace X] (f : C((Fin 2 → I), X)) : Prop :=
  ∀ z ∈ Cube.boundary (Fin 2), f z = f (fun _ => 0)

/-- A null homotopy with moving but constant boundary gives a based null homotopy.
The first stage inserts a collar. The second contracts the resulting radial path. -/
theorem genLoop_null_of_movingBoundary {X : Type*} [TopologicalSpace X] {x y : X}
    (p : GenLoop (Fin 2) X x)
    (H : ContinuousMap.HomotopyWith p.val (ContinuousMap.const _ y) SquareConstantBoundary) :
    GenLoop.Homotopic p GenLoop.const := by
  let z₀ := squareOrigin
  have hz₀ : z₀ ∈ Cube.boundary (Fin 2) := (⟨0, Or.inl rfl⟩)
  let h  := H.toContinuousMap.comp
    ⟨fun t => (t, z₀), continuous_id.prodMk continuous_const⟩
  have hzero : h 0 = x := (H.apply_zero z₀).trans (GenLoop.boundary p z₀ hz₀)
  let r : C((Fin 2 → I), I) :=
    ⟨squareCollarTime 1, squareCollarTime_continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  let q : GenLoop (Fin 2) X x := ⟨h.comp r, fun z hz => by
    change h (squareCollarTime 1 z) = x
    rw [squareCollarTime_boundary 1 z hz]
    exact hzero⟩
  have hfirst : GenLoop.Homotopic p q := by
    refine ⟨{
      toFun := fun sz => H (squareCollarTime sz.1 sz.2,
        squareCollarExpand sz.1 sz.2)
      continuous_toFun := H.continuous.comp
        (squareCollarTime_continuous.prodMk (by
          apply continuous_pi
          intro i
          apply continuous_projIcc.comp
          exact ((((continuous_apply i).comp continuous_snd).subtype_val.sub
            (continuous_fst.subtype_val.div_const 4)).div
            (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
            (fun sz => ne_of_gt (squareCollarDenom_pos sz.1)))))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro z
      rw [(show squareCollarTime 0 z = 0 by
        ext
        exact min_eq_left (mul_nonneg (by norm_num) (squareDepth_nonneg z))), (show squareCollarExpand 0 z = z by
          funext i
          simpa only [squareCollarExpand, Set.Icc.coe_zero, zero_div, sub_zero,
            div_one] using Set.projIcc_val zero_le_one (z i))]
      exact H.apply_zero z
    · intro z
      change H (squareCollarTime 1 z, squareCollarExpand 1 z) =
        H (squareCollarTime 1 z, z₀)
      by_cases hd : 1 ≤ 4 * squareDepth z
      · have ht : squareCollarTime 1 z = 1 := Subtype.ext (min_eq_left hd)
        rw [ht, H.apply_one, H.apply_one]
        rfl
      · apply H.prop
        apply squareCollarExpand_boundary
        have hlt := lt_of_not_ge hd
        change squareDepth z ≤ 1 / 4
        linarith
    · intro s z hz
      change H (squareCollarTime s z, squareCollarExpand s z) = p z
      rw [squareCollarTime_boundary s z hz, H.apply_zero, GenLoop.boundary p z hz]
      exact GenLoop.boundary p _ (squareCollarExpand_boundary s z (by
        rw [squareDepth_boundary z hz]
        exact div_nonneg s.2.1 (by norm_num)))
  have hsecond : GenLoop.Homotopic q GenLoop.const := by
    refine ⟨{
      toFun := fun sz => h (unitInterval.symm sz.1 * r sz.2)
      continuous_toFun := h.continuous.comp (by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp
          (unitInterval.continuous_symm.comp continuous_fst)).mul
            (continuous_subtype_val.comp (r.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro z
      change h (unitInterval.symm 0 * r z) = h (r z)
      simp
    · simp_all
    · intro s z hz
      change h (unitInterval.symm s * squareCollarTime 1 z) = h (squareCollarTime 1 z)
      rw [squareCollarTime_boundary 1 z hz, mul_zero]
  exact hfirst.trans hsecond

end Whitehead

namespace Whitehead
open scoped unitInterval Topology

variable {X Y Z : Type}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem killsPi2_precompose (f : C(X, Y)) (g : C(Y, Z)) (hg : KillsPi2 g) :
    KillsPi2 (g.comp f) := by
  intro x p
  exact hg (f x) (mapSquare f p)

theorem killsPi2_postcompose (f : C(X, Y)) (g : C(Y, Z)) (hf : KillsPi2 f) :
    KillsPi2 (g.comp f) := by
  intro x p
  have h := mapSquare_homotopic g (hf x p)
  simpa only [mapSquare_const, ← mapSquare_comp] using h

/-- An ordinary homotopy preserves the vanishing of the induced second homotopy map. -/
theorem killsPi2_of_homotopic {f g : C(X, Y)} (hfg : f.Homotopic g)
    (hg : KillsPi2 g) : KillsPi2 f := by
  obtain ⟨H⟩ := hfg
  intro x p
  obtain ⟨G⟩ := hg x p
  have hz₀ : (fun _ : Fin 2 => 0) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let F : ContinuousMap.HomotopyWith (mapSquare f p).val (mapSquare g p).val
      SquareConstantBoundary := {
    toHomotopy := H.compContinuousMap p.val
    prop' := by
      intro t z hz
      change H (t, p z) = H (t, p (fun _ => 0))
      rw [GenLoop.boundary p z hz, GenLoop.boundary p _ hz₀] }
  let G' : ContinuousMap.HomotopyWith (mapSquare g p).val
      (ContinuousMap.const _ (g x)) SquareConstantBoundary := {
    toHomotopy := G.toHomotopy
    prop' := by
      intro t z hz
      change G (t, z) = G (t, fun _ => 0)
      rw [G.eq_fst t hz, G.eq_fst t hz₀]
      exact (GenLoop.boundary (mapSquare g p) z hz).trans
        (GenLoop.boundary (mapSquare g p) _ hz₀).symm }
  exact genLoop_null_of_movingBoundary (mapSquare f p) (F.trans G')

theorem killsPi2_homotopic_iff {f g : C(X, Y)} (hfg : f.Homotopic g) :
    KillsPi2 f ↔ KillsPi2 g :=
  ⟨killsPi2_of_homotopic hfg.symm, killsPi2_of_homotopic hfg⟩

/-- A homotopy equivalence in the target reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_postcomp_iff (e : ContinuousMap.HomotopyEquiv Y Z)
    (f : C(X, Y)) : KillsPi2 (e.toFun.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_postcompose (e.toFun.comp f) e.invFun h
    have hh : ((e.invFun.comp e.toFun).comp f).Homotopic f := by
      simpa using e.left_inv.comp (ContinuousMap.Homotopic.refl f)
    exact (killsPi2_homotopic_iff hh).mp hk
  · exact killsPi2_postcompose f e.toFun

/-- A homotopy equivalence in the source reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_precomp_iff (e : ContinuousMap.HomotopyEquiv X Y)
    (f : C(Y, Z)) : KillsPi2 (f.comp e.toFun) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_precompose e.invFun (f.comp e.toFun) h
    have hh : (f.comp (e.toFun.comp e.invFun)).Homotopic f := by
      simpa using (ContinuousMap.Homotopic.refl f).comp e.right_inv
    exact (killsPi2_homotopic_iff hh).mp hk
  · exact killsPi2_precompose e.toFun f

/-- The zero condition is transported across a homotopy-commutative square whose
vertical maps are genuine homotopy equivalences. -/
theorem killsPi2_homotopyEquiv_square_iff {X' Y' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y']
    (e : ContinuousMap.HomotopyEquiv X X') (d : ContinuousMap.HomotopyEquiv Y Y')
    (f : C(X, Y)) (g : C(X', Y'))
    (h : (g.comp e.toFun).Homotopic (d.toFun.comp f)) :
    KillsPi2 g ↔ KillsPi2 f := by grind [killsPi2_homotopyEquiv_precomp_iff, killsPi2_homotopic_iff, killsPi2_homotopyEquiv_postcomp_iff]

end Whitehead

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D X : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace X]

/-- The ordinary homotopy extension property, retaining both equations as
equalities of actual continuous maps. -/
def HasHomotopyExtension (i : A → D) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] (f : C(D, Z)) (H : C(I × A, Z)),
    (∀ a, H (0, a) = f (i a)) →
    ∃ G : C(I × D, Z), (∀ d, G (0, d) = f d) ∧
      ∀ t a, G (t, i a) = H (t, a)

theorem HasHomotopyExtension.homeomorph {A' D' : Type u}
    [TopologicalSpace A'] [TopologicalSpace D'] {i : A → D}
    (h : HasHomotopyExtension i) (e : A ≃ₜ A') (d : D ≃ₜ D')
    (j : A' → D') (hsq : ∀ a, j (e a) = d (i a)) : HasHomotopyExtension j := by
  intro Z _ f H h₀
  let f'  := f.comp d.toContinuousMap
  let H' : C(I × A, Z) := H.comp
    ⟨fun ta => (ta.1, e ta.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  have h'₀ : ∀ a, H' (0, a) = f' (i a) := by
    intro a
    change H (0, e a) = f (d (i a))
    rw [h₀, hsq]
  obtain ⟨G, hG₀, hGA⟩ := h Z f' H' h'₀
  refine ⟨G.comp ⟨fun td => (td.1, d.symm td.2),
    continuous_fst.prodMk (d.symm.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro z
    change G (0, d.symm z) = f z
    rw [hG₀]
    exact congrArg f (d.apply_symm_apply z)
  · intro t a
    have hs : d.symm (j a) = i (e.symm a) := by
      apply d.injective
      rw [d.apply_symm_apply, ← hsq, e.apply_symm_apply]
    change G (t, d.symm (j a)) = H (t, a)
    rw [hs, hGA]
    exact congrArg (fun b => H (t, b)) (e.apply_symm_apply a)

/-- The boundary of a real normed unit ball has homotopy extension by the
explicit radial cylinder retraction. -/
theorem unitBoundary_hasHomotopyExtension (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HasHomotopyExtension (unitBoundaryInclusion E) := by
  intro Z _ f H h₀
  exact ⟨ballHomotopyExtension f H h₀,
    ballHomotopyExtension_zero f H h₀, ballHomotopyExtension_boundary f H h₀⟩

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev FullBallCylinderBoundary :=
  {z : I × ClosedUnitBall E // z.1 = 0 ∨ z.1 = 1 ∨ ‖z.2.val‖ = 1}

def ballCylinderForward (z : ClosedUnitBall (ℝ × E)) : I × ClosedUnitBall E :=
  (⟨(z.val.1 + 1) / 2, by
    have h : |z.val.1| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (norm_fst_le z.val).trans z.property
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> linarith⟩,
   ⟨z.val.2, (norm_snd_le z.val).trans z.property⟩)

def ballCylinderInverse (z : I × ClosedUnitBall E) : ClosedUnitBall (ℝ × E) :=
  ⟨(2 * (z.1 : ℝ) - 1, z.2.val), by
    rw [Prod.norm_mk, Real.norm_eq_abs]
    apply max_le _ z.2.property
    rw [abs_le]
    have hl := z.1.2.1
    have hu := z.1.2.2
    constructor <;> linarith⟩

/-- The cylinder is literally a ball in the product norm, after rescaling
its interval coordinate from `[-1,1]` to `[0,1]`. -/
def ballCylinderHomeomorph : ClosedUnitBall (ℝ × E) ≃ₜ I × ClosedUnitBall E where
  toFun := ballCylinderForward E
  invFun := ballCylinderInverse E
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * (z.1 : ℝ) - 1) + 1) / 2 = (z.1 : ℝ)
      ring
    · rfl
  continuous_toFun := by
    unfold ballCylinderForward
    fun_prop
  continuous_invFun := by
    unfold ballCylinderInverse
    fun_prop



/-- The sphere for the product norm is exactly the union of the two ends
and the side boundary of the disk cylinder. -/
def ballCylinderBoundaryHomeomorph : UnitBoundary (ℝ × E) ≃ₜ FullBallCylinderBoundary E where
  toFun z := ⟨ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z),
    (show (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 0 ∨
    (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 1 ∨
    ‖(ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).2.val‖ = 1 by
      have he : max |z.val.1| ‖z.val.2‖ = 1 := by
        have hz := z.property
        rw [Prod.norm_mk, Real.norm_eq_abs] at hz
        exact hz
      by_cases hs : ‖z.val.2‖ = 1
      · exact Or.inr (Or.inr hs)
      have hf : |z.val.1| = 1 := by
        by_cases hle : |z.val.1| ≤ ‖z.val.2‖
        · simp_all
        · grind
      by_cases hz : 0 ≤ z.val.1
      · right
        left
        apply Subtype.ext
        change (z.val.1 + 1) / 2 = (1 : ℝ)
        rw [abs_of_nonneg hz] at hf
        linarith
      · left
        apply Subtype.ext
        change (z.val.1 + 1) / 2 = (0 : ℝ)
        rw [abs_of_nonpos (le_of_not_ge hz)] at hf
        linarith)⟩
  invFun z := ⟨((ballCylinderHomeomorph E).symm z.val).val,
    (show ‖((ballCylinderHomeomorph E).symm z.val).val‖ = 1 by
      apply le_antisymm ((ballCylinderHomeomorph E).symm z.val).property
      change 1 ≤ max ‖2 * (z.val.1 : ℝ) - 1‖ ‖z.val.2.val‖
      rcases z.property with hz | hz | hz
      · simp_all
      · have ht : ‖2 * (z.val.1 : ℝ) - 1‖ = 1 := by norm_num [hz]
        rw [ht]
        exact le_max_left _ _
      · simp_all)⟩
  left_inv z := by
    apply Subtype.ext
    exact congrArg (fun w : ClosedUnitBall (ℝ × E) => w.val)
      ((ballCylinderHomeomorph E).symm_apply_apply
      (unitBoundaryInclusion (ℝ × E) z))
  right_inv z := by
    apply Subtype.ext
    exact (ballCylinderHomeomorph E).apply_symm_apply z.val
  continuous_toFun :=
    ((ballCylinderHomeomorph E).continuous.comp
      (unitBoundaryInclusion (ℝ × E)).continuous).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      ((ballCylinderHomeomorph E).symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- Relative homotopy extension that also keeps both endpoint disk maps
fixed. This is the geometric input for cancelling a boundary backtrack. -/
theorem fullBallCylinderBoundary_hasHomotopyExtension :
    HasHomotopyExtension (Subtype.val : FullBallCylinderBoundary E → I × ClosedUnitBall E) :=
  (unitBoundary_hasHomotopyExtension (ℝ × E)).homeomorph
    (ballCylinderBoundaryHomeomorph E) (ballCylinderHomeomorph E) Subtype.val
    (fun _ => rfl)

end FiniteChains.RelativeAttachment

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

/-- Actual path classes, with the lifted comparability order rather than any extra data. -/
def UOrder (a : P) := UV (orderCx P) a

variable {P} {a : P}

def uOrderEnd (v : UOrder P a) : P := endV v

def uOrderStep (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    UOrder P a := extend (ordPos h) v

theorem uOrderStep_end (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    uOrderEnd (uOrderStep v q h) = q := endV_extend rfl

theorem uOrderStep_refl (v : UOrder P a) :
    uOrderStep v (uOrderEnd v) (le_refl _) = v := by
  have h := extendList_htpy
    (isPath_ordPos (le_refl (uOrderEnd v))) (htpy_ordSelf_nil (uOrderEnd v))
  simpa only [extendList_cons, extendList_nil, uOrderStep] using h

/-- Triangle homotopy makes successive lifted comparabilities compose. -/
theorem uOrderStep_comp (v : UOrder P a) {q r : P} (h : uOrderEnd v ≤ q) (hqr : q ≤ r) :
    uOrderStep (uOrderStep v q h) r ((uOrderStep_end v q h).le.trans hqr) =
      uOrderStep v r (h.trans hqr) := by
  have ht := extendList_htpy
    ((isPath_ordPos h).append (isPath_ordPos hqr))
    (htpy_orderCx_tri h hqr)
  have hg : ordPos ((uOrderStep_end v q h).le.trans hqr) = ordPos hqr := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (uOrderStep_end v q h) rfl
    · rfl
  change extend (ordPos ((uOrderStep_end v q h).le.trans hqr))
    (extend (ordPos h) v) = extend (ordPos (h.trans hqr)) v
  simp_all

def UOrderLe (v w : UOrder P a) : Prop :=
  ∃ h : uOrderEnd v ≤ uOrderEnd w, uOrderStep v (uOrderEnd w) h = w

theorem uOrderStep_eq_of_end_eq (v : UOrder P a) (q : P)
    (h : uOrderEnd v ≤ q) (hq : q = uOrderEnd v) : uOrderStep v q h = v := by
  subst q
  exact uOrderStep_refl v

instance uOrderPartialOrder : PartialOrder (UOrder P a) where
  le := UOrderLe
  le_refl v := ⟨le_refl _, uOrderStep_refl v⟩
  le_trans v w z hvw hwz := by
    obtain ⟨hvw, hew⟩ := hvw
    obtain ⟨hwz, hez⟩ := hwz
    refine ⟨hvw.trans hwz, ?_⟩
    have hc := uOrderStep_comp v hvw hwz
    simp only [hew] at hc
    exact hc.symm.trans hez
  le_antisymm v w hvw hwv := by
    obtain ⟨hvw, hew⟩ := hvw
    obtain ⟨hwv, _⟩ := hwv
    have h : uOrderEnd v = uOrderEnd w := le_antisymm hvw hwv
    have he : uOrderStep v (uOrderEnd w) hvw = v :=
      uOrderStep_eq_of_end_eq v _ hvw h.symm
    exact he.symm.trans hew

theorem uOrderEnd_monotone : Monotone (uOrderEnd (P := P) (a := a)) :=
  fun _ _ h => h.1

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem uOrderStep_le (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    v ≤ uOrderStep v q h := by
  change UOrderLe _ _
  unfold UOrderLe
  simp only [uOrderStep_end]
  exact ⟨h, trivial⟩


theorem uOrder_unique_up (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    ∃! w : UOrder P a, v ≤ w ∧ uOrderEnd w = q := by
  refine ⟨uOrderStep v q h, ⟨uOrderStep_le v q h, uOrderStep_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  simp_all

def uOrderBack (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    UOrder P a := extend (ordNeg h) v

theorem uOrderBack_end (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    uOrderEnd (uOrderBack v q h) = q := endV_extend rfl


theorem uOrder_unique_down (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    ∃! w : UOrder P a, w ≤ v ∧ uOrderEnd w = q := by
  refine ⟨uOrderBack v q h, ⟨(by
    let hb  :=
      (uOrderBack_end v q h).le.trans h
    refine ⟨hb, ?_⟩
    have hg : ordPos hb = revGerm (ordNeg h) := by
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext (uOrderBack_end v q h) rfl
      · rfl
    change extend (ordPos hb) (extend (ordNeg h) v) = v
    rw [hg]
    exact extend_revGerm rfl), uOrderBack_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  have hg : ordNeg hle = ordNeg h := by
    apply Prod.ext
    · simp_all
    · rfl
  have hr : extend (ordNeg h) (extend (ordPos hle) w) = w := by
    rw [← hg]
    exact extend_revGerm (eb := ordPos hle) rfl
  have ht := congrArg (extend (ordNeg h)) he
  exact hr.symm.trans ht

/-- The endpoint map of actual path classes is a poset covering whenever the base
order complex is connected. -/
theorem uOrderEnd_isPosetCover (hc : IsConnected (orderCx P)) :
    IsPosetCover (uOrderEnd (P := P) (a := a)) where
  mono := uOrderEnd_monotone
  surj := endV_surjective hc
  up := uOrder_unique_up
  down := uOrder_unique_down

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderEdge (e : OrdEdge (UOrder P a)) : UE (orderCx P) a :=
  ⟨(e.1.1, ⟨(uOrderEnd e.1.1, uOrderEnd e.1.2), uOrderEnd_monotone e.2⟩), rfl⟩

def uOrderFace (t : OrdTri (UOrder P a)) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1, uOrderEnd t.1.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2⟩), rfl⟩

theorem uOrder_up_injective {v w z : UOrder P a} (hw : v ≤ w) (hz : v ≤ z)
    (he : uOrderEnd w = uOrderEnd z) : w = z := by
  obtain ⟨hvw, ew⟩ := hw
  obtain ⟨hvz, ez⟩ := hz
  simp_all

theorem uOrderEdge_injective : Function.Injective (uOrderEdge (P := P) (a := a)) := by
  intro e f h
  have hroot  := congrArg (fun g : UE (orderCx P) a => g.1.1) h
  have hend  :=
    congrArg (fun g : UE (orderCx P) a => g.1.2.1.2) h
  have ht  := uOrder_up_injective e.2 (hroot ▸ f.2) hend
  exact Subtype.ext (Prod.ext hroot ht)

theorem uOrderFace_injective : Function.Injective (uOrderFace (P := P) (a := a)) := by
  intro t s h
  have hroot  := congrArg (fun g : UF (orderCx P) a => g.1.1) h
  have hmid  :=
    congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.1) h
  have htop  :=
    congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.2) h
  have hm  := uOrder_up_injective t.2.1 (hroot ▸ s.2.1) hmid
  have ht  :=
    uOrder_up_injective (t.2.1.trans t.2.2) (hroot ▸ s.2.1.trans s.2.2) htop
  exact Subtype.ext (Prod.ext hroot (Prod.ext hm ht))

theorem uOrderEdge_surjective : Function.Surjective (uOrderEdge (P := P) (a := a)) := by
  rintro ⟨⟨v, e⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = e.1.1 := hv
  let h  := hv'.le.trans e.2
  let w := uOrderStep (v : UOrder P a) e.1.2 h
  refine ⟨⟨(v, w), uOrderStep_le v _ h⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl
    (Subtype.ext (Prod.ext hv (uOrderStep_end v _ h))))

theorem uOrderFace_surjective : Function.Surjective (uOrderFace (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = t.1.1 := hv
  let h  := hv'.le.trans t.2.1
  let w := uOrderStep (v : UOrder P a) t.1.2.1 h
  let h'  := (uOrderStep_end v _ h).le.trans t.2.2
  let z := uOrderStep w t.1.2.2 h'
  refine ⟨⟨(v, w, z), uOrderStep_le v _ h, uOrderStep_le w _ h'⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext hv (Prod.ext (uOrderStep_end v _ h) (uOrderStep_end w _ h')))))

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem uOrderEdge_target (e : OrdEdge (UOrder P a)) :
    uTgt (uOrderEdge e) = e.1.2 := e.2.2

theorem uOrderFace_att (t : OrdTri (UOrder P a)) :
    uAtt (uOrderFace t) = ((orderCx (UOrder P a)).att t).map
      (fun eb => (uOrderEdge eb.1, eb.2)) := by
  obtain ⟨⟨v, w, z⟩, hvw, hwz⟩ := t
  have hvw' : extend (ordPos (uOrderEnd_monotone hvw)) v = w := hvw.2
  have hwz' : extend (ordPos (uOrderEnd_monotone hwz)) w = z := hwz.2
  have hvz' : extend (ordPos (uOrderEnd_monotone (hvw.trans hwz))) v = z :=
    (hvw.trans hwz).2
  have hback : extend (ordNeg (uOrderEnd_monotone (hvw.trans hwz))) z = v := by
    have h := extend_revGerm
      (eb := ordPos (uOrderEnd_monotone (hvw.trans hwz))) rfl
    rwa [hvz'] at h
  change uLiftPath [ordPos (uOrderEnd_monotone hvw), ordPos (uOrderEnd_monotone hwz),
    ordNeg (uOrderEnd_monotone (hvw.trans hwz))] v =
      [(uOrderEdge ⟨(v, w), hvw⟩, true), (uOrderEdge ⟨(w, z), hwz⟩, true),
        (uOrderEdge ⟨(v, z), hvw.trans hwz⟩, false)]
  rw [uLiftPath_cons rfl, hvw', uLiftPath_cons rfl, hwz', uLiftPath_cons rfl,
    uLiftPath_nil]
  simp only [ordPos, ordNeg, liftGerm_true, liftGerm_false]
  congr 1
  congr 1
  congr 1
  congr 1
  apply Subtype.ext
  exact Prod.ext hback rfl

/-- The constructed cellular map identifies the lifted-order cells with the existing
path-class universal-cover cells, and preserves their actual attaching paths. -/
def uOrderHom : Hom (orderCx (UOrder P a)) (uCover (orderCx P) a) where
  onV := id
  onE := uOrderEdge
  onF := uOrderFace
  src_onE _ := rfl
  tgt_onE := uOrderEdge_target
  base_onF _ := rfl
  att_onF := uOrderFace_att

theorem uOrderHom_chain2_injective :
    Function.Injective (chain2 (uOrderHom (P := P) (a := a))) :=
  Finsupp.mapDomain_injective uOrderFace_injective

theorem uOrderHom_chain2_surjective :
    Function.Surjective (chain2 (uOrderHom (P := P) (a := a))) :=
  Finsupp.mapDomain_surjective uOrderFace_surjective

theorem uOrderHom_cycle_iff (c : OrdTri (UOrder P a) →₀ ℤ) :
    bdry2 (uCover (orderCx P) a) (chain2 uOrderHom c) = 0 ↔
      bdry2 (orderCx (UOrder P a)) c = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective uOrderEdge_injective
    rw [Finsupp.mapDomain_zero]
    exact h
  · simp_all

/-- Every actual universal-cover two-cycle has a unique finite cycle in the
constructed lifted-order complex as its preimage. -/
theorem exists_unique_uOrder_cycle (c : UF (orderCx P) a →₀ ℤ)
    (hc : bdry2 (uCover (orderCx P) a) c = 0) :
    ∃! d : OrdTri (UOrder P a) →₀ ℤ,
      chain2 uOrderHom d = c ∧ bdry2 (orderCx (UOrder P a)) d = 0 := by
  obtain ⟨d, hd⟩ := uOrderHom_chain2_surjective c
  refine ⟨d, ⟨hd, (uOrderHom_cycle_iff d).mp (hd.symm ▸ hc)⟩, ?_⟩
  intro e he
  exact uOrderHom_chain2_injective (he.1.trans hd.symm)

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u

section Inverse

/-- The two-sided inverse supplied by `Function.surjInv` for a bijection. -/
theorem surjInv_apply_apply {α β : Type u} {f : α → β} (hf : Function.Bijective f)
    (x : α) : Function.surjInv hf.2 (f x) = x :=
  hf.1 (Function.surjInv_eq hf.2 (f x))

variable {L E : Complex2.{u}} (ι : Hom L E)
variable (hV : Function.Bijective ι.onV) (hE : Function.Bijective ι.onE)
  (hF : Function.Bijective ι.onF)

theorem map_surjInv_map (q : List (L.E × Bool)) :
    ((q.map fun eb => (ι.onE eb.1, eb.2)).map
      fun eb => (Function.surjInv hE.2 eb.1, eb.2)) = q := by
  induction q with
  | nil => rfl
  | cons a t ih => simp [ih, surjInv_apply_apply hE]

/-- The inverse of a cellular map which is bijective on cells. -/
def homInv : Hom E L where
  onV := Function.surjInv hV.2
  onE := Function.surjInv hE.2
  onF := Function.surjInv hF.2
  src_onE := by
    intro e
    obtain ⟨e', rfl⟩ := hE.2 e
    rw [surjInv_apply_apply hE, ι.src_onE, surjInv_apply_apply hV]
  tgt_onE := by
    intro e
    obtain ⟨e', rfl⟩ := hE.2 e
    rw [surjInv_apply_apply hE, ι.tgt_onE, surjInv_apply_apply hV]
  base_onF := by
    intro f
    obtain ⟨f', rfl⟩ := hF.2 f
    rw [surjInv_apply_apply hF, ι.base_onF, surjInv_apply_apply hV]
  att_onF := by
    intro f
    obtain ⟨f', rfl⟩ := hF.2 f
    rw [surjInv_apply_apply hF, ι.att_onF]
    exact (map_surjInv_map ι hE (L.att f')).symm


@[simp] theorem homInv_onE_apply (e : E.E) : ι.onE ((homInv ι hV hE hF).onE e) = e :=
  Function.surjInv_eq hE.2 e

@[simp] theorem homInv_onF_apply (f : E.F) : ι.onF ((homInv ι hV hE hF).onF f) = f :=
  Function.surjInv_eq hF.2 f

@[simp] theorem homInv_onV_comp (x : L.V) : (homInv ι hV hE hF).onV (ι.onV x) = x :=
  surjInv_apply_apply hV x

@[simp] theorem homInv_onE_comp (e : L.E) : (homInv ι hV hE hF).onE (ι.onE e) = e :=
  surjInv_apply_apply hE e

@[simp] theorem homInv_onF_comp (f : L.F) : (homInv ι hV hE hF).onF (ι.onF f) = f :=
  surjInv_apply_apply hF f

theorem mapPath_homInv (q : List (L.E × Bool)) :
    mapPath (homInv ι hV hE hF) (mapPath ι q) = q :=
  map_surjInv_map ι hE q

end Inverse

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderHomInv : Hom (uCover (orderCx P) a) (orderCx (UOrder P a)) :=
  homInv uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩

theorem uOrderHomInv_vertex (v : UOrder P a) : uOrderHomInv.onV v = v :=
  homInv_onV_comp uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩ v

theorem uOrderHomInv_path (p : List ((orderCx (UOrder P a)).E × Bool)) :
    mapPath uOrderHomInv (mapPath uOrderHom p) = p :=
  mapPath_homInv uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩ p

/-- The actual lifted-order complex is connected, without any connectivity assumption
on the original poset: path classes use only the component of the chosen base point. -/
theorem uOrder_complex_isConnected : IsConnected (orderCx (UOrder P a)) := by
  intro v w
  obtain ⟨p, hp⟩ := isConnected_univCover (X := orderCx P) (x₀ := a) v w
  refine ⟨mapPath uOrderHomInv p, ?_⟩
  simpa only [uOrderHomInv_vertex] using isPath_mapPath uOrderHomInv hp

/-- Actual loops in the lifted-order complex contract, by the inverse of the
constructed cellular comparison with the path-class universal cover. -/
theorem uOrder_complex_simplyConnected : SimplyConnected (orderCx (UOrder P a)) := by
  intro v p hp
  have h := simplyConnected_univCover (X := orderCx P) (x₀ := a) v
    (mapPath uOrderHom p) (isPath_mapPath uOrderHom hp)
  have hi := mapPath_htpy uOrderHomInv h
  change Htpy (orderCx (UOrder P a)) (uOrderHomInv.onV v) (uOrderHomInv.onV v)
    (mapPath uOrderHomInv (mapPath uOrderHom p)) [] at hi
  rw [uOrderHomInv_path p] at hi
  simpa only [uOrderHomInv_vertex] using hi

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def ordNerveChain0 : (P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun p => FreeAbelianGroup.of [p])

theorem ordNerveChain0_bdry1 (c : OrdEdge P →₀ ℤ) :
    ordNerveChain0 (bdry1 (orderCx P) c) = Nerve.bdry (ordNerveChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [bdry1_single]
    simp
    simp [ordNerveChain0, ordNerveChain1, orderCx, Nerve.bdryOn,
      Nerve.consMap_of, smul_sub, map_sub, Finsupp.linearCombination_single]

theorem ordNerveChain1_mem_inc (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using AddSubgroup.add_mem _ hc hd
  | single e n =>
    simp only [ordNerveChain1, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using e.2

theorem ordNerveChain1_lengthProjection (c : OrdEdge P →₀ ℤ) :
    Nerve.lengthProjection 2 (ordNerveChain1 c) = ordNerveChain1 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n => simp [ordNerveChain1]

theorem ordNerveChain1_chain1 (f : P → Q) (hf : Monotone f) (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 (chain1 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    change ordNerveChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
      (Finsupp.single e n)) = _
    rw [Finsupp.mapDomain_single]
    simp [ordNerveChain1, Nerve.cmap_of, orderCxMap]

end FiniteChains.Comb

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

def decodeOrdVertexList : List P → P →₀ ℤ
  | [a] => Finsupp.single a 1
  | _ => 0

def decodeOrdNerve0 : Nerve.Ch P →+ (P →₀ ℤ) := lift decodeOrdVertexList

omit [PartialOrder P] in
theorem decodeOrdNerve0_encode (c : P →₀ ℤ) :
    decodeOrdNerve0 (ordNerveChain0 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n => simp [ordNerveChain0, decodeOrdNerve0, decodeOrdVertexList]

omit [PartialOrder P] in
theorem ordNerveChain0_injective : Function.Injective (ordNerveChain0 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve0_encode] using congrArg decodeOrdNerve0 h

theorem ordNerveChain1_cycle_iff (c : OrdEdge P →₀ ℤ) :
    Nerve.bdry (ordNerveChain1 c) = 0 ↔ bdry1 (orderCx P) c = 0 := by
  rw [← ordNerveChain0_bdry1]
  exact ⟨fun h => ordNerveChain0_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩


theorem ordNerveChain1_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain1 (decodeOrdNerve1 c) = Nerve.lengthProjection 2 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve1_of]
    exact (by
      cases l with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => simp [decodeOrdEdgeList]
        | cons b l =>
          cases l with
          | nil =>
            have h : a ≤ b := by simpa [List.isChain_cons] using hl
            simp [decodeOrdEdgeList, h, ordNerveChain1]
          | cons c l => simp [decodeOrdEdgeList])
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp_all

end FiniteChains.Comb
end
