module

public import RequestProject.CombData

@[expose] public section

/-!
# The cellular pushout `E = K ∪_p L` of Proposition 3.11

Proposition 3.11 of the paper descends a chain of complexes over an acyclic regular cover
`p : D → K` to a chain over `K` by forming, for every term `L` of the chain upstairs, the
cellular pushout

  `E = K ∪_p L = (K ⊔ L)/(d ∼ p d  for every cell d of D)`.

So far the project used this construction only as a black box (the field `descent` of
`FiniteChains.Comb.Gap`).  This file builds it honestly inside the combinatorial model of
`RequestProject/CellComplex.lean` and proves everything about it that does not involve
homotopy groups:

* `FiniteChains.Comb.pushoutComplex` — the complex `E`: its cells are the cells of `K`
  together with the cells of `L` which do not come from `D`;
* `FiniteChains.Comb.pushoutInl` — the cellular map `K → E`, injective on all cells, so
  `FiniteChains.Comb.sub_pushoutComplex : Sub K E`;
* `FiniteChains.Comb.pushoutMap` — the cellular map `L → E`;
* `FiniteChains.Comb.pushout_comm` — the square commutes: `L → E` precomposed with `D → L`
  is `K → E` precomposed with `p`;
* `FiniteChains.Comb.pushout_universal` — the **universal property**: any pair of cellular
  maps out of `K` and `L` agreeing on `D` factors uniquely through `E`;
* `FiniteChains.Comb.pushoutComplex_finite_*` — `E` has finitely many cells as soon as `K`
  has and `L` has only finitely many cells off `D`.

Only the injectivity of the inclusion `D ⊆ L` is used; `p` is an arbitrary cellular map.
-/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains
namespace Comb

universe u

variable {K D L : Complex2.{u}}

/-! ### Transport of edge paths along a map of graphs -/

/-- A map of graphs takes edge paths to edge paths. -/
theorem isPath_map {V E V' E' : Type*} {src tgt : E → V} {src' tgt' : E' → V'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q : List _} {a b : V}, IsPath src tgt q a b →
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
        cases s <;> simp_all

/-! ### The cells of `L` off `D` -/

variable (i : Hom D L)

/-- The vertices of `L` which do not come from `D`. -/
def OffV := {v : L.V // ∀ d, i.onV d ≠ v}

/-- The edges of `L` which do not come from `D`. -/
def OffE := {e : L.E // ∀ d, i.onE d ≠ e}

/-- The two-cells of `L` which do not come from `D`. -/
def OffF := {f : L.F // ∀ d, i.onF d ≠ f}

variable (p : Hom D K)

variable (i : Hom D L)

open Classical in
/-- The vertex map `L → E`: a vertex coming from `D` goes to its image in `K`, any other
vertex survives. -/
def pushV (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then Sum.inl (p.onV h.choose) else Sum.inr ⟨v, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The edge map `L → E`. -/
def pushE (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then Sum.inl (p.onE h.choose) else Sum.inr ⟨e, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The two-cell map `L → E`. -/
def pushF (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then Sum.inl (p.onF h.choose) else Sum.inr ⟨f, fun d hd => h ⟨d, hd⟩⟩

variable {i : Hom D L}

theorem pushV_of_mem (hi : Function.Injective i.onV) (d : D.V) :
    pushV p i (i.onV d) = Sum.inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem (hi : Function.Injective i.onE) (d : D.E) :
    pushE p i (i.onE d) = Sum.inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := ⟨d, rfl⟩
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem (hi : Function.Injective i.onF) (d : D.F) :
    pushF p i (i.onF d) = Sum.inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := ⟨d, rfl⟩
  rw [pushF, dif_pos h, hi h.choose_spec]

variable (i : Hom D L)

theorem pushV_of_off (v : OffV i) :
    pushV p i v.1 = Sum.inr v := by
  rw [pushV, dif_neg (by grind)]
  rfl

theorem pushE_of_off (e : OffE i) :
    pushE p i e.1 = Sum.inr e := by
  rw [pushE, dif_neg (by grind)]
  rfl

theorem pushF_of_off (f : OffF i) :
    pushF p i f.1 = Sum.inr f := by
  rw [pushF, dif_neg (by grind)]
  rfl

/-! ### The pushout complex -/

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.src e)) (fun e => pushV p i (L.src e.1))

def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

variable (e : L.E)

include hiV hiE in
theorem psrc_pushE : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl _ = _
    simp_all [p.src_onE, i.src_onE, pushV_of_mem]
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]; rfl

include hiV hiE in
theorem ptgt_pushE : ptgt p i (pushE p i e) = pushV p i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl _ = _
    simp_all [p.tgt_onE, i.tgt_onE, pushV_of_mem]
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
    · exact isPath_map (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (K.att_isLoop f)
    · exact isPath_map _ _
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) (L.att_isLoop f.1)

variable (e : K.E)

@[simp] theorem pushoutComplex_src_inl :
    (pushoutComplex p i hiV hiE).src (Sum.inl e) = Sum.inl (K.src e) := rfl

@[simp] theorem pushoutComplex_tgt_inl :
    (pushoutComplex p i hiV hiE).tgt (Sum.inl e) = Sum.inl (K.tgt e) := rfl

variable (e : L.E)

theorem pushoutComplex_src_pushE :
    (pushoutComplex p i hiV hiE).src (pushE p i e) = pushV p i (L.src e) :=
  by solve_by_elim [psrc_pushE]

theorem pushoutComplex_tgt_pushE :
    (pushoutComplex p i hiV hiE).tgt (pushE p i e) = pushV p i (L.tgt e) :=
  by solve_by_elim [ptgt_pushE]

/-- The inclusion `K ⊆ E`. -/
def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
  onV := Sum.inl
  onE := Sum.inl
  onF := Sum.inl
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun _ => rfl

section

variable (hiF : Function.Injective i.onF)
include hiF

variable (f : L.F)

include hiV hiE in
theorem att_pushF :
    (pushoutComplex p i hiV hiE).att (pushF p i f) =
      (L.att f).map fun eb => (pushE p i eb.1, eb.2) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show (K.att _).map _ = _
    simp_all [p.att_onF, i.att_onF, Function.comp, pushE_of_mem]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiV hiE in
theorem base_pushF :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show Sum.inl _ = _
    simp_all [p.base_onF, i.base_onF, pushV_of_mem]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

/-- The cellular map `L → E`. -/
def pushoutMap :
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
theorem pushout_comm :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have : ∀ (X Y : Complex2.{u}) (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨a, b, c, _, _, _, _⟩ ⟨a', b', c', _, _, _, _⟩ h1 h2 h3
    simp_all
  exact this _ _ _ _ (funext (pushV_of_mem p hiV)) (funext (pushE_of_mem p hiE)) (funext (pushF_of_mem p hiF))

end

/-! ### The universal property -/

variable {M : Complex2.{u}}

variable (f : Hom K M)
    (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d))

/-- The map out of the pushout induced by a compatible pair of maps. -/
def pushoutLift : Hom (pushoutComplex p i hiV hiE) M := by
  have lV : ∀ v : L.V, Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v := by
    intro v
    by_cases h : ∃ d, i.onV d = v
    · grind [pushV_of_mem]
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  have lE : ∀ e : L.E, Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e := by
    intro e
    by_cases h : ∃ d, i.onE d = e
    · grind [pushE_of_mem]
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
        · show M.att _ = ((K.att c).map _).map _
          simp [f.att_onF]
        · show M.att _ = ((L.att c.1).map _).map _
          simp [g.att_onF, List.map_map, Function.comp, lE] }

@[simp] theorem pushoutLift_onV :
    (pushoutLift p i hiV hiE f g hV hE).onV = Sum.elim f.onV (fun w : OffV i => g.onV w.1) := rfl

@[simp] theorem pushoutLift_onE :
    (pushoutLift p i hiV hiE f g hV hE).onE = Sum.elim f.onE (fun w : OffE i => g.onE w.1) := rfl

@[simp] theorem pushoutLift_onF :
    (pushoutLift p i hiV hiE f g hV hE).onF = Sum.elim f.onF (fun w : OffF i => g.onF w.1) := rfl

/-! ### Finiteness -/

end

/-! ### Functoriality in the term upstairs -/

section Functor

variable {L' : Complex2.{u}}

variable (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')

section

variable (hj'V : Function.Injective j'.onV)
    (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF)
    (hkj : k.comp j = j')
include hkj

theorem functor_hV (d : D.V) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d) =
      (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
  show pushV p j' _ = Sum.inl _
  rw [show k.onV _ = j'.onV d from congrFun (congrArg Hom.onV hkj) d,
    pushV_of_mem p hj'V]

theorem functor_hE (d : D.E) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d) =
      (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
  show pushE p j' _ = Sum.inl _
  rw [show k.onE _ = j'.onE d from congrFun (congrArg Hom.onE hkj) d,
    pushE_of_mem p hj'E]

end

/-- The map of pushouts induced by an inclusion `L ⊆ L'` of terms over `D`. -/
def pushoutFunctor
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :=
  pushoutLift p j hjV hjE _ _
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)

variable {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}

/-- A cell of `L` off `D` stays off `D` in a larger term `L'`. -/
theorem off_map_V
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 := by
  intro d hd
  refine w.2 d (hkV ?_) <;> aesop

theorem off_map_E
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 := by
  intro d hd
  refine w.2 d (hkE ?_) <;> aesop

theorem off_map_F
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 := by
  intro d hd
  refine w.2 d (hkF ?_) <;> aesop

end Functor

/-! ### Connectivity -/

section Connected

/-- **The pushout of connected complexes is connected.** -/
theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  set E := pushoutComplex p i hiV hiE
  set b : E.V := Sum.inl _
  have key : ∀ x : E.V, (∃ q, IsPath E.src E.tgt q x b) ∧ ∃ q, IsPath E.src E.tgt q b x := by
    rintro (a | w)
    · obtain ⟨q₁, hq₁⟩ := hK a _
      obtain ⟨q₂, hq₂⟩ := hK (p.onV d₀) a
      exact ⟨⟨_, isPath_map (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₁⟩,
        ⟨_, isPath_map (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₂⟩⟩
    · have hw := pushV_of_off p i w
      have hd := pushV_of_mem p hiV d₀
      obtain ⟨q₁, hq₁⟩ := hL w.1 (i.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hL (i.onV d₀) w.1
      have h₁ := isPath_map _ _
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₁
      have h₂ := isPath_map _ _
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
