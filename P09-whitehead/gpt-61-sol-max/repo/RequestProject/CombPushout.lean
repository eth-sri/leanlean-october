import Mathlib.Tactic

import RequestProject.CombData

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

namespace FiniteChains.Comb



variable {K D L : Complex2.{u}}

/-! ### Transport of edge paths along a map of graphs -/

/-- A map of graphs takes edge paths to edge paths. -/
theorem isPath_map {V E V' E' : Type*} {src tgt : E → V} {src' tgt' : E' → V'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q : List (E × Bool)} {a b : V}, IsPath src tgt q a b →
      IsPath src' tgt' (q.map fun eb => (fE eb.1, eb.2)) (fV a) (fV b) := by
  classical
  intro q
  induction q <;> grind [FiniteChains.Comb.IsPath, germSrc, germTgt]

/-! ### The cells of `L` off `D` -/

variable (i : Hom D L)
/-- The vertices of `L` which do not come from `D`. -/
def OffV   := {v : L.V // ∀ d, i.onV d ≠ v}

/-- The edges of `L` which do not come from `D`. -/
def OffE   := {e : L.E // ∀ d, i.onE d ≠ e}

/-- The two-cells of `L` which do not come from `D`. -/
def OffF   := {f : L.F // ∀ d, i.onF d ≠ f}

variable (p : Hom D K)
  (i : Hom D L)
open Classical in
/-- The vertex map `L → E`: a vertex coming from `D` goes to its image in `K`, any other
vertex survives. -/
noncomputable def pushV   (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then Sum.inl (p.onV h.choose) else Sum.inr ⟨v, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The edge map `L → E`. -/
noncomputable def pushE   (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then Sum.inl (p.onE h.choose) else Sum.inr ⟨e, fun d hd => h ⟨d, hd⟩⟩

open Classical in
/-- The two-cell map `L → E`. -/
noncomputable def pushF   (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then Sum.inl (p.onF h.choose) else Sum.inr ⟨f, fun d hd => h ⟨d, hd⟩⟩

theorem pushV_of_mem  {i : Hom D L} (hi : Function.Injective i.onV) (d : D.V) :
    pushV p i (i.onV d) = Sum.inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := by grind
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem  {i : Hom D L} (hi : Function.Injective i.onE) (d : D.E) :
    pushE p i (i.onE d) = Sum.inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := by grind
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem  {i : Hom D L} (hi : Function.Injective i.onF) (d : D.F) :
    pushF p i (i.onF d) = Sum.inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := by grind
  rw [pushF, dif_pos h, hi h.choose_spec]

theorem pushV_of_off   (v : OffV i) :
    pushV p i v.1 = Sum.inr v := by
  rw [pushV, dif_neg (by rintro ⟨d, hd⟩; exact v.2 d hd)]
  rfl

theorem pushE_of_off   (e : OffE i) :
    pushE p i e.1 = Sum.inr e := by
  rw [pushE, dif_neg (by rintro ⟨d, hd⟩; exact e.2 d hd)]
  rfl

theorem pushF_of_off   (f : OffF i) :
    pushF p i f.1 = Sum.inr f := by
  rw [pushF, dif_neg (by rintro ⟨d, hd⟩; exact f.2 d hd)]
  rfl

/-! ### The pushout complex -/

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

noncomputable def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.src e)) (fun e => pushV p i (L.src e.1))

noncomputable def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.src (p.onE d)) = _
    rw [p.src_onE, i.src_onE, pushV_of_mem p hiV]
  · 
    rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    show pushV p i (L.src e) = pushV p i (L.src e)
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
noncomputable def pushoutComplex : Complex2.{u} where
  V := K.V ⊕ OffV i
  E := K.E ⊕ OffE i
  F := K.F ⊕ OffF i
  src := psrc p i
  tgt := ptgt p i
  base := Sum.elim (fun f => Sum.inl (K.base f)) (fun f => pushV p i (L.base f.1))
  att := Sum.elim (fun f => (K.att f).map fun eb => (Sum.inl eb.1, eb.2))
    (fun f => (L.att f.1).map fun eb => (pushE p i eb.1, eb.2))
  att_isLoop := by
    aesop (add unsafe apply [FiniteChains.Comb.isPath_map, FiniteChains.Comb.Complex2.att_isLoop, FiniteChains.Comb.psrc_pushE, FiniteChains.Comb.ptgt_pushE])





abbrev pushoutComplex_src_pushE.{eta_u0} :=
  @FiniteChains.Comb.psrc_pushE.{eta_u0}

abbrev pushoutComplex_tgt_pushE.{eta_u0} :=
  @FiniteChains.Comb.ptgt_pushE.{eta_u0}

/-- The inclusion `K ⊆ E`. -/
noncomputable def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
  onV := Sum.inl
  onE := Sum.inl
  onF := Sum.inl
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun _ => rfl

variable (hiF : Function.Injective i.onF)
include hiF in
include hiV hiE in
theorem att_pushF  (f : L.F) :
    (pushoutComplex p i hiV hiE).att (pushF p i f) =
      (L.att f).map fun eb => (pushE p i eb.1, eb.2) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show (K.att (p.onF d)).map (fun eb => (Sum.inl eb.1, eb.2)) = _
    rw [p.att_onF, i.att_onF]
    simp [pushE_of_mem p hiE]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiF in
include hiV hiE in
theorem base_pushF  (f : L.F) :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show Sum.inl (K.base (p.onF d)) = _
    rw [p.base_onF, i.base_onF, pushV_of_mem p hiV]
  · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include hiF in
/-- The cellular map `L → E`. -/
noncomputable def pushoutMap  :
    Hom L (pushoutComplex p i hiV hiE) where
  onV := pushV p i
  onE := pushE p i
  onF := pushF p i
  src_onE := pushoutComplex_src_pushE p i hiV hiE
  tgt_onE := pushoutComplex_tgt_pushE p i hiV hiE
  base_onF := base_pushF p i hiV hiE hiF
  att_onF := att_pushF p i hiV hiE hiF

include hiF in
/-- **The pushout square commutes**: a cell of `D` has the same image in `E` whether it is
pushed into `L` or mapped into `K`. -/
theorem pushout_comm  :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have hV  := pushV_of_mem p hiV
  have hE  := pushE_of_mem p hiE
  have hF  := pushF_of_mem p hiF
  have : ∀ (X Y : Complex2.{u}) (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨a, b, c, _, _, _, _⟩ ⟨a', b', c', _, _, _, _⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  exact this _ _ _ _ (funext hV) (funext hE) (funext hF)

/-! ### The universal property -/

variable {M : Complex2.{u}}

/-- The map out of the pushout induced by a compatible pair of maps. -/
noncomputable def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV : ∀ v : L.V, Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v := by
    intro v
    by_cases h : ∃ d, i.onV d = v
    · classical aesop (add simp [pushV_of_mem])
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  have lE : ∀ e : L.E, Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e := by
    intro e
    by_cases h : ∃ d, i.onE d = e
    · classical grind [pushE_of_mem]
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
          simp_all }







/-! ### Finiteness -/

end

/-! ### Functoriality in the term upstairs -/

section

variable {L' : Complex2.{u}}

variable (p : Hom D K)
  (j : Hom D L)
theorem functor_hV   (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.V) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d) =
      (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
  show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
  aesop (add unsafe apply [pushV_of_mem])

theorem functor_hE   (j' : Hom D L') (k : Hom L L')
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') (d : D.E) :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d) =
      (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
  show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
  aesop (add unsafe apply [pushE_of_mem])

/-- The map of pushouts induced by an inclusion `L ⊆ L'` of terms over `D`. -/
noncomputable def pushoutFunctor   (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')  :=
  pushoutLift p j hjV hjE (pushoutInl p j' hj'V hj'E) ((pushoutMap p j' hj'V hj'E hj'F).comp k)
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)

variable {j : Hom D L}
  {j' : Hom D L'}
/-- A cell of `L` off `D` stays off `D` in a larger term `L'`. -/
theorem off_map_V   {k : Hom L L'}
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 := by
  intro d hd
  refine w.2 d (hkV ?_)
  rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d, hd]

theorem off_map_E   {k : Hom L L'}
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 := by
  intro d hd
  refine w.2 d (hkE ?_)
  rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d, hd]

theorem off_map_F   {k : Hom L L'}
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 := by
  intro d hd
  refine w.2 d (hkF ?_)
  rw [show k.onF (j.onF d) = j'.onF d from congrFun (congrArg Hom.onF hkj) d, hd]

end

/-! ### Connectivity -/

section

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
      exact ⟨⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₁⟩,
        ⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl)
          (fun _ => rfl) hq₂⟩⟩
    · have hw  := pushV_of_off p i w
      have hd  := pushV_of_mem p hiV d₀
      obtain ⟨q₁, hq₁⟩ := hL w.1 (i.onV d₀)
      obtain ⟨q₂, hq₂⟩ := hL (i.onV d₀) w.1
      have h₁ := isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₁
      have h₂ := isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₂
      rw [hw, hd] at h₁
      rw [hw, hd] at h₂
      exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
  intro x y
  obtain ⟨⟨q₁, hq₁⟩, -⟩ := key x
  obtain ⟨-, ⟨q₂, hq₂⟩⟩ := key y
  exact ⟨q₁ ++ q₂, hq₁.append hq₂⟩

end

end FiniteChains.Comb

