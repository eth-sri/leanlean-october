import RequestProject.CombData
import RequestProject.Tac
noncomputable section


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

bwd

namespace FiniteChains.Comb

universe u

variable {K D L : Complex2.{u}}

/-! ### Transport of edge paths along a map of graphs -/

/-- A map of graphs takes edge paths to edge paths. -/
theorem isPath_map {V E V' E'} {src tgt} {src' tgt'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q} {a b}, IsPath src tgt q a b →
      IsPath src' tgt' (q.map fun eb => (fE eb.1, eb.2)) (fV a) (fV b) := by
  intro q
  induction q with
  | nil => simp
  | cons eb q ih =>
      rintro a b ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases' eb with e s
        cases s <;> simp [germSrc, hs, ht] at h1 ⊢ <;> exact congrArg fV h1
      · cases' eb with e s
        cases s
        · simp_all
        simp_all

/-! ### The cells of `L` off `D` -/

/-- The vertices of `L` which do not come from `D`. -/
def OffV (i : Hom D L) := {v : L.V // ∀ d, i.onV d ≠ v}

/-- The edges of `L` which do not come from `D`. -/
def OffE (i : Hom D L) := {e : L.E // ∀ d, i.onE d ≠ e}

/-- The two-cells of `L` which do not come from `D`. -/
def OffF (i : Hom D L) := {f : L.F // ∀ d, i.onF d ≠ f}

open Classical in
/-- The vertex map `L → E`: a vertex coming from `D` goes to its image in `K`, any other
vertex survives. -/
def pushV (p : Hom D K) (i : Hom D L) (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then Sum.inl (p.onV h.choose) else Sum.inr ⟨v, by simp_all⟩

open Classical in
/-- The edge map `L → E`. -/
def pushE (p : Hom D K) (i : Hom D L) (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then Sum.inl (p.onE h.choose) else Sum.inr ⟨e, by simp_all⟩

open Classical in
/-- The two-cell map `L → E`. -/
def pushF (p : Hom D K) (i : Hom D L) (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then Sum.inl (p.onF h.choose) else Sum.inr ⟨f, by simp_all⟩

theorem pushV_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onV) d :
    pushV p i (i.onV d) = Sum.inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := by simp
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onE) d :
    pushE p i (i.onE d) = Sum.inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := by simp
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onF) d :
    pushF p i (i.onF d) = Sum.inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := by simp
  rw [pushF, dif_pos h, hi h.choose_spec]

theorem pushV_of_off (p : Hom D K) (i : Hom D L) v :
    pushV p i v.1 = Sum.inr v := by
  rw [pushV, dif_neg (by grind)]
  rfl

theorem pushE_of_off (p : Hom D K) (i : Hom D L) e :
    pushE p i e.1 = Sum.inr e := by
  rw [pushE, dif_neg (by grind)]
  rfl

theorem pushF_of_off (p : Hom D K) (i : Hom D L) f :
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

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.src (p.onE d)) = _
    rw [p.src_onE, i.src_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, by simp_all⟩]
    rfl

include hiV hiE in
theorem ptgt_pushE (e : L.E) : ptgt p i (pushE p i e) = pushV p i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.tgt (p.onE d)) = _
    rw [p.tgt_onE, i.tgt_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, by simp_all⟩]
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



theorem pushoutComplex_src_pushE e :
    (pushoutComplex p i hiV hiE).src (pushE p i e) = pushV p i (L.src e) :=
  psrc_pushE p i hiV hiE e

theorem pushoutComplex_tgt_pushE e :
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
  · rw [pushF_of_off p i ⟨f, by simp_all⟩]
    rfl

include hiV hiE in
theorem base_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) := by
  by_cases h : ∃ d, i.onF d = f
  · obtain ⟨d, rfl⟩ := h
    rw [pushF_of_mem p hiF d]
    show Sum.inl (K.base (p.onF d)) = _
    rw [p.base_onF, i.base_onF, pushV_of_mem p hiV]
  · rw [pushF_of_off p i ⟨f, by simp_all⟩]
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
theorem pushout_comm hiF :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have hV : ∀ d, pushV p i (i.onV d) = Sum.inl (p.onV d) := pushV_of_mem p hiV
  have hE : ∀ d, pushE p i (i.onE d) = Sum.inl (p.onE d) := pushE_of_mem p hiE
  have hF : ∀ d, pushF p i (i.onF d) = Sum.inl (p.onF d) := pushF_of_mem p hiF
  have : ∀ (X Y : Complex2.{u}) (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨a, b, c, _, _, _, _⟩ ⟨a', b', c', _, _, _, _⟩ h1 h2 h3
    simp_all
  aesop

/-! ### The universal property -/

variable {M : Complex2.{u}}

/-- The map out of the pushout induced by a compatible pair of maps. -/
def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV : ∀ v, Sum.elim f.onV (g.onV ·.1) (pushV p i v) = g.onV v := by
    intro v
    by_cases h : ∃ d, i.onV d = v
    · obtain ⟨d, rfl⟩ := h
      rw [pushV_of_mem p hiV d]
      simp_all
    · rw [pushV_of_off p i ⟨v, by simp_all⟩]
      rfl
  have lE : ∀ e, Sum.elim f.onE (g.onE ·.1) (pushE p i e) = g.onE e := by
    intro e
    by_cases h : ∃ d, i.onE d = e
    · obtain ⟨d, rfl⟩ := h
      rw [pushE_of_mem p hiE d]
      simp_all
    · rw [pushE_of_off p i ⟨e, by simp_all⟩]
      rfl
  exact
    { onV := Sum.elim f.onV (g.onV ·.1)
      onE := Sum.elim f.onE (g.onE ·.1)
      onF := Sum.elim f.onF (g.onF ·.1)
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

section Functor

variable {L' : Complex2.{u}}

theorem functor_hV (p : Hom D K) j j' (k : Hom L L')
    hj'V hj'E
    hj'F (hkj : k.comp j = j') d :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d) =
      (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
  show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
  rw [show k.onV (j.onV d) = j'.onV d from by aesop,
    pushV_of_mem p hj'V]

theorem functor_hE (p : Hom D K) j j' (k : Hom L L')
    hj'V hj'E
    hj'F (hkj : k.comp j = j') d :
    ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d) =
      (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
  show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
  rw [show k.onE (j.onE d) = j'.onE d from by aesop,
    pushE_of_mem p hj'E]

/-- The map of pushouts induced by an inclusion `L ⊆ L'` of terms over `D`. -/
def pushoutFunctor (p : Hom D K) j j' (k : Hom L L')
    hjV hjE
    hj'V hj'E
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :=
  pushoutLift p j hjV hjE _ _
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)

/-- A cell of `L` off `D` stays off `D` in a larger term `L'`. -/
theorem off_map_V {j' : Hom D L'} {k : Hom L L'}
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 := by
  intro d hd
  refine w.2 d (hkV ?_)
  aesop

theorem off_map_E {j' : Hom D L'} {k : Hom L L'}
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 := by
  intro d hd
  refine w.2 d (hkE ?_)
  aesop

theorem off_map_F {j' : Hom D L'} {k : Hom L L'}
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 := by
  intro d hd
  refine w.2 d (hkF ?_)
  aesop

end Functor

/-! ### Connectivity -/

section Connected

/-- **The pushout of connected complexes is connected.** -/
theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    hiV hiE
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  set E := pushoutComplex p i hiV hiE
  set b : E.V := Sum.inl (p.onV d₀)
  have key : ∀ x, (∃ q, IsPathX E q x b) ∧ ∃ q, IsPathX E q b x := by
    rintro (a | w)
    · cases' hK a _ with q₁ hq₁
      cases' hK _ a with q₂ hq₂
      exact ⟨⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (by aesop)
          (by aesop) hq₁⟩,
        ⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (by aesop)
          (by aesop) hq₂⟩⟩
    · have hw := pushV_of_off p i w
      have hd := pushV_of_mem p hiV d₀
      cases' hL w.1 (i.onV d₀) with q₁ hq₁
      cases' hL (i.onV d₀) w.1 with q₂ hq₂
      have h₁ := isPath_map (src := L.src) (tgt := L.tgt) _ _
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₁
      have h₂ := isPath_map (src := L.src) (tgt := L.tgt) _ _
        (pushoutComplex_src_pushE p i hiV hiE) (pushoutComplex_tgt_pushE p i hiV hiE) hq₂
      aesop
  intro x y
  obtain ⟨⟨q₁, hq₁⟩, -⟩ := key x
  obtain ⟨-, ⟨q₂, hq₂⟩⟩ := key y
  exact ⟨q₁ ++ q₂, hq₁.append hq₂⟩
