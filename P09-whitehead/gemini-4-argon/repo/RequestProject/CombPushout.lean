module

public import RequestProject.CombData

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

variable {K D L : Complex2.{u}}

theorem isPath_map {V E V' E' : Type*} {src tgt : E → V} {src' tgt' : E' → V'}
    (fV : V → V') (fE : E → E') (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    ∀ {q : List (E × Bool)} {a b : V}, IsPath src tgt q a b →
      IsPath src' tgt' (q.map fun eb => (fE eb.1, eb.2)) (fV a) (fV b)
  | [], _, _, h => congrArg fV h
  | (_, s) :: _, _, _, ⟨h1, h2⟩ =>
      ⟨by cases s <;> simp [germSrc, hs, ht] at h1 ⊢ <;> exact congrArg fV h1,
       by cases s <;> simpa [germTgt, hs, ht] using isPath_map fV fE hs ht h2⟩

def OffV (i : Hom D L) : Type u := {v : L.V // ∀ d, i.onV d ≠ v}
def OffE (i : Hom D L) : Type u := {e : L.E // ∀ d, i.onE d ≠ e}
def OffF (i : Hom D L) : Type u := {f : L.F // ∀ d, i.onF d ≠ f}

open Classical in
noncomputable def pushV (p : Hom D K) (i : Hom D L) (v : L.V) : K.V ⊕ OffV i :=
  if h : ∃ d, i.onV d = v then .inl (p.onV h.choose) else .inr ⟨v, fun d hd => h ⟨d, hd⟩⟩

open Classical in
noncomputable def pushE (p : Hom D K) (i : Hom D L) (e : L.E) : K.E ⊕ OffE i :=
  if h : ∃ d, i.onE d = e then .inl (p.onE h.choose) else .inr ⟨e, fun d hd => h ⟨d, hd⟩⟩

open Classical in
noncomputable def pushF (p : Hom D K) (i : Hom D L) (f : L.F) : K.F ⊕ OffF i :=
  if h : ∃ d, i.onF d = f then .inl (p.onF h.choose) else .inr ⟨f, fun d hd => h ⟨d, hd⟩⟩

theorem pushV_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onV) (d : D.V) :
    pushV p i (i.onV d) = .inl (p.onV d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  rw [pushV, dif_pos h, hi h.choose_spec]

theorem pushE_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onE) (d : D.E) :
    pushE p i (i.onE d) = .inl (p.onE d) := by
  have h : ∃ d', i.onE d' = i.onE d := ⟨d, rfl⟩
  rw [pushE, dif_pos h, hi h.choose_spec]

theorem pushF_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onF) (d : D.F) :
    pushF p i (i.onF d) = .inl (p.onF d) := by
  have h : ∃ d', i.onF d' = i.onF d := ⟨d, rfl⟩
  rw [pushF, dif_pos h, hi h.choose_spec]

theorem pushV_of_off (p : Hom D K) (i : Hom D L) (v : OffV i) :
    pushV p i v.1 = .inr v := dif_neg fun ⟨d, hd⟩ => v.2 d hd

theorem pushE_of_off (p : Hom D K) (i : Hom D L) (e : OffE i) :
    pushE p i e.1 = .inr e := dif_neg fun ⟨d, hd⟩ => e.2 d hd

theorem pushF_of_off (p : Hom D K) (i : Hom D L) (f : OffF i) :
    pushF p i f.1 = .inr f := dif_neg fun ⟨d, hd⟩ => f.2 d hd

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

noncomputable def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => .inl (K.src e)) (fun e => pushV p i (L.src e.1))

noncomputable def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => .inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.src (p.onE d)) = _
    rw [p.src_onE, i.src_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]; rfl

include hiV hiE in
theorem ptgt_pushE (e : L.E) : ptgt p i (pushE p i e) = pushV p i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE d]
    show Sum.inl (K.tgt (p.onE d)) = _
    rw [p.tgt_onE, i.tgt_onE, pushV_of_mem p hiV]
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]; rfl

noncomputable def pushoutComplex : Complex2.{u} where
  V := K.V ⊕ OffV i
  E := K.E ⊕ OffE i
  F := K.F ⊕ OffF i
  src := psrc p i
  tgt := ptgt p i
  base := Sum.elim (fun f => .inl (K.base f)) (fun f => pushV p i (L.base f.1))
  att := Sum.elim (fun f => (K.att f).map fun eb => (.inl eb.1, eb.2))
    (fun f => (L.att f.1).map fun eb => (pushE p i eb.1, eb.2))
  att_isLoop := by
    rintro (f | f)
    · exact isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (K.att_isLoop f)
    · exact isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) (L.att_isLoop f.1)

noncomputable def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
  onV := .inl
  onE := .inl
  onF := .inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

noncomputable def pushoutMap (hiF : Function.Injective i.onF) :
    Hom L (pushoutComplex p i hiV hiE) where
  onV := pushV p i
  onE := pushE p i
  onF := pushF p i
  src_onE := psrc_pushE p i hiV hiE
  tgt_onE := ptgt_pushE p i hiV hiE
  base_onF f := by
    by_cases h : ∃ d, i.onF d = f
    · obtain ⟨d, rfl⟩ := h
      rw [pushF_of_mem p hiF d]
      show Sum.inl (K.base (p.onF d)) = _
      rw [p.base_onF, i.base_onF, pushV_of_mem p hiV]
    · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]; rfl
  att_onF f := by
    by_cases h : ∃ d, i.onF d = f
    · obtain ⟨d, rfl⟩ := h
      rw [pushF_of_mem p hiF d]
      show (K.att (p.onF d)).map (fun eb => (Sum.inl eb.1, eb.2)) = _
      rw [p.att_onF, i.att_onF]
      simp [Function.comp, pushE_of_mem p hiE]
    · rw [pushF_of_off p i ⟨f, fun d hd => h ⟨d, hd⟩⟩]; rfl

theorem pushout_comm (hiF : Function.Injective i.onF) :
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := by
  have : ∀ (X Y : Complex2.{u}) (f g : Hom X Y), f.onV = g.onV → f.onE = g.onE →
      f.onF = g.onF → f = g := by
    rintro X Y ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ rfl rfl rfl; rfl
  exact this _ _ _ _ (funext (pushV_of_mem p hiV)) (funext (pushE_of_mem p hiE))
    (funext (pushF_of_mem p hiF))

variable {M : Complex2.{u}}

noncomputable def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV (v : L.V) : Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v := by
    by_cases h : ∃ d, i.onV d = v
    · obtain ⟨d, rfl⟩ := h; rw [pushV_of_mem p hiV d]; exact (hV d).symm
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]; rfl
  have lE (e : L.E) : Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e := by
    by_cases h : ∃ d, i.onE d = e
    · obtain ⟨d, rfl⟩ := h; rw [pushE_of_mem p hiE d]; exact (hE d).symm
    · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]; rfl
  exact
    { onV := Sum.elim f.onV (fun w : OffV i => g.onV w.1)
      onE := Sum.elim f.onE (fun w : OffE i => g.onE w.1)
      onF := Sum.elim f.onF (fun w : OffF i => g.onF w.1)
      src_onE := by rintro (e | e); exact f.src_onE e; exact (g.src_onE e.1).trans (lV _).symm
      tgt_onE := by rintro (e | e); exact f.tgt_onE e; exact (g.tgt_onE e.1).trans (lV _).symm
      base_onF := by rintro (c | c); exact f.base_onF c; exact (g.base_onF c.1).trans (lV _).symm
      att_onF := by
        rintro (c | c)
        · show M.att (f.onF c) = ((K.att c).map fun eb => (Sum.inl eb.1, eb.2)).map _
          simp [f.att_onF]
        · show M.att (g.onF c.1) = ((L.att c.1).map fun eb => (pushE p i eb.1, eb.2)).map _
          rw [g.att_onF, List.map_map]
          exact List.map_congr_left fun eb _ => by simp [Function.comp, lE eb.1] }

end

section

variable {L' : Complex2.{u}}

noncomputable def pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :
    Hom (pushoutComplex p j hjV hjE) (pushoutComplex p j' hj'V hj'E) :=
  pushoutLift p j hjV hjE (pushoutInl p j' hj'V hj'E) ((pushoutMap p j' hj'V hj'E hj'F).comp k)
    (fun d => by
      show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
      erw [congrFun (congrArg Hom.onV hkj) d, pushV_of_mem p hj'V])
    (fun d => by
      show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
      erw [congrFun (congrArg Hom.onE hkj) d, pushE_of_mem p hj'E])

theorem off_map_V {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkV : Function.Injective k.onV) (hkj : k.comp j = j') (w : OffV j) :
    ∀ d, j'.onV d ≠ k.onV w.1 :=
  fun d hd => w.2 d (hkV ((congrFun (congrArg Hom.onV hkj) d).trans hd))

theorem off_map_E {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkE : Function.Injective k.onE) (hkj : k.comp j = j') (w : OffE j) :
    ∀ d, j'.onE d ≠ k.onE w.1 :=
  fun d hd => w.2 d (hkE ((congrFun (congrArg Hom.onE hkj) d).trans hd))

theorem off_map_F {j : Hom D L} {j' : Hom D L'} {k : Hom L L'}
    (hkF : Function.Injective k.onF) (hkj : k.comp j = j') (w : OffF j) :
    ∀ d, j'.onF d ≠ k.onF w.1 :=
  fun d hd => w.2 d (hkF ((congrFun (congrArg Hom.onF hkj) d).trans hd))

end

theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  set E := pushoutComplex p i hiV hiE
  set b : E.V := .inl (p.onV d₀)
  have mapK {x y : K.V} : ∃ q, IsPath E.src E.tgt q (.inl x) (.inl y) :=
    let ⟨q, hq⟩ := hK x y
    ⟨_, isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl) hq⟩
  have mapL {x y : L.V} : ∃ q, IsPath E.src E.tgt q (pushV p i x) (pushV p i y) :=
    let ⟨q, hq⟩ := hL x y
    ⟨_, isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
      (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) hq⟩
  have key : ∀ x : E.V, (∃ q, IsPath E.src E.tgt q x b) ∧ ∃ q, IsPath E.src E.tgt q b x
    | .inl _ => ⟨mapK, mapK⟩
    | .inr w => by
        have h1 := @mapL w.1 (i.onV d₀); have h2 := @mapL (i.onV d₀) w.1
        rw [pushV_of_off, pushV_of_mem p hiV] at h1 h2
        exact ⟨h1, h2⟩
  intro x y
  obtain ⟨⟨q₁, hq₁⟩, -⟩ := key x
  obtain ⟨-, ⟨q₂, hq₂⟩⟩ := key y
  exact ⟨q₁ ++ q₂, hq₁.append hq₂⟩
