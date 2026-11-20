module

public import RequestProject.ComponentComplex

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {K D L : Complex2.{u}}

/-! ### The pushout of types along an embedding -/

/-- Elements outside the image of the gluing map. -/
abbrev OffRange {α β : Type*} (i : α → β) := {x : β // ∀ a, i a ≠ x}

open Classical in
/-- The pushout consists of the left type and the part of the right type outside the overlap. -/
noncomputable def glueCell {α β γ : Type*} (p : α → γ) (i : α → β) (x : β) : γ ⊕ OffRange i :=
  if h : ∃ a, i a = x then Sum.inl (p h.choose) else Sum.inr ⟨x, fun a ha => h ⟨a, ha⟩⟩

section GlueCell
variable {α β γ : Type*} {i : α → β} (p : α → γ)

theorem glueCell_of_mem (hi : Function.Injective i) (a : α) :
    glueCell p i (i a) = Sum.inl (p a) := by
  classical
  have h : ∃ b, i b = i a := ⟨a, rfl⟩
  rw [glueCell, dite_eq_left h, hi h.choose_spec]

theorem glueCell_of_off (x : OffRange i) : glueCell p i x.1 = Sum.inr x := by
  classical
  rw [glueCell, dite_eq_right (by rintro ⟨a, ha⟩; exact x.2 a ha)]

/-- To check a property of a right-hand cell and its image, check the overlap and its complement. -/
theorem glueCell_cases (hi : Function.Injective i) {R : β → γ ⊕ OffRange i → Prop}
    (h₁ : ∀ a, R (i a) (Sum.inl (p a))) (h₂ : ∀ x : OffRange i, R x.1 (Sum.inr x))
    (x : β) : R x (glueCell p i x) := by
  by_cases h : x ∈ Set.range i
  · obtain ⟨a, rfl⟩ := h
    rw [glueCell_of_mem p hi]
    exact h₁ a
  · let y : OffRange i := ⟨x, fun a ha => h ⟨a, ha⟩⟩
    change R y.1 (glueCell p i y.1)
    rw [glueCell_of_off p y]
    exact h₂ y

/-- A compatible pair of maps out of the two types agrees with the right inclusion. -/
theorem glueCell_elim {δ : Type*} (hi : Function.Injective i) (f : γ → δ) (g : β → δ)
    (h : ∀ a, f (p a) = g (i a)) (x : β) :
    (Sum.elim f fun t : OffRange i => g t.1) (glueCell p i x) = g x :=
  glueCell_cases p hi (R := fun t z => (Sum.elim f fun u  => g u.1) z = g t)
    h (fun _ => rfl) x

theorem glueCell_inl_iff (hi : Function.Injective i) (x : β) :
    (∃ y, glueCell p i x = Sum.inl y) ↔ x ∈ Set.range i := by
  apply glueCell_cases p hi (R := fun t z => (∃ y, z = Sum.inl y) ↔ t ∈ Set.range i)
  · exact fun a => iff_of_true ⟨p a, rfl⟩ ⟨a, rfl⟩
  · intro t
    simp [Set.mem_range, show ¬ ∃ a, i a = t.1 from fun ⟨a, ha⟩ => t.2 a ha]

/-- Only two cells in the glued part can be identified by the right inclusion. -/
theorem glueCell_eq (hi : Function.Injective i) {x y : β} (h : glueCell p i x = glueCell p i y) :
    x = y ∨ ∃ a b, x = i a ∧ y = i b ∧ p a = p b := by
  revert h
  refine glueCell_cases p hi (R := fun x z => z = glueCell p i y →
    x = y ∨ ∃ a b, x = i a ∧ y = i b ∧ p a = p b) (fun a => ?_) (fun x => ?_) x
  · refine glueCell_cases p hi (R := fun y z => Sum.inl (p a) = z →
      i a = y ∨ ∃ a' b, i a = i a' ∧ y = i b ∧ p a' = p b) (fun b h => ?_) (by simp) y
    exact Or.inr ⟨a, b, rfl, rfl, Sum.inl.inj h⟩
  · refine glueCell_cases p hi (R := fun y z => Sum.inr x = z →
      x.1 = y ∨ ∃ a b, x.1 = i a ∧ y = i b ∧ p a = p b) (by simp) (fun y h => ?_) y
    exact Or.inl (congrArg Subtype.val (Sum.inr.inj h))

theorem glueCell_eq_inr_val (hi : Function.Injective i) {x : β} {y : OffRange i}
    (h : glueCell p i x = Sum.inr y) : x = y.val := by
  revert h
  refine glueCell_cases p hi (R := fun x z => z = Sum.inr y → x = y.val) (by simp) ?_ x
  exact fun _ h => congrArg Subtype.val (Sum.inr.inj h)

/-- An embedding of right-hand types over the same overlap induces an embedding of pushouts. -/
theorem glueCell_functor_injective {δ : Type*} {j : α → δ} {k : β → δ}
    {F : γ ⊕ OffRange i → γ ⊕ OffRange j} (hk : Function.Injective k) (h : k ∘ i = j)
    (hL : ∀ a, F (Sum.inl a) = Sum.inl a)
    (hR : ∀ x : OffRange i, F (Sum.inr x) = glueCell p j (k x.1)) : Function.Injective F := by
  let g (x : OffRange i) : OffRange j :=
    ⟨k x.1, fun a ha => x.2 a (hk ((congrFun h a).trans ha))⟩
  have hF : F = Sum.map id g := by
    funext x
    rcases x with a | x
    · exact hL a
    · exact (hR x).trans (glueCell_of_off p (g x))
  rw [hF]
  exact Sum.map_injective.mpr ⟨fun _ _ h => h, fun _ _ h => Subtype.ext (hk (congrArg Subtype.val h))⟩

end GlueCell

abbrev OffV (i : Hom D L) := OffRange i.onV
abbrev OffE (i : Hom D L) := OffRange i.onE
abbrev OffF (i : Hom D L) := OffRange i.onF

noncomputable abbrev pushV (p : Hom D K) (i : Hom D L) := glueCell p.onV i.onV
noncomputable abbrev pushE (p : Hom D K) (i : Hom D L) := glueCell p.onE i.onE
noncomputable abbrev pushF (p : Hom D K) (i : Hom D L) := glueCell p.onF i.onF

theorem pushV_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onV) (a : D.V) :
    pushV p i (i.onV a) = Sum.inl (p.onV a) := glueCell_of_mem p.onV hi a

theorem pushV_of_off (p : Hom D K) (i : Hom D L) (x : OffV i) :
    pushV p i x.1 = Sum.inr x := glueCell_of_off p.onV x

theorem pushE_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onE) (a : D.E) :
    pushE p i (i.onE a) = Sum.inl (p.onE a) := glueCell_of_mem p.onE hi a

theorem pushE_of_off (p : Hom D K) (i : Hom D L) (x : OffE i) :
    pushE p i x.1 = Sum.inr x := glueCell_of_off p.onE x

theorem pushF_of_mem (p : Hom D K) {i : Hom D L} (hi : Function.Injective i.onF) (a : D.F) :
    pushF p i (i.onF a) = Sum.inl (p.onF a) := glueCell_of_mem p.onF hi a

theorem pushF_of_off (p : Hom D K) (i : Hom D L) (x : OffF i) :
    pushF p i x.1 = Sum.inr x := glueCell_of_off p.onF x

/-! ### The pushout complex -/

section

variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)

noncomputable def psrc : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.src e)) (fun e => pushV p i (L.src e.1))

noncomputable def ptgt : K.E ⊕ OffE i → K.V ⊕ OffV i :=
  Sum.elim (fun e => Sum.inl (K.tgt e)) (fun e => pushV p i (L.tgt e.1))

include hiV hiE in
theorem psrc_pushE (e : L.E) : psrc p i (pushE p i e) = pushV p i (L.src e) :=
  glueCell_elim p.onE hiE (Sum.inl ∘ K.src) (pushV p i ∘ L.src)
    (fun d => by simp [p.src_onE, i.src_onE, pushV_of_mem p hiV]) e

include hiV hiE in
theorem ptgt_pushE (e : L.E) : ptgt p i (pushE p i e) = pushV p i (L.tgt e) :=
  glueCell_elim p.onE hiE (Sum.inl ∘ K.tgt) (pushV p i ∘ L.tgt)
    (fun d => by simp [p.tgt_onE, i.tgt_onE, pushV_of_mem p hiV]) e

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
    rintro (f | f)
    · exact isPath_map (src := K.src) (tgt := K.tgt) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (K.att_isLoop f)
    · exact isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) (L.att_isLoop f.1)



theorem pushoutComplex_src_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).src (pushE p i e) = pushV p i (L.src e) :=
  psrc_pushE p i hiV hiE e

theorem pushoutComplex_tgt_pushE (e : L.E) :
    (pushoutComplex p i hiV hiE).tgt (pushE p i e) = pushV p i (L.tgt e) :=
  ptgt_pushE p i hiV hiE e

/-- The inclusion `K ⊆ E`. -/
noncomputable def pushoutInl : Hom K (pushoutComplex p i hiV hiE) where
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
      (L.att f).map fun eb => (pushE p i eb.1, eb.2) :=
  glueCell_elim (δ := List ((K.E ⊕ OffE i) × Bool)) p.onF hiF (fun t => (K.att t).map fun (eb : K.E × Bool) => (Sum.inl eb.1, eb.2))
    (fun t => (L.att t).map fun (eb : L.E × Bool) => (pushE p i eb.1, eb.2))
    (fun d => by simp [p.att_onF, i.att_onF, Function.comp, pushE_of_mem p hiE]) f

include hiV hiE in
theorem base_pushF (hiF : Function.Injective i.onF) (f : L.F) :
    (pushoutComplex p i hiV hiE).base (pushF p i f) = pushV p i (L.base f) :=
  glueCell_elim p.onF hiF (Sum.inl ∘ K.base) (pushV p i ∘ L.base)
    (fun d => by simp [p.base_onF, i.base_onF, pushV_of_mem p hiV]) f

/-- The cellular map `L → E`. -/
noncomputable def pushoutMap (hiF : Function.Injective i.onF) :
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
    (pushoutMap p i hiV hiE hiF).comp i = (pushoutInl p i hiV hiE).comp p := Hom.ext' (funext (pushV_of_mem p hiV)) (funext (pushE_of_mem p hiE))
    (funext (pushF_of_mem p hiF))

/-! ### The universal property -/

variable {M : Complex2.{u}}

/-- The map out of the pushout induced by a compatible pair of maps. -/
noncomputable def pushoutLift (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d)) : Hom (pushoutComplex p i hiV hiE) M := by
  have lV := glueCell_elim p.onV hiV f.onV g.onV (fun d => (hV d).symm)
  have lE := glueCell_elim p.onE hiE f.onE g.onE (fun d => (hE d).symm)
  exact
    { onV := Sum.elim f.onV (fun w  => g.onV w.1)
      onE := Sum.elim f.onE (fun w  => g.onE w.1)
      onF := Sum.elim f.onF (fun w  => g.onF w.1)
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
noncomputable def pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
    (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j') :
    Hom (pushoutComplex p j hjV hjE) (pushoutComplex p j' hj'V hj'E) :=
  pushoutLift p j hjV hjE (pushoutInl p j' hj'V hj'E) ((pushoutMap p j' hj'V hj'E hj'F).comp k)
    (functor_hV p j j' k hj'V hj'E hj'F hkj) (functor_hE p j j' k hj'V hj'E hj'F hkj)




end Functor

/-! ### Connectivity -/

section Connected

/-- **The pushout of connected complexes is connected.** -/
theorem isConnected_pushoutComplex (p : Hom D K) (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hK : IsConnected K) (hL : IsConnected L) (d₀ : D.V) :
    IsConnected (pushoutComplex p i hiV hiE) := by
  have key (x : (pushoutComplex p i hiV hiE).V) :
      ∃ q, IsPath (psrc p i) (ptgt p i) q (Sum.inl (p.onV d₀)) x := by
    rcases x with x | x
    · obtain ⟨q, hq⟩ := hK (p.onV d₀) x
      exact ⟨_, isPath_mapPath (pushoutInl p i hiV hiE) hq⟩
    · obtain ⟨q, hq⟩ := hL (i.onV d₀) x.1
      have h := isPath_map (src := L.src) (tgt := L.tgt) (pushV p i) (pushE p i)
        (psrc_pushE p i hiV hiE) (ptgt_pushE p i hiV hiE) hq
      rw [pushV_of_mem p hiV, pushV_of_off p i] at h
      exact ⟨_, h⟩
  intro x y
  obtain ⟨pₓ, hx⟩ := key x
  obtain ⟨pᵧ, hy⟩ := key y
  exact ⟨_, (isPath_revPath (X := pushoutComplex p i hiV hiE) hx).append hy⟩

end Connected

end Comb
end FiniteChains
