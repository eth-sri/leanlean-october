/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Kőnig's edge-colouring theorem

A finite bipartite graph has a proper edge colouring with `Δ(G)` colours.
-/

@[expose] public section

namespace Galvin

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {C : Type*}

/-- A partial proper edge colouring of `G` with colours in `C`. -/
structure PC (G : SimpleGraph V) (C : Type*) where
  /-- The colour of a pair of vertices, if it is a coloured edge. -/
  col : Sym2 V → Option C
  adj : ∀ {u v γ}, col s(u, v) = some γ → G.Adj u v
  proper : ∀ {u v w γ}, col s(u, v) = some γ → col s(u, w) = some γ → v = w

namespace PC

attribute [local instance] Classical.propDecidable

variable {G : SimpleGraph V} {C : Type*} [DecidableEq V] [DecidableEq C]

/-- A colour is free at a vertex if no edge at that vertex carries it. -/
def Fr (c : PC G C) (v : V) (γ : C) : Prop := ∀ u, c.col s(v, u) ≠ some γ

/-- Swapping two colours in an optional colour. -/
lemma map_swap {C : Type*} [DecidableEq C] (a b : C) {γ : C} {o : Option C} :
    o.map (Equiv.swap a b) = some γ ↔ o = some (Equiv.swap a b γ) := by
  cases o with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp

/-- `c'` colours at least the edges that `c` colours. -/
def Ex (c c' : PC G C) : Prop := ∀ e, c.col e ≠ none → c'.col e ≠ none

theorem Ex.trans {a b d : PC G C} (h : Ex a b) (h' : Ex b d) : Ex a d :=
  fun e hc => h' e (h e hc)

/-- The colouring that colours nothing. -/
def _empty (G : SimpleGraph V) (C : Type*) : PC G C where
  col _ := none
  adj := by intro u v γ h; simp at h
  proper := by intro u v w γ h; simp at h

/-- Colour the edge `xy` with `γ`, which is free at both endpoints. -/
def se (c : PC G C) (x y : V) (γ : C) (h : G.Adj x y) (hx : c.Fr x γ)
    (hy : c.Fr y γ) : PC G C where
  col e := if e = s(x, y) then some γ else c.col e
  adj := by
    intro u v δ hc
    split_ifs at hc with huv
    · simp only [Option.some_inj] at hc
      subst hc
      grind [Sym2.eq_iff, SimpleGraph.adj_comm]
    · exact c.adj hc
  proper := by
    intro u v w δ h1 h2
    split_ifs at h1 h2
    all_goals grind [Sym2.eq_iff, Fr, PC.proper]

theorem se_ex (c : PC G C) (x y : V) (γ : C) (h : G.Adj x y) (hx : c.Fr x γ)
    (hy : c.Fr y γ) : Ex c (c.se x y γ h hx hy) := by
  intro e he
  by_cases h' : e = s(x, y)
  · simp [se, h']
  · simp only [se, h', ite_false]
    exact he

/-- The subgraph of the edges coloured `a` or `b`. -/
def kg (c : PC G C) (a b : C) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (c.col s(u, v) = some a ∨ c.col s(u, v) = some b)
  symm.symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact h2
  loopless := ⟨fun v h => h.1 rfl⟩

theorem reach (c : PC G C) {a b : C} {x u v : V} (hu : (c.kg a b).Reachable x u)
    (h : c.col s(u, v) = some a ∨ c.col s(u, v) = some b) : (c.kg a b).Reachable x v := by
  refine hu.trans (Adj.reachable ⟨?_, h⟩)
  rcases h with h | h <;> exact (c.adj h).ne

/-- The colour function after swapping `a` and `b` on the Kempe component of `x`. -/
noncomputable def kf (c : PC G C) (a b : C) (x : V) : Sym2 V → Option C :=
  Sym2.lift ⟨fun u v =>
    if (c.kg a b).Reachable x u ∧ (c.kg a b).Reachable x v
    then (c.col s(u, v)).map (Equiv.swap a b) else c.col s(u, v), fun u v => by
      have h : s(v, u) = s(u, v) := Sym2.eq_swap
      simp only [and_comm, h]⟩

theorem kfR (c : PC G C) {a b : C} {x u : V} (hu : (c.kg a b).Reachable x u) (v : V) :
    c.kf a b x s(u, v) = (c.col s(u, v)).map (Equiv.swap a b) := by
  simp only [kf, Sym2.lift_mk]
  split_ifs with hv
  · rfl
  · have hv : ¬ (c.kg a b).Reachable x v := fun h => hv ⟨hu, h⟩
    cases h : c.col s(u, v) with
    | none => simp
    | some γ =>
      simp only [Option.map_some]
      rw [Equiv.swap_apply_of_ne_of_ne (fun e => hv (reach c hu (Or.inl (by rw [h, e]))))
        (fun e => hv (reach c hu (Or.inr (by rw [h, e]))))]

theorem kfN (c : PC G C) {a b : C} {x u : V} (hu : ¬ (c.kg a b).Reachable x u)
    (v : V) : c.kf a b x s(u, v) = c.col s(u, v) := by
  simp only [kf, Sym2.lift_mk]
  split_ifs with h
  · exact absurd h.1 hu
  · rfl

/-- Swapping the colours `a` and `b` on the Kempe component of `x`. -/
noncomputable def ks (c : PC G C) (a b : C) (x : V) : PC G C where
  col := c.kf a b x
  adj := by
    intro u v γ h
    by_cases hu : (c.kg a b).Reachable x u
    · rw [kfR c hu v, map_swap] at h
      exact c.adj h
    · rw [kfN c hu v] at h
      exact c.adj h
  proper := by
    intro u v w γ h1 h2
    by_cases hu : (c.kg a b).Reachable x u
    · rw [kfR c hu v, map_swap] at h1
      rw [kfR c hu w, map_swap] at h2
      exact c.proper h1 h2
    · rw [kfN c hu v] at h1
      rw [kfN c hu w] at h2
      exact c.proper h1 h2

theorem ks_ex (c : PC G C) (a b : C) (x : V) : Ex c (c.ks a b x) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    by_cases hu : (c.kg a b).Reachable x u
    · rw [show (c.ks a b x).col s(u, v) = (c.col s(u, v)).map (Equiv.swap a b) from
        kfR c hu v]
      rcases h : c.col s(u, v) with _ | δ
      · exact fun _ => he h
      · simp
    · rwa [show (c.ks a b x).col s(u, v) = c.col s(u, v) from kfN c hu v]

theorem frR (c : PC G C) {a b : C} {x v : V}
    (hv : (c.kg a b).Reachable x v) (γ : C) :
    c.Fr v (Equiv.swap a b γ) → (c.ks a b x).Fr v γ := by
  intro h u hu
  rw [show (c.ks a b x).col s(v, u) = (c.col s(v, u)).map (Equiv.swap a b) from kfR c hv u,
    map_swap] at hu
  exact h u hu

theorem frN (c : PC G C) {a b : C} {x v : V}
    (hv : ¬ (c.kg a b).Reachable x v) (γ : C) :
    c.Fr v γ → (c.ks a b x).Fr v γ := by
  intro h u hu
  rw [show (c.ks a b x).col s(v, u) = c.col s(v, u) from kfN c hv u] at hu
  exact h u hu

end PC

open PC

/-- At an endpoint of an uc edge some colour is free, provided there are at least `Δ(G)`
colours. -/
theorem free [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hxy : G.Adj x y)
    (hnone : c.col s(x, y) = none) : ∃ γ, c.Fr x γ := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [Fr, not_forall, not_not] at hcon
  choose g hg using hcon
  have hcards := card_le_card_of_injOn (s := univ) g
    (fun γ (_ : γ ∈ (univ : Finset C)) => show g γ ∈ (G.neighborFinset x).erase y from by
      refine mem_erase.2 ⟨fun h => ?_, (mem_neighborFinset _ _ _).2 (c.adj (hg γ))⟩
      have hh := hg γ
      rw [h, hnone] at hh
      simp at hh)
    (fun γ₁ _ γ₂ _ h => Option.some_injective _ (by rw [← hg γ₁, ← hg γ₂, h]))
  rw [card_univ, card_erase_of_mem ((mem_neighborFinset _ _ _).2 hxy),
    card_neighborFinset_eq_degree] at hcards
  have hdeg := G.degree_le_maxDegree x
  have hpos : 0 < G.degree x := G.degree_pos_iff_exists_adj x |>.2 ⟨y, hxy⟩
  omega

/-- Along a walk of a graph contained in `G`, a proper 2-colouring of `G` changes at every step. -/
theorem par {H : SimpleGraph V} (hHG : H ≤ G) (s : G.Coloring (Fin 2)) {u v : V}
    (p : H.Walk u v) : (s v : ℕ) % 2 = ((s u : ℕ) + p.length) % 2 := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    rw [Walk.length_cons, ih]
    have hne : (s u : ℕ) ≠ (s w : ℕ) := fun he => s.valid (hHG h) (Fin.ext he)
    have hu := (s u).isLt
    have hw := (s w).isLt
    omega

/-- **Alternation along a Kempe path.** If `b` is free at `y`, then on every path of the `a/b`
Kempe graph ending at `y`, the first edge has colour `a` if the length is odd and `b` if it is
even (and positive). -/
theorem alt (c : PC G C) {a b : C} {y : V} (hy : c.Fr y b) {u : V}
    (p : (c.kg a b).Walk u y) (hp : p.IsPath) (hlen : 0 < p.length) :
    c.col s(u, p.snd) = some (if p.length % 2 = 1 then a else b) := by
  induction p with
  | nil => simp at hlen
  | @cons u w y h r ih =>
    have hcol := h.2
    rw [Walk.snd_cons]
    rw [Walk.cons_isPath_iff] at hp
    rcases Nat.eq_zero_or_pos r.length with h0 | hpos
    · have hwy : w = y := Walk.eq_of_length_eq_zero h0
      subst hwy
      rw [Walk.length_cons, h0, zero_add]
      rcases hcol with hcol | hcol
      · simpa using hcol
      · exact absurd (by rwa [Sym2.eq_swap]) (hy u)
    · have hih := ih hy hp.1 hpos
      have hne : u ≠ r.snd := by
        intro he
        exact hp.2 (by rw [he]; exact r.getVert_mem_support 1)
      rw [Walk.length_cons]
      have hdiff : c.col s(u, w) ≠ c.col s(w, r.snd) := by
        intro he
        have h1 : c.col s(w, u) = c.col s(w, r.snd) := by rw [Sym2.eq_swap, he]
        exact hne (c.proper (h1.trans hih) hih)
      rcases Nat.mod_two_eq_zero_or_one r.length with hr | hr
      · have h1 : (r.length + 1) % 2 = 1 := by omega
        rw [hr] at hih
        simp only [zero_ne_one, ite_false] at hih
        rw [hih] at hdiff
        simp only [h1, ite_true]
        rcases hcol with hcol | hcol
        · exact hcol
        · exact absurd hcol hdiff
      · have h1 : (r.length + 1) % 2 = 0 := by omega
        rw [hr] at hih
        simp only [ite_true] at hih
        rw [hih] at hdiff
        simp only [h1, zero_ne_one, ite_false]
        rcases hcol with hcol | hcol
        · exact absurd hcol hdiff
        · exact hcol

/-- **Kőnig's extension step.** In a bipartite graph with at least `Δ(G)` colours, any uc
edge can be coloured after recolouring. -/
theorem step [Fintype V] [Fintype C] [DecidableRel G.Adj] (s : G.Coloring (Fin 2))
    (c : PC G C) (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col s(x, y) = none) : ∃ c' : PC G C, Ex c c' ∧ c'.col s(x, y) ≠ none := by
  classical
  obtain ⟨a, ha⟩ := free c hcard hadj hnone
  obtain ⟨b, hb⟩ := free c hcard hadj.symm (by rw [Sym2.eq_swap]; exact hnone)
  by_cases hay : c.Fr y a
  · exact ⟨c.se x y a hadj ha hay, se_ex c x y a hadj ha hay, by simp [se]⟩
  have hab : a ≠ b := fun h => hay (h ▸ hb)
  have hxy : ¬ (c.kg a b).Reachable y x := by
    rintro ⟨q⟩
    set p := q.toPath.1.reverse
    have hp : p.IsPath := q.toPath.2.reverse
    have hpar := par (fun u v (h : (c.kg a b).Adj u v) => h.2.elim (fun h => c.adj h) (fun h => c.adj h)) s p
    have hodd : p.length % 2 = 1 := by
      have hx := (s x).isLt
      have hy' := (s y).isLt
      have : (s x : ℕ) ≠ (s y : ℕ) := fun h => s.valid hadj (Fin.ext h)
      omega
    have hlen : 0 < p.length := by omega
    have := alt c hb p hp hlen
    simp only [hodd, ↓reduceIte] at this
    exact ha _ this
  set c1 := c.ks a b y with hc1
  have ha1 : c1.Fr x a := frN c hxy a ha
  have hay1 : c1.Fr y a := frR c (Reachable.refl y) a (by rwa [Equiv.swap_apply_left])
  exact ⟨c1.se x y a hadj ha1 hay1, (ks_ex c a b y).trans
    (se_ex c1 x y a hadj ha1 hay1), by simp [se]⟩

/-- The set of uc edges. -/
noncomputable def uc [Fintype V] [DecidableRel G.Adj] (c : PC G C) : Finset G.edgeSet :=
  univ.filter fun e => c.col e = none

/-- **Kőnig's theorem.** A finite bipartite graph has a total proper partial edge colouring with any
colour type of size at least `Δ(G)`. -/
theorem tot [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2)) (hcard : G.maxDegree ≤ Fintype.card C) :
    ∃ c : PC G C, ∀ e : G.edgeSet, c.col e ≠ none := by
  classical
  suffices H : ∀ k (c : PC G C), (uc c).card = k → ∃ c' : PC G C,
      Ex c c' ∧ ∀ u v, G.Adj u v → c'.col s(u, v) ≠ none by
    obtain ⟨c, -, h⟩ := H _ (_empty G C) rfl
    refine ⟨c, fun e => ?_⟩
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf u v => exact h u v he
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk
  by_cases htot : ∀ u v, G.Adj u v → c.col s(u, v) ≠ none
  · exact ⟨c, fun e h => h, htot⟩
  · push Not at htot
    obtain ⟨x, y, hxy, hnone⟩ := htot
    obtain ⟨c₁, hext, hc₁⟩ := step s c hcard hxy hnone
    refine (ih _ ?_ c₁ rfl).imp fun c₂ h => ⟨hext.trans h.1, h.2⟩
    rw [← hk]
    refine Finset.card_lt_card ⟨fun e he => ?_, fun hsub => ?_⟩
    · simp only [uc, mem_filter, mem_univ, true_and] at he ⊢
      by_contra hc
      exact (hext e hc) he
    · have h1 : (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ uc c₁ := hsub (by simp [uc, hnone])
      simp only [uc, mem_filter, mem_univ, true_and] at h1
      exact hc₁ h1

/-- **Kőnig's edge-colouring theorem.** The line graph of a finite bipartite graph is
`Δ(G)`-colourable. -/
theorem lgcol [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Colorable 2) : G.lineGraph.Colorable G.maxDegree := by
  classical
  obtain ⟨s⟩ := h
  obtain ⟨c, hc⟩ := tot (C := Fin G.maxDegree) s (by simp)
  let f : G.edgeSet → Fin G.maxDegree := fun e => Classical.choose (Option.ne_none_iff_exists'.mp (hc e))
  have hf : ∀ (a b : V) (hb : s(a, b) ∈ G.edgeSet), c.col s(a, b) = some (f ⟨s(a, b), hb⟩) :=
    fun a b hb => Classical.choose_spec (Option.ne_none_iff_exists'.mp (hc ⟨s(a, b), hb⟩))
  refine ⟨Coloring.mk f ?_⟩
  rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj hcol
  grind [PC.proper, SimpleGraph.lineGraph_adj_iff_exists, Sym2.mem_iff_exists]

end Galvin
