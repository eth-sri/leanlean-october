module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvHFacts

/-!
# Down-phase driver, host RAM (D3a), part 2: host items in memory

* `ItemsAt m T xs`: the items `xs` at `T`, three words each (kind, two arguments), as in
  `HostAt` (which is a count word followed by `ItemsAt`, `hostAt_of`);
* `wr3`: writing one item (`ItemsAt.snoc`);
* `ptsLen n xs`: the number of symbolic points of a list of items;
* `ptE`: the host point written by the RAM (`ptI` is an instance, `ptI_eq`);
* the prefix `pre li n N r t` of `walkItems` (`pre_succ`, `pre_full`) and the size bounds.
-/

namespace Chazelle.Core

namespace DrvH

@[expose] public section

open DrvR

/-! ## Encoding of items -/

/-- The kind word of an item. -/
def encK : HostItem → ℕ
  | .run _ _ => 0
  | .pt (.vtx _) => 1
  | .pt (.onEdge _ _) => 2

/-- The first argument word of an item. -/
def encA : HostItem → ℕ
  | .run a _ => a
  | .pt (.vtx j) => j
  | .pt (.onEdge e _) => e

/-- The second argument word of an item. -/
def encB : HostItem → ℕ
  | .run _ ℓ => ℓ
  | .pt (.vtx _) => 0
  | .pt (.onEdge _ h) => h

/-- **Items in memory**: item `i` of `xs` at `T + 3 i` (kind, two arguments). -/
def ItemsAt (m : ℕ → ℕ) (T : ℕ) (xs : List HostItem) : Prop :=
  ∀ i, i < xs.length →
    m (T + 3 * i) = encK (xs.getD i (.run 0 0)) ∧ m (T + 3 * i + 1) = encA (xs.getD i (.run 0 0)) ∧
      m (T + 3 * i + 2) = encB (xs.getD i (.run 0 0))

/-- Write three words. -/
def wr3 (m : ℕ → ℕ) (p a b c : ℕ) : ℕ → ℕ := upd (upd (upd m p a) (p + 1) b) (p + 2) c

theorem wr3_lt {m : ℕ → ℕ} {p a b c x : ℕ} (hx : x < p) : wr3 m p a b c x = m x := by
  unfold wr3
  rw [Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ (by omega),
    Machine.upd_other _ _ _ (⋄)]

theorem ItemsAt.nil (m : ℕ → ℕ) (T : ℕ) : ItemsAt m T [] := fun i hi => by simp at hi

/-- **Appending an item** written at the end. -/
theorem ItemsAt.snoc {m : ℕ → ℕ} {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (it : HostItem) :
    ItemsAt (wr3 m (T + 3 * xs.length) (encK it) (encA it) (encB it)) T (xs ++ [it]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  unfold wr3
  rcases Nat.lt_or_ge i xs.length with h1 | h1
  · Ξ List.getD_append _ _ _ _ h1
    obtain ⟨a1, a2, a3⟩ := h i h1
    refine ⟨?_, ?_, ?_⟩
    · rw [Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (⋄), a1]
    · rw [Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (⋄), a2]
    · rw [Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (⋄), a3]
  · have hi' : i = xs.length := ⋄
    subst hi'
    Ξ List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self
    ϴ List.getD_cons_zero
    refine ⟨?_, ?_, ?_⟩
    · rw [Machine.upd_other _ _ _ (⋄), Machine.upd_other _ _ _ (by omega),
        Machine.upd_same]
    · rw [Machine.upd_other _ _ _ (⋄), Machine.upd_same]
    · Ξ Machine.upd_same

/-- Items survive a change of the memory outside their words. -/
theorem ItemsAt.congr {m m' : ℕ → ℕ} {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (hm : ∀ a, T ≤ a → a < T + 3 * xs.length → m' a = m a) : ItemsAt m' T xs := by
  intro i hi
  obtain ⟨a1, a2, a3⟩ := h i hi
  exact ⟨by rw [hm _ (⋄) (by omega), a1], by rw [hm _ (by omega) (by omega), a2],
    by rw [hm _ (⋄) (by omega), a3]⟩

/-- **The host layout** is the count word followed by the items. -/
theorem hostAt_of {m : ℕ → ℕ} {B : ℕ} {H : Host} (h0 : m B = H.length) (h : ItemsAt m (B + 1) H) :
    HostAt m B H := by
  refine ⟨h0, fun i hi => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h i hi
  rw [show B + 1 + 3 * i + 1 = B + 2 + 3 * i by ring,
    show B + 1 + 3 * i + 2 = B + 3 + 3 * i by ring] at *
  generalize H.getD i (.run 0 0) = it at a1 a2 a3
  rcases it with ⟨a, l⟩ | ⟨j⟩ | ⟨e, hh⟩
  · exact ⟨a1, a2, a3⟩
  · exact ⟨a1, a2⟩
  · exact ⟨a1, a2, a3⟩

/-- The reversal of items, read one by one. -/
theorem getD_reverse_items {xs : List HostItem} {i : ℕ} (hi : i < xs.length) :
    xs.reverse.getD i (.run 0 0) = xs.getD (xs.length - 1 - i) (.run 0 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_reverse,
    List.getD_eq_getElem _ _ (⋄)]

/-! ## Point counts -/

/-- The number of symbolic points of a list of items. -/
def ptsLen (n : ℕ) (xs : List HostItem) : ℕ := (Host.pts n xs).length

theorem ptsLen_nil (n : ℕ) : ptsLen n [] = 0 := rfl

theorem ptsLen_append (n : ℕ) (xs ys : List HostItem) :
    ptsLen n (xs ++ ys) = ptsLen n xs + ptsLen n ys := by
  Θ ptsLen, Host.pts, List.flatMap_append

theorem ptsLen_pt (n : ℕ) (x : SymPt) : ptsLen n [.pt x] = 1 := by
  Θ ptsLen, Host.pts, HostItem.pts

theorem ptsLen_run (n a l : ℕ) : ptsLen n [.run a l] = l + 1 := by
  Θ ptsLen, Host.pts, HostItem.pts

theorem ptsLen_reverse (n : ℕ) (xs : List HostItem) : ptsLen n xs.reverse = ptsLen n xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    Ξ List.reverse_cons, ptsLen_append, ih, show x :: xs = [x] ++ xs from rfl, ptsLen_append
    omega

/-! ## The points written by the RAM -/

/-- The host point written by the RAM: edge `qE li n e`, height `h - 1`. -/
def ptE (li : Bool) (n e h : ℕ) : HostItem := .pt (.onEdge (qE li n e) (h - 1))

/-! ## The prefixes of the walk items -/

/-- The items of the arc loop's iteration `t` (arc `arcs[t]` and its successor). -/
def arcIt (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) : List HostItem :=
  arcItems li n N r ((N.region r).arcs.getD t 0)
    ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)

/-- The items written by the first `t` iterations of the arc loop. -/
def pre (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) : List HostItem :=
  (List.range t).flatMap (arcIt li n N r)

theorem pre_succ (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) :
    pre li n N r (t + 1) = pre li n N r t ++ arcIt li n N r t := by
  Θ pre, List.range_succ, List.flatMap_append

theorem pre_full (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    pre li n N r (N.region r).arcs.length = walkItems li n N r := rfl

theorem runItems_length_le (li : Bool) (n : ℕ) (s e : WPos) : (runItems li n s e).length ≤ 1 := by
  unfold runItems; split_ifs <;> simp

theorem arcItems_length_le (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).length ≤ 4 := by
  unfold arcItems
  have := runItems_length_le li n (N.arc j).s (N.arc j).e
  ϴ List.length_append, List.length_singleton
  split_ifs <;> simp <;> omega

theorem pre_length_le (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) :
    (pre li n N r t).length ≤ 4 * t := by
  induction t with
  | zero => simp [pre]
  | succ t ih =>
    Ξ pre_succ, List.length_append
    have := arcItems_length_le li n N r ((N.region r).arcs.getD t 0)
      ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)
    unfold arcIt
    omega

theorem runCnt_lt (li : Bool) {n : ℕ} (hn : 0 < n) (s e : WPos) : runCnt li n s e < n :=
  Nat.mod_lt _ hn

theorem ptsLen_runItems (li : Bool) {n : ℕ} (_hn : 0 < n) (s e : WPos) :
    ptsLen n (runItems li n s e) = runCnt li n s e := by
  unfold runItems
  split_ifs with h0 h1
  · rw [h0]; rfl
  · rw [ptsLen_run]; omega
  · rw [ptsLen_run]; omega

theorem ptsLen_arcItems_le (li : Bool) {n : ℕ} (hn : 0 < n) (N : NF) (r jp j : ℕ) :
    ptsLen n (arcItems li n N r jp j) ≤ n + 3 := by
  unfold arcItems
  have h1 := ptsLen_runItems li hn (N.arc j).s (N.arc j).e
  have h2 := runCnt_lt li hn (N.arc j).s (N.arc j).e
  have h3 : ∀ x b, ptsLen n [ptI li n x b] = 1 := fun x b => ptsLen_pt n _
  split_ifs <;> simp only [ptsLen_append, h3, List.nil_append] <;> omega

theorem ptsLen_pre_le (li : Bool) {n : ℕ} (hn : 0 < n) (N : NF) (r t : ℕ) :
    ptsLen n (pre li n N r t) ≤ (n + 3) * t := by
  induction t with
  | zero => simp [pre, ptsLen_nil]
  | succ t ih =>
    Ξ pre_succ, ptsLen_append
    have := ptsLen_arcItems_le li hn N r ((N.region r).arcs.getD t 0)
      ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)
    unfold arcIt
    Ξ Nat.mul_succ
    omega

end

end DrvH

end Chazelle.Core
