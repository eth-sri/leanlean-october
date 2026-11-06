module

public meta import Chazelle.Arithmetic

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

section
variable (m : ℕ → ℕ)
include m
/-- **Items in memory**: item `i` of `xs` at `T + 3 i` (kind, two arguments). -/
def ItemsAt (T : ℕ) (xs : List HostItem) : Prop :=
  ∀ i, i < xs.length →
    m (T + 3 * i) = encK (xs.getD i (.run 0 0)) ∧ m (T + 3 * i + 1) = encA (xs.getD i (.run 0 0)) ∧
      m (T + 3 * i + 2) = encB (xs.getD i (.run 0 0))

/-- Write three words. -/
def wr3 (p a b c : ℕ) : ℕ → ℕ := upd (upd (upd m p a) (p + 1) b) (p + 2) c


end

theorem wr3_lt {m : ℕ → ℕ} {p a b c x : ℕ} (hx : x < p) : wr3 m p a b c x = m x := by
  unfold wr3
  ram_all 

theorem ItemsAt.nil (m : ℕ → ℕ) (T : ℕ) : ItemsAt m T [] := fun i hi => by simp at hi

/-- **Appending an item** written at the end. -/
theorem ItemsAt.snoc {m : ℕ → ℕ} {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (it : HostItem) :
    ItemsAt (wr3 m (T + 3 * xs.length) (encK it) (encA it) (encB it)) T (xs ++ [it]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  unfold wr3
  rcases Nat.lt_or_ge i xs.length with h1 | h1
  · rw [List.getD_append _ _ _ _ h1]
    obtain ⟨a1, a2, a3⟩ := h i h1
    refine ⟨?_, ?_, ?_⟩
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), a1]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), a2]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), a3]
  · have hi' : i = xs.length := by omega
    simp_all

/-- Items survive a change of the memory outside their words. -/
theorem ItemsAt.congr {m m' : ℕ → ℕ} {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (hm : ∀ a, T ≤ a → a < T + 3 * xs.length → m' a = m a) : ItemsAt m' T xs := by
  core_grind

/-- **The host layout** is the count word followed by the items. -/
theorem hostAt_of {m : ℕ → ℕ} {B : ℕ} {H : Host} (h0 : m B = H.length) (h : ItemsAt m (B + 1) H) :
    HostAt m B H := by
  refine ⟨h0, fun i hi => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h i hi
  rw [show B + 1 + 3 * i + 1 = B + 2 + 3 * i by ring,
    show B + 1 + 3 * i + 2 = B + 3 + 3 * i by ring] at *
  generalize H.getD i (.run 0 0) = it at a1 a2 a3
  rcases it with ⟨a, l⟩ | ⟨j⟩ | ⟨e, hh⟩
  all_goals aesop


/-! ## Point counts -/

/-- The number of symbolic points of a list of items. -/
def ptsLen (n : ℕ) (xs : List HostItem) : ℕ := (Host.pts n xs).length

section
variable (n : ℕ)
theorem ptsLen_nil : ptsLen n [] = 0 := rfl

theorem ptsLen_append (xs ys : List HostItem) :
    ptsLen n (xs ++ ys) = ptsLen n xs + ptsLen n ys := by
  simp [ptsLen, Host.pts, List.flatMap_append]

theorem ptsLen_pt (x : SymPt) : ptsLen n [.pt x] = 1 := by
  aesop


end

theorem ptsLen_run (n a l : ℕ) : ptsLen n [.run a l] = l + 1 := by
  simp [ptsLen, Host.pts, HostItem.pts]

theorem ptsLen_reverse (n : ℕ) (xs : List HostItem) : ptsLen n xs.reverse = ptsLen n xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, ptsLen_append, ih, show x :: xs = [x] ++ xs from rfl, ptsLen_append]
    omega

/-! ## The points written by the RAM -/

/-- The host point written by the RAM: edge `qE li n e`, height `h - 1`. -/
def ptE (li : Bool) (n e h : ℕ) : HostItem := .pt (.onEdge (qE li n e) (h - 1))

/-! ## The prefixes of the walk items -/

section
variable (li : Bool) (n : ℕ) (N : NF) (r t : ℕ)
include li n N r t
/-- The items of the arc loop's iteration `t` (arc `arcs[t]` and its successor). -/
def arcIt : List HostItem :=
  arcItems li n N r ((N.region r).arcs.getD t 0)
    ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)

/-- The items written by the first `t` iterations of the arc loop. -/
def pre : List HostItem :=
  (List.range t).flatMap (arcIt li n N r)


end

section
variable (li : Bool) (n : ℕ)
theorem pre_succ (N : NF) (r t : ℕ) :
    pre li n N r (t + 1) = pre li n N r t ++ arcIt li n N r t := by
  simp [pre, List.range_succ, List.flatMap_append]

theorem pre_full (N : NF) (r : ℕ) :
    pre li n N r (N.region r).arcs.length = walkItems li n N r := rfl

theorem runItems_length_le (s e : WPos) : (runItems li n s e).length ≤ 1 := by
  grind [runItems]

theorem arcItems_length_le (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).length ≤ 4 := by
  unfold arcItems
  have := runItems_length_le li n (N.arc j).s (N.arc j).e
  grind

theorem pre_length_le (N : NF) (r t : ℕ) :
    (pre li n N r t).length ≤ 4 * t := by
  induction t with
  | zero => simp [pre]
  | succ t ih =>
    rw [pre_succ, List.length_append]
    grind [Chazelle.Core.DrvH.arcItems_length_le, arcIt]


end

section
variable (li : Bool) {n : ℕ}
theorem runCnt_lt (hn : 0 < n) (s e : WPos) : runCnt li n s e < n :=
  Nat.mod_lt _ hn

theorem ptsLen_runItems (_hn : 0 < n) (s e : WPos) :
    ptsLen n (runItems li n s e) = runCnt li n s e := by
  unfold runItems
  split_ifs with h0 h1
  · rw [h0]; rfl
  · grind [ptsLen_run]
  grind [ptsLen_run]

section
variable (hn : 0 < n) (N : NF)
include hn N
theorem ptsLen_arcItems_le (r jp j : ℕ) :
    ptsLen n (arcItems li n N r jp j) ≤ n + 3 := by
  unfold arcItems
  have h1 := ptsLen_runItems li hn (N.arc j).s (N.arc j).e
  have h2 := runCnt_lt li hn (N.arc j).s (N.arc j).e
  have h3 : ∀ x b, ptsLen n [ptI li n x b] = 1 := fun x b => ptsLen_pt n _
  grind [ptsLen_append, List.nil_append]

theorem ptsLen_pre_le (r t : ℕ) :
    ptsLen n (pre li n N r t) ≤ (n + 3) * t := by
  induction t with
  | zero => aesop
  | succ t ih =>
    rw [pre_succ, ptsLen_append]
    have := ptsLen_arcItems_le li hn N r ((N.region r).arcs.getD t 0)
      ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)
    unfold arcIt
    grind



end

end

end

end DrvH

end Chazelle.Core
