/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Connecting moves for four weights

The same finite family of moves normalizes each weight fiber and has size at most
twice the normalized width.
-/
@[expose] public noncomputable section

namespace SemigroupBetti

/-! ## Minimal escaping vectors

For a support `s`, consider exponents supported on `s` that admit a factorization using
a variable outside `s`. The minimal such exponents form a finite antichain
(Dickson's lemma). We keep one representative per degree with support exactly `s`.
-/
open Finset Finsupp

abbrev I := Fin 4
abbrev V := I →₀ ℕ
abbrev Mask := Finset I

variable (n : Fin 4 → ℕ) (s : Mask) (d : ℕ)

/-- Width divided by the common divisor of the three offsets from the first weight. -/
def normalizedWidth : ℕ :=
  (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0))

abbrev Fiber := {u : V // u.weight n = d}

/-- The degree of `u` can be realized using a variable outside `s`. -/
def Esc (u : V) := ∃ v : V, v.weight n = u.weight n ∧ ¬ v.support ⊆ s

@[mk_iff] structure Atom (x : V) : Prop where
  deg : x.weight n = d
  mask : x.support = s
  min : Minimal (Esc n s) x

def degrees :=
  let atoms := WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (Esc n s))
  (atoms.toFinset.filter (support · = s)).image (weight n)

def pick := Classical.epsilon (Atom n s d)

/-- Prefer non-singleton supports; between disjoint pairs, prefer the one without `1`. -/
def priority (s : Mask) := if s.Nontrivial then if 1 ∈ s then 1 else 0 else 2
abbrev Preferred := MinimalFor (fun x : V => x.weight n = d) (priority ∘ support)
def root : V := Classical.epsilon (Preferred n d)

abbrev Cut := Mask × Mask

-- Orient all three pair partitions with `1` on the left. A singleton spoke repeats
-- its one support, so it fits the same indexing scheme.
abbrev partition (i j k : I) : Cut := ({1, i}, {j, k})
abbrev P := partition 0 2 3
abbrev Q := partition 3 2 0
abbrev E := partition 2 0 3
abbrev spoke (i : I) : Cut := ({i}, {i})
abbrev cuts : Finset Cut := {spoke 0, spoke 1, spoke 2, spoke 3, P, Q, E}
abbrev cutDegrees (c : Cut) := degrees n c.1 ∩ degrees n c.2

/-- Each label prescribes a move from the chosen left-side exponent to the degree root. -/
def labels := cuts.sigma (cutDegrees n)

variable {n s d}

lemma root_spec (x : Fiber n d) : Preferred n d (root n d) :=
  Classical.epsilon_spec (exists_minimalFor_of_wellFoundedLT _ _ ⟨x.val, x.prop⟩)

lemma mem_degrees : d ∈ degrees n s ↔ ∃ x, Atom n s d x := by
  simp [degrees, atom_iff, and_comm]

lemma pick_spec (h : d ∈ degrees n s) : Atom n s d (pick n s d) :=
  Classical.epsilon_spec (mem_degrees.mp h)

/-! ## Connecting a fiber

Think of equality modulo the proposed relations as a coloring. In a least
multicolored degree, sharing a variable forces two vectors to have the same
color. Choose representatives of root and non-root colors, preferring non-singletons.
A singleton non-root support is joined to the root by a spoke. Otherwise the
representatives fill a pair partition, with `1` on the non-root side.
-/

/-- Allowed supports, as seen from the preferred representatives `a` (non-root) and
`b` (root). A cut is clear when no allowed support crosses it. -/
private abbrev Fits (a b c : Mask) :=
  Disjoint c a ∨ Disjoint c b ∧ priority a ≤ priority c
private abbrev Clear (a b t : Mask) := ∀ c, Fits a b c → c ⊆ t ∨ Disjoint c t

/-- Classification on the sixteen masks, independent of the weights or degree. -/
private lemma four_cases : ∀ {a b : Mask}, ¬ a ⊆ b → priority b ≤ priority a →
    Disjoint a b → Clear a b a ∧
    ((a, a) ∈ cuts ∨ Clear a b b ∧ (a, b) ∈ cuts) := by decide

/-- Any additive assignment that respects the moves is constant on fibers. -/
lemma normal_form {M : Type*} [AddMonoid M] (f : V →+ M)
    (hn : ∀ i, 0 < n i)
    (hm : ∀ j : labels n, f (pick n j.val.1.1 j.val.2) = f (root n j.val.2))
    (x : Fiber n d) : f x = f (root n d) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have step {i : I} (a : Fiber n d) (h : a.val i ≠ 0) :
        f a = f (root n (d - n i)) + f (single i 1) := by
      have := (weight_sub_single_add (w := n) h).trans a.prop
      have := hn i
      rw [← ih (d - n i) (by omega) ⟨a.val - single i 1, by omega⟩, ← map_add,
        sub_add_single_one_cancel h]
    have sep {a b : Fiber n d} (h : f a ≠ f b) : Disjoint a.val.support b.val.support := by
      simp only [disjoint_left, mem_support_iff]
      exact fun i ha hb => h ((step a ha).trans (step b hb).symm)
    -- Inclusion of supports also gives agreement: the only disjoint inclusion
    -- starts with the zero vector, whose fiber is a singleton.
    have same {u v : Fiber n d} (sub : u.val.support ⊆ v.val.support) : f u = f v := by
      by_contra h
      let := nonTorsionWeight_of ℕ n (fun i => (hn i).ne')
      have := (sep h).eq_bot_of_le sub
      have := v.prop.trans u.prop.symm
      simp_all [weight_eq_zero_iff_eq_zero]
    have largest := root_spec x
    let r : Fiber n d := ⟨_, largest.prop⟩
    by_contra bad
    obtain ⟨a, best⟩ := exists_minimalFor_of_wellFoundedLT (fun z : Fiber n d => f z ≠ f r)
      (fun z => priority z.val.support) ⟨x, bad⟩
    have hne := best.prop
    have valid (w : Fiber n d) : Fits a.val.support r.val.support w.val.support := by
      have := best.le (j := w)
      grind only [@sep w a, @sep w r]
    -- A clear side with a different color across from it supplies a move degree.
    have side {u v : Fiber n d} (h : f u ≠ f v)
        (cl : Clear a.val.support r.val.support u.val.support) :
        d ∈ degrees n u.val.support := by
      refine mem_degrees.mpr ⟨_, u.prop, rfl, ⟨v, v.prop.trans u.prop.symm, mt same h.symm⟩, ?_⟩
      rintro x ⟨y, hy, out⟩ hle
      obtain ⟨t, ht⟩ := exists_add_of_le hle
      -- Reattaching a nonzero remainder to the escape would cross the cut.
      have cut := cl _ (valid ⟨y + t, by simpa [ht, hy] using u.prop⟩)
      simp_all [support_add_eq_union, disjoint_union_left, disjoint_union_right, union_subset_iff]
    obtain ⟨cl, cs⟩ := four_cases (mt same hne) (largest.le a.prop) (sep hne)
    have ea := side hne cl
    have pa := pick_spec ea
    apply hne
    rw [same (v := ⟨_, pa.deg⟩) pa.mask.ge]
    rcases cs with h | ⟨cr, h⟩ <;>
      refine hm ⟨⟨_, d⟩, mem_sigma.mpr ⟨h, mem_inter.mpr ⟨ea, ?_⟩⟩⟩
    exacts [ea, side hne.symm cr]

/-! ## Counting on a side

A two-coordinate antichain injects into either coordinate. If `u` admits an
escape, no selected vector strictly dominates `u`: we can count the vectors
in the strips `x i < u i` and `x j ≤ u j` separately.
-/
variable {x y u : V} {e : ℕ}

/-- An escaping corner rules out its entire upper-right quadrant, apart from itself. -/
lemma Atom.blocked (hd : Atom n s d x) (hu : Esc n s u) :
    x = u ∨ ∃ i ∈ u.support, x i < u i := by
  by_contra! h
  exact h.1 (hd.min.eq_of_ge hu (fun i => by grind))

lemma descent (hd : d ∈ degrees n s) (he : e ∈ degrees n s) :
    d = e ∨ ∃ i ∈ s, pick n s e i < pick n s d i := by
  have a := pick_spec hd
  have b := pick_spec he
  grind [b.blocked a.min.prop, a.mask, a.deg, b.deg]

/-- Encode a degree by its first coordinate in the low strip or its second
coordinate in the other strip. Descent in both directions makes each tag injective. -/
lemma strips (c : Cut) (i j : I) (eq : y.weight n = u.weight n)
    (hF : cutDegrees n c ⊆ degrees n {i, j} := by
      apply_rules [inter_subset_left, inter_subset_right])
    (supports : u.support ⊆ {i, j} ∧ ¬ y.support ⊆ {i, j} := by
      norm_num [subset_iff, Fin.forall_fin_succ, Finsupp.single_apply] <;> omega) :
    #(cutDegrees n c) ≤ u i - 1 + (if u.weight n ∈ cutDegrees n c then u j else u j - 1) := by
  set F := cutDegrees n c
  let v := pick n {i, j}
  let enc (d : ℕ) : ℕ ⊕ ℕ := if v d i < u i then .inl (v d i) else .inr (v d j)
  set b := if u.weight n ∈ F then u j else u j - 1
  have bound := card_le_card_of_injOn enc (s := F)
    (t := (Icc 1 (u i - 1)).disjSum (Icc 1 b)) ?_ ?_
  · simpa using bound
  · intro d hd
    have ha := pick_spec (hF hd)
    have full := ha.mask.ge
    simp [insert_subset_iff] at full
    rcases ha.blocked ⟨y, eq, supports.2⟩ with rfl | hrect <;>
      dsimp only [enc, b] <;> split_ifs <;> simp <;> grind [ha.deg, supports.1]
  · intro d hd e he
    dsimp [enc, v]
    grind [descent]

/-! ## The width bound

Let `a, b, c` be the consecutive normalized gaps. Write `p, q, e` for the
numbers of degrees of the three pair cuts. The pure relation at variable 1 gives
`p, q ≤ a + b - 1`, and the rectangle on the interior side gives `e ≤ c + a - 1`.

The relation at variable 2 gives `p + q ≤ 2 * (b + c) - 3`: in counting the
13 rectangle for `q`, either the degree of the corner `(c, b)` is missing or a 2
cancels from its representative on 02, shortening the pure bound for `p` by one. Taking
the better bound on `p + q` gives `4 + p + q + e ≤ 2 * (a + b + c)`.
-/
lemma normalized_count (hm : StrictMono n) : #(labels n) ≤ 2 * normalizedWidth n := by
  have singles (i : I) : #(degrees n {i}) ≤ 1 := by
    rw [card_le_one]
    grind [descent]
  have gaps := Fin.strictMono_iff_lt_succ.mp hm
  norm_num [Fin.forall_fin_succ] at gaps
  unfold normalizedWidth
  set g := Nat.gcd _ _
  -- Factor the three differences by their common divisor.
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨⟨a, ha⟩, ⟨A, hA⟩, W, hW⟩ := (Nat.dvd_gcd_iff.mp (dvd_refl g)).imp_right Nat.dvd_gcd_iff.mp
  have chain : 0 < g * a ∧ g * a < g * A ∧ g * A < g * W := by omega
  simp only [Nat.mul_pos_iff_of_pos_left hg, Nat.mul_lt_mul_left hg] at chain
  obtain ⟨b, hb, rfl⟩ := exists_pos_add_of_lt chain.2.1
  obtain ⟨c, hc, rfl⟩ := exists_pos_add_of_lt chain.2.2
  rw [hW, Nat.mul_div_cancel_left _ hg]
  simp only [Nat.sub_eq_iff_eq_add (hm.monotone (Fin.zero_le _))] at ha hA hW
  -- Two pure trades and the trade between the interior pair and the endpoints.
  obtain ⟨id₁, id₂, id₃⟩ : weight n (single 0 b + single 2 a) = weight n (single 1 (a + b)) ∧
      weight n (single 1 c + single 3 b) = weight n (single 2 (b + c)) ∧
      weight n (single 0 c + single 3 a) = weight n (single 1 c + single 2 a) := by
    simp [weight_single, ha, hA, hW]; ring_nf; trivial
  have p₁ := strips P 1 0 id₁
  have q₁ := strips Q 1 3 id₁
  have p₂ := strips P 2 3 id₂
  have e := strips E 1 2 id₃
  have q := strips Q 1 3 id₂.symm
  norm_num [id₂, weight_single, Finsupp.single_apply] at p₁ q₁ p₂ e q
  split at q
  case' isTrue hit =>
    obtain ⟨z, hr⟩ := mem_degrees.mp hit.2
    -- Cancel a 2 from the 02 representative of the pure degree; its 0 survives.
    have full := hr.mask.ge
    simp only [insert_subset_iff, singleton_subset_iff, mem_support_iff] at full
    have hrel := weight_sub_single_add (w := n) full.1
    rw [hr.deg] at hrel
    have eq : weight n (z - single 2 1) = weight n (single 2 (b + c - 1)) := by
      rw [weight_single, smul_eq_mul, Nat.sub_mul, add_mul]; omega
    have small := strips P 2 3 eq
    norm_num [Finsupp.single_apply] at small
  all_goals
    split at e <;> simp +decide [labels, cuts] <;> grind

end SemigroupBetti
