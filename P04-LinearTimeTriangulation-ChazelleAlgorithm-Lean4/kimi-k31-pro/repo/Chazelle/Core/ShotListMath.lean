module

public import Chazelle.Core.WalkEmbed
public import Chazelle.SimpTactics
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

/-!
# Shooting at a list of arcs with holes, part 1: cutting cyclic intervals

A shot at the arcs of a region must avoid the walk edges through the origin (`ShooterOK` forbids
an origin on the target subarc).  The caller names **holes**: open cyclic key intervals `(x, y)`
between two walk vertices (the open edge `(p, p + 1)` for an origin inside the edge `p`, the pair
of edges `(p - 1, p + 1)` for an origin at the vertex `p`).  Every arc (a closed cyclic key interval
`[a, b]`, the whole walk when `a = b`) is cut by the holes, one after the other, into closed
pieces.

* `CIn a b k`: `k` lies in the closed cyclic interval `[a, b]`.
* `cut1 key a b x y`: the pieces of `[a, b]` outside the open hole `(x, y)` (at most two).
* `cut1_open` (P0): the open interval of a piece lies in the open interval of the arc (so the
  weight of a piece is at most that of the arc);
* `cut1_sub` (P1): a piece lies in the arc and outside the open hole;
* `cut1_cover` (P2): a key of the arc outside the closed hole lies in a piece.
* `leaves`: the pieces after a list of holes, with `leaves_open`, `leaves_sub`, `leaves_cover`.

All statements are order-theoretic facts about real numbers (no range assumptions).
-/

namespace Chazelle.Core

namespace ShotList

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- `k` lies in the closed cyclic interval `[a, b]` (the whole circle when `a = b`). -/
def CIn (a b k : ℝ) : Prop := sideInArc a b k ∨ k = a ∨ k = b

/-- **The pieces of the arc `[a, b]` outside the open hole `(x, y)`**, from the keys
`ka kb kx ky` of the four ends. -/
noncomputable def cutK {α : Type} (ka kb kx ky : ℝ) (a b x y : α) : List (α × α) := by
  classical
  exact
    if sideInArc kx ky ka then
      (if sideInArc ka kb ky then
        (if sideInArc ky kb kx then [(y, x)] else [(y, b)])
      else [])
    else if sideInArc ka kb kx then
      (a, x) :: (if sideInArc kx kb ky then [(y, b)] else [])
    else if kx = ka then
      (if sideInArc ka kb ky then [(y, b)] else [])
    else [(a, b)]

/-- **The pieces of the arc `[a, b]` outside the open hole `(x, y)`.** -/
noncomputable def cut1 {α : Type} (key : α → ℝ) (a b x y : α) : List (α × α) :=
  cutK (key a) (key b) (key x) (key y) a b x y

/-- The pieces of `cut1`, as key pairs. -/
theorem cut1_cases {α : Type} (key : α → ℝ) (a b x y : α) {u v : α}
    (h : (u, v) ∈ cut1 key a b x y) :
    (sideInArc (key x) (key y) (key a) ∧ sideInArc (key a) (key b) (key y) ∧
        sideInArc (key y) (key b) (key x) ∧ u = y ∧ v = x) ∨
      (sideInArc (key x) (key y) (key a) ∧ sideInArc (key a) (key b) (key y) ∧
        ¬ sideInArc (key y) (key b) (key x) ∧ u = y ∧ v = b) ∨
      (¬ sideInArc (key x) (key y) (key a) ∧ sideInArc (key a) (key b) (key x) ∧ u = a ∧ v = x) ∨
      (¬ sideInArc (key x) (key y) (key a) ∧ sideInArc (key a) (key b) (key x) ∧
        sideInArc (key x) (key b) (key y) ∧ u = y ∧ v = b) ∨
      (¬ sideInArc (key x) (key y) (key a) ∧ ¬ sideInArc (key a) (key b) (key x) ∧
        key x = key a ∧ sideInArc (key a) (key b) (key y) ∧ u = y ∧ v = b) ∨
      (¬ sideInArc (key x) (key y) (key a) ∧ ¬ sideInArc (key a) (key b) (key x) ∧
        key x ≠ key a ∧ u = a ∧ v = b) := by
  unfold cut1 cutK at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;>
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  · exact Or.inl ⟨h1, h2, h3, h.1, h.2⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3, h.1, h.2⟩)
  · rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h4, h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h4, h5, h.1, h.2⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h4, h.1, h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h4, h6, h7, h.1, h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h4, h6, h.1, h.2⟩))))

/-! ## Transfer to ranks

A statement built from order comparisons of five reals holds as soon as it holds for their ranks
(naturals below `5`), where it is decided. -/

/-- The cyclic interval test on naturals. -/
def siaN (a b k : ℕ) : Bool := if a < b then a < k && k < b else a < k || k < b

/-- The closed cyclic interval test on naturals. -/
def CInN (a b k : ℕ) : Bool := siaN a b k || k == a || k == b

/-- The rank of `v` among the elements of `L`. -/
noncomputable def rank (L : List ℝ) (v : ℝ) : ℕ := (L.filter (fun w => decide (w < v))).length

theorem rank_lt_of_lt {L : List ℝ} {v w : ℝ} (hv : v ∈ L) (h : v < w) : rank L v < rank L w := by
  unfold rank
  induction L with
  | nil => simp at hv
  | cons z L ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hv with rfl | hv'
    · simp only [lt_irrefl, decide_false, h, decide_true]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have : (L.filter (fun u => decide (u < v))).length ≤
          (L.filter (fun u => decide (u < w))).length :=
        List.Sublist.length_le (List.monotone_filter_right L (fun u hu => by
          simp only [decide_eq_true_eq] at hu ⊢; exact hu.trans h))
      omega
    · have := ih hv'
      by_cases h1 : z < v
      · have h2 : z < w := h1.trans h
        sio only [h1, h2, decide_true, ↓reduceIte, List.length_cons]
      · by_cases h2 : z < w
        · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
            List.length_cons]; omega
        · simp only [h1, h2, decide_false, Bool.false_eq_true, ↓reduceIte]; exact this

theorem rank_lt_iff {L : List ℝ} {v w : ℝ} (hv : v ∈ L) (hw : w ∈ L) :
    v < w ↔ rank L v < rank L w := by
  constructor
  · exact rank_lt_of_lt hv
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · exact absurd (rank_lt_of_lt hw h'') (by omega)
    · rw [h''] at h; exact lt_irrefl _ h

theorem rank_eq_iff {L : List ℝ} {v w : ℝ} (hv : v ∈ L) (hw : w ∈ L) :
    v = w ↔ rank L v = rank L w := by
  constructor
  · rintro rfl; rfl
  · intro h
    rcases lt_trichotomy v w with h' | h' | h'
    · exact absurd h ((rank_lt_of_lt hv h').ne)
    · exact h'
    · exact absurd h ((rank_lt_of_lt hw h').ne')

theorem rank_lt_length (L : List ℝ) (v : ℝ) : rank L v ≤ L.length :=
  List.length_filter_le _ _

theorem sideInArc_rank {L : List ℝ} {a b k : ℝ} (ha : a ∈ L) (hb : b ∈ L) (hk : k ∈ L) :
    sideInArc a b k ↔ siaN (rank L a) (rank L b) (rank L k) = true := by
  unfold sideInArc siaN
  have e1 := rank_lt_iff ha hb
  have e2 := rank_lt_iff ha hk
  have e3 := rank_lt_iff hk hb
  by_cases h : a < b
  · have h' := e1.1 h
    simp only [h, h', ↓reduceIte, e2, e3, Bool.and_eq_true, decide_eq_true_eq]
  · have h' : ¬ rank L a < rank L b := fun h' => h (e1.2 h')
    simp only [h, h', ↓reduceIte, e2, e3, Bool.or_eq_true, decide_eq_true_eq]

theorem cIn_rank {L : List ℝ} {a b k : ℝ} (ha : a ∈ L) (hb : b ∈ L) (hk : k ∈ L) :
    CIn a b k ↔ CInN (rank L a) (rank L b) (rank L k) = true := by
  unfold CIn CInN
  rw [sideInArc_rank ha hb hk, rank_eq_iff hk ha, rank_eq_iff hk hb]
  simp [Bool.or_eq_true, or_assoc]

/-! ## The order facts, decided on ranks -/

/-- Boolean implication. -/
def imp (p q : Bool) : Bool := !p || q

/-- P1 on ranks: each piece lies in the arc and outside the open hole. -/
def P1N (A B X Y K : ℕ) : Bool :=
  imp (X != Y) (
    imp (siaN X Y A && siaN A B Y && siaN Y B X && CInN Y X K) (CInN A B K && !siaN X Y K) &&
    imp (siaN X Y A && siaN A B Y && !siaN Y B X && CInN Y B K) (CInN A B K && !siaN X Y K) &&
    imp (!siaN X Y A && siaN A B X && CInN A X K) (CInN A B K && !siaN X Y K) &&
    imp (!siaN X Y A && siaN A B X && siaN X B Y && CInN Y B K) (CInN A B K && !siaN X Y K) &&
    imp (!siaN X Y A && !siaN A B X && X == A && siaN A B Y && CInN Y B K)
      (CInN A B K && !siaN X Y K) &&
    imp (!siaN X Y A && !siaN A B X && X != A && CInN A B K) (!siaN X Y K))

/-- P2 on ranks: a key of the arc outside the closed hole lies in a piece. -/
def P2N (A B X Y K : ℕ) : Bool :=
  imp (X != Y && CInN A B K && !CInN X Y K) (
    imp (siaN X Y A) (siaN A B Y && imp (siaN Y B X) (CInN Y X K) &&
      imp (!siaN Y B X) (CInN Y B K)) &&
    imp (!siaN X Y A && siaN A B X) (CInN A X K || (siaN X B Y && CInN Y B K)) &&
    imp (!siaN X Y A && !siaN A B X && X == A) (siaN A B Y && CInN Y B K))

theorem p1N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P1N A B X Y K = true := by decide

/-- P0 on ranks: the open interval of a piece lies in the open interval of the arc. -/
def P0N (A B X Y K : ℕ) : Bool :=
  imp (X != Y) (
    imp (siaN X Y A && siaN A B Y && siaN Y B X && siaN Y X K) (siaN A B K) &&
    imp (siaN X Y A && siaN A B Y && siaN Y B K) (siaN A B K) &&
    imp (!siaN X Y A && siaN A B X && siaN A X K) (siaN A B K) &&
    imp (!siaN X Y A && siaN A B X && siaN X B Y && siaN Y B K) (siaN A B K) &&
    imp (!siaN X Y A && !siaN A B X && siaN A B Y && siaN Y B K) (siaN A B K))

theorem p0N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P0N A B X Y K = true := by decide

theorem p2N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P2N A B X Y K = true := by decide

/-! ## The order facts on reals -/

/-- P1 on reals. -/
theorem p1R (a b x y k : ℝ) (hxy : x ≠ y) :
    (sideInArc x y a → sideInArc a b y → sideInArc y b x → CIn y x k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (sideInArc x y a → sideInArc a b y → ¬ sideInArc y b x → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → sideInArc a b x → CIn a x k → CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc x b y → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x = a → sideInArc a b y → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x ≠ a → CIn a b k → ¬ sideInArc x y k) := by
  set L : List ℝ := [a, b, x, y, k] with hL
  have ma : a ∈ L := by simp [L]
  have mb : b ∈ L := by simp [L]
  have mx : x ∈ L := by simp [L]
  have my : y ∈ L := by simp [L]
  have mk : k ∈ L := by simp [L]
  have hlen : L.length = 5 := rfl
  have hP := p1N_all (rank L a) (by have := rank_lt_length L a; omega)
    (rank L b) (by have := rank_lt_length L b; omega) (rank L x)
    (by have := rank_lt_length L x; omega) (rank L y) (by have := rank_lt_length L y; omega)
    (rank L k) (by have := rank_lt_length L k; omega)
  simp only [ne_eq] at hxy ⊢
  rw [rank_eq_iff mx my] at hxy
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    cIn_rank my mx mk, cIn_rank ma mb mk, sideInArc_rank mx my mk, cIn_rank my mb mk,
    sideInArc_rank ma mb mx, cIn_rank ma mx mk, sideInArc_rank mx mb my, rank_eq_iff mx ma]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  rw [show (X = A) = ((X == A) = true) from propext beq_iff_eq.symm] at *
  rw [show (X = Y) = ((X == Y) = true) from propext beq_iff_eq.symm] at hxy
  simp only [P1N, imp, bne] at hP
  generalize siaN X Y A = s1 at *
  generalize siaN A B Y = s2 at *
  generalize siaN Y B X = s3 at *
  generalize CInN Y X K = s4 at *
  generalize CInN A B K = s5 at *
  generalize siaN X Y K = s6 at *
  generalize CInN Y B K = s7 at *
  generalize siaN A B X = s8 at *
  generalize CInN A X K = s9 at *
  generalize siaN X B Y = s10 at *
  generalize (X == A) = e1 at *
  generalize (X == Y) = e2 at *
  have he2 : e2 = false := by simpa using hxy
  subst he2
  revert hP
  revert s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 e1
  decide

/-- The ranks of five reals, as a transfer package. -/
theorem ranks5 (a b x y k : ℝ) : ∃ L : List ℝ, a ∈ L ∧ b ∈ L ∧ x ∈ L ∧ y ∈ L ∧ k ∈ L ∧
    rank L a < 6 ∧ rank L b < 6 ∧ rank L x < 6 ∧ rank L y < 6 ∧ rank L k < 6 := by
  refine ⟨[a, b, x, y, k], by simp, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · have := rank_lt_length [a, b, x, y, k]; simp only [List.length_cons, List.length_nil] at this
    exact Nat.lt_of_le_of_lt (this _) (by norm_num)

/-- P0 on reals. -/
theorem p0R (a b x y k : ℝ) (hxy : x ≠ y) :
    (sideInArc x y a → sideInArc a b y → sideInArc y b x → sideInArc y x k → sideInArc a b k) ∧
    (sideInArc x y a → sideInArc a b y → sideInArc y b k → sideInArc a b k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc a x k → sideInArc a b k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc x b y → sideInArc y b k →
      sideInArc a b k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → sideInArc a b y → sideInArc y b k →
      sideInArc a b k) := by
  obtain ⟨L, ma, mb, mx, my, mk, ra, rb, rx, ry, rk⟩ := ranks5 a b x y k
  have hP := p0N_all _ ra _ rb _ rx _ ry _ rk
  simp only [ne_eq] at hxy
  rw [rank_eq_iff mx my] at hxy
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    sideInArc_rank my mx mk, sideInArc_rank ma mb mk, sideInArc_rank my mb mk,
    sideInArc_rank ma mb mx, sideInArc_rank ma mx mk, sideInArc_rank mx mb my]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  rw [show (X = Y) = ((X == Y) = true) from propext beq_iff_eq.symm] at hxy
  simp only [P0N, imp, bne] at hP
  generalize siaN X Y A = s1 at *
  generalize siaN A B Y = s2 at *
  generalize siaN Y B X = s3 at *
  generalize siaN Y X K = s4 at *
  generalize siaN A B K = s5 at *
  generalize siaN Y B K = s6 at *
  generalize siaN A B X = s7 at *
  generalize siaN A X K = s8 at *
  generalize siaN X B Y = s9 at *
  generalize (X == Y) = e2 at *
  have he2 : e2 = false := by simpa using hxy
  subst he2
  revert hP
  revert s1 s2 s3 s4 s5 s6 s7 s8 s9
  decide

/-- P2 on reals. -/
theorem p2R (a b x y k : ℝ) (hxy : x ≠ y) (hk : CIn a b k) (hk' : ¬ CIn x y k) :
    (sideInArc x y a → sideInArc a b y ∧ (sideInArc y b x → CIn y x k) ∧
      (¬ sideInArc y b x → CIn y b k)) ∧
    (¬ sideInArc x y a → sideInArc a b x → CIn a x k ∨ (sideInArc x b y ∧ CIn y b k)) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x = a → sideInArc a b y ∧ CIn y b k) := by
  obtain ⟨L, ma, mb, mx, my, mk, ra, rb, rx, ry, rk⟩ := ranks5 a b x y k
  have hP := p2N_all _ ra _ rb _ rx _ ry _ rk
  simp only [ne_eq] at hxy
  rw [rank_eq_iff mx my] at hxy
  rw [cIn_rank ma mb mk] at hk
  rw [cIn_rank mx my mk] at hk'
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    cIn_rank my mx mk, cIn_rank my mb mk, sideInArc_rank ma mb mx, cIn_rank ma mx mk,
    sideInArc_rank mx mb my, rank_eq_iff mx ma]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  rw [show (X = A) = ((X == A) = true) from propext beq_iff_eq.symm] at *
  rw [show (X = Y) = ((X == Y) = true) from propext beq_iff_eq.symm] at hxy
  simp only [P2N, imp, bne] at hP
  generalize siaN X Y A = s1 at *
  generalize siaN A B Y = s2 at *
  generalize siaN Y B X = s3 at *
  generalize CInN Y X K = s4 at *
  generalize CInN Y B K = s5 at *
  generalize siaN A B X = s6 at *
  generalize CInN A X K = s7 at *
  generalize siaN X B Y = s8 at *
  generalize CInN A B K = s9 at *
  generalize CInN X Y K = s10 at *
  generalize (X == A) = e1 at *
  generalize (X == Y) = e2 at *
  have he2 : e2 = false := by simpa using hxy
  subst he2
  revert hP hk hk'
  revert s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 e1
  decide

/-! ## The pieces of one hole -/

section Generic

variable {α : Type} (key : α → ℝ)

/-- **P0**: the open interval of a piece lies in the open interval of the arc. -/
theorem cut1_open {a b x y : α} (hxy : key x ≠ key y) {u v : α}
    (h : (u, v) ∈ cut1 key a b x y) {k : ℝ} (hk : sideInArc (key u) (key v) k) :
    sideInArc (key a) (key b) k := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := p0R (key a) (key b) (key x) (key y) k hxy
  rcases cut1_cases key a b x y h with
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ |
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, h4, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩
  · exact q1 h1 h2 h3 hk
  · exact q2 h1 h2 hk
  · exact q3 h1 h2 hk
  · exact q4 h1 h2 h3 hk
  · exact q5 h1 h2 h4 hk
  · exact hk

/-- **P1**: a piece lies in the arc and outside the open hole. -/
theorem cut1_sub {a b x y : α} (hxy : key x ≠ key y) {u v : α}
    (h : (u, v) ∈ cut1 key a b x y) {k : ℝ} (hk : CIn (key u) (key v) k) :
    CIn (key a) (key b) k ∧ ¬ sideInArc (key x) (key y) k := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p1R (key a) (key b) (key x) (key y) k hxy
  rcases cut1_cases key a b x y h with
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ |
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, h4, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩
  · exact q1 h1 h2 h3 hk
  · exact q2 h1 h2 h3 hk
  · exact q3 h1 h2 hk
  · exact q4 h1 h2 h3 hk
  · exact q5 h1 h2 h3 h4 hk
  · exact ⟨hk, q6 h1 h2 h3 hk⟩

/-- **P2**: a key of the arc outside the closed hole lies in a piece. -/
theorem cut1_cover {a b x y : α} (hxy : key x ≠ key y) {k : ℝ} (hk : CIn (key a) (key b) k)
    (hk' : ¬ CIn (key x) (key y) k) :
    ∃ uv ∈ cut1 key a b x y, CIn (key uv.1) (key uv.2) k := by
  obtain ⟨q1, q2, q3⟩ := p2R (key a) (key b) (key x) (key y) k hxy hk hk'
  unfold cut1 cutK
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact ⟨(y, x), by simp, (q1 h1).2.1 h3⟩
  · exact ⟨(y, b), by simp, (q1 h1).2.2 h3⟩
  · exact absurd (q1 h1).1 h2
  · rcases q2 h1 h4 with h | ⟨-, h⟩
    · exact ⟨(a, x), by simp, h⟩
    · exact ⟨(y, b), by simp, h⟩
  · rcases q2 h1 h4 with h | ⟨h', -⟩
    · exact ⟨(a, x), by simp, h⟩
    · exact absurd h' h5
  · exact ⟨(y, b), by simp, (q3 h1 h4 h6).2⟩
  · exact absurd (q3 h1 h4 h6).1 h7
  · exact ⟨(a, b), by simp, hk⟩

/-! ## Several holes -/

/-- **The pieces of an arc after a list of holes**, cut one after the other. -/
noncomputable def leaves : List (α × α) → α × α → List (α × α)
  | [], p => [p]
  | h :: hs, p => (cut1 key p.1 p.2 h.1 h.2).flatMap (fun q => leaves hs q)

/-- The holes are proper (distinct end keys). -/
def HolesOK (hs : List (α × α)) : Prop := ∀ h ∈ hs, key h.1 ≠ key h.2

/-- **P0 for several holes.** -/
theorem leaves_open {hs : List (α × α)} (hh : HolesOK key hs) {p uv : α × α}
    (h : uv ∈ leaves key hs p) {k : ℝ} (hk : sideInArc (key uv.1) (key uv.2) k) :
    sideInArc (key p.1) (key p.2) k := by
  induction hs generalizing p with
  | nil => simp only [leaves, List.mem_singleton] at h; subst h; exact hk
  | cons g hs ih =>
    simp only [leaves, List.mem_flatMap] at h
    obtain ⟨q, hq, hq'⟩ := h
    exact cut1_open key (hh g (by simp)) hq
      (ih (fun h' hm => hh h' (List.mem_cons_of_mem _ hm)) hq')

/-- **P1 for several holes.** -/
theorem leaves_sub {hs : List (α × α)} (hh : HolesOK key hs) {p uv : α × α}
    (h : uv ∈ leaves key hs p) {k : ℝ} (hk : CIn (key uv.1) (key uv.2) k) :
    CIn (key p.1) (key p.2) k ∧ ∀ g ∈ hs, ¬ sideInArc (key g.1) (key g.2) k := by
  induction hs generalizing p with
  | nil =>
    simp only [leaves, List.mem_singleton] at h; subst h
    exact ⟨hk, fun _ hg => absurd hg List.not_mem_nil⟩
  | cons g hs ih =>
    simp only [leaves, List.mem_flatMap] at h
    obtain ⟨q, hq, hq'⟩ := h
    obtain ⟨h1, h2⟩ := ih (fun h' hm => hh h' (List.mem_cons_of_mem _ hm)) hq'
    obtain ⟨h3, h4⟩ := cut1_sub key (hh g (by simp)) hq h1
    refine ⟨h3, fun g' hg' => ?_⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact h4
    · exact h2 g' hg'

/-- **P2 for several holes.** -/
theorem leaves_cover {hs : List (α × α)} (hh : HolesOK key hs) {p : α × α} {k : ℝ}
    (hk : CIn (key p.1) (key p.2) k) (hk' : ∀ g ∈ hs, ¬ CIn (key g.1) (key g.2) k) :
    ∃ uv ∈ leaves key hs p, CIn (key uv.1) (key uv.2) k := by
  induction hs generalizing p with
  | nil => exact ⟨p, by simp [leaves], hk⟩
  | cons g hs ih =>
    obtain ⟨q, hq, hq'⟩ := cut1_cover key (hh g (by simp)) hk (hk' g (by simp))
    obtain ⟨uv, huv, huv'⟩ := ih (fun h' hm => hh h' (List.mem_cons_of_mem _ hm)) hq'
      (fun g' hg' => hk' g' (List.mem_cons_of_mem _ hg'))
    exact ⟨uv, by simp only [leaves, List.mem_flatMap]; exact ⟨q, hq, huv⟩, huv'⟩

end Generic

end

end ShotList

end Chazelle.Core
