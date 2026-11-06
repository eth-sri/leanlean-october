module

public import Chazelle.Core.ShootCutLoop2
public import Chazelle.Rwx
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-G, part 24: keys along the path of the core

The core hands pieces whose ends have increasing **unwrapped keys** (a key plus a multiple of the
number `n` of walk edges) within one lap from the start:

* `sideInArc_unw`: a key strictly between two others in unwrapped order, within one lap, lies in
  their cyclic interval;
* `KPath`: the pieces go through increasing unwrapped keys; `e6_of_kpath`: the end of every piece
  but the last lies strictly inside the cyclic interval from its start to the final end (the
  tiling conjunct of `CutterOK`); `kpath_of_upath`: a path of walk vertices is one;
* `arcWt_ge`: a stretch of `L` counted edges inside the unwrapped interval of an arc weighs at
  least `L`.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideInArc)

namespace ShootCut

/-- An integer `m` with `x + m n ∈ (0, 2n)` for `x ∈ [0, n)` is `0` or `1`. -/
theorem int01 {n x : ℝ} {m : ℤ} (hn : 0 < n) (hx0 : 0 ≤ x) (hxn : x < n) (h1 : 0 < x + m * n)
    (h2 : x + m * n < 2 * n) : m = 0 ∨ m = 1 := by
  have a1 : (m : ℝ) > -1 := by
    by_contra h; push Not at h; nlinarith
  have a2 : (m : ℝ) < 2 := by
    by_contra h; push Not at h; nlinarith
  have b1 : m > -1 := by exact_mod_cast a1
  have b2 : m < 2 := by exact_mod_cast a2
  omega

/-- **A key between two others in unwrapped order** (within one lap) lies in their cyclic
interval. -/
theorem sideInArc_unw {n a b x A B X : ℝ} (hn : 0 < n) (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hA : ∃ i : ℤ, A = a + i * n)
    (hX : ∃ j : ℤ, X = x + j * n) (hB : ∃ k : ℤ, B = b + k * n) (h1 : A < X) (h2 : X < B)
    (h3 : B ≤ A + n) : sideInArc a b x := by
  obtain ⟨i, rfl⟩ := hA
  obtain ⟨j, rfl⟩ := hX
  obtain ⟨k, rfl⟩ := hB
  have hj : j - i = 0 ∨ j - i = 1 := int01 hn hx0 hxn (by pcnl)
    (by pcnl)
  have hk : k - i = 0 ∨ k - i = 1 := int01 hn hb0 hbn (by pcnl)
    (by pcnl)
  have ej : (j : ℝ) = i + (j - i : ℤ) := by pcr
  have ek : (k : ℝ) = i + (k - i : ℤ) := by pcr
  unfold sideInArc
  rcases hj with hj | hj <;> rcases hk with hk | hk <;> rw [hj] at ej <;> rw [hk] at ek <;>
    push_cast at ej ek <;> rw [ej] at h1 h2 <;> rw [ek] at h2 h3
  · have hab : a < b := by nlinarith
    rw [ite_eq_left hab]; constructor <;> nlinarith
  · have hab : ¬ a < b := by intro h; nlinarith
    rw [ite_eq_right hab]; left; nlinarith
  · exfalso; nlinarith
  · have hab : ¬ a < b := by intro h; nlinarith
    rw [ite_eq_right hab]; right; nlinarith

variable (M : Model) (Q : Polygon)

/-- The pieces go through increasing unwrapped keys. -/
def KPath (n : ℝ) : ℝ → List Pc → ℝ → Prop
  | V, [], V' => V = V'
  | V, pc :: ps, V' => (∃ i : ℤ, V = M.key Q pc.s + i * n) ∧
      ∃ V₁, V < V₁ ∧ (∃ j : ℤ, V₁ = M.key Q pc.e + j * n) ∧ KPath n V₁ ps V'

variable {M Q}

theorem KPath.le {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' → V ≤ V'
  | _, [], _, h => le_of_eq h
  | _, _ :: _, _, ⟨_, _, h1, _, h2⟩ => le_trans h1.le h2.le

theorem KPath.lt {n : ℝ} {V V' : ℝ} {ps : List Pc} (h : KPath M Q n V ps V') (hne : ps ≠ []) :
    V < V' := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons pc ps => obtain ⟨_, _, h1, _, h2⟩ := h; exact lt_of_lt_of_le h1 h2.le

theorem KPath.append {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' →
    ∀ (qs : List Pc) {V'' : ℝ}, KPath M Q n V' qs V'' → KPath M Q n V (ps ++ qs) V''
  | _, [], _, h, _, _, hq => by simp [KPath] at h; subst h; exact hq
  | _, _ :: _, _, ⟨h1, V₁, h2, h3, h4⟩, qs, _, hq => ⟨h1, V₁, h2, h3, KPath.append h4 qs hq⟩

/-- The last end of a path is congruent to its end value. -/
theorem KPath.last {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ} (_ : KPath M Q n V ps V')
    (hne : ps ≠ []), ∃ j : ℤ, V' = M.key Q (ps.getLast hne).e + j * n
  | _, [pc], _, ⟨_, V₁, _, h3, h4⟩, _ => by simp [KPath] at h4; subst h4; exact h3
  | _, _ :: q :: qs, _, ⟨_, _, _, _, h4⟩, _ => by
    rw [List.getLast_cons (List.cons_ne_nil q qs)]
    exact KPath.last h4 (List.cons_ne_nil q qs)

/-- **The tiling conjunct**: along a path of pieces within one lap, the end of every piece but
the last lies strictly inside the cyclic interval from its start to the final end. -/
theorem e6_of_kpath {n : ℝ} (hn : 0 < n) :
    ∀ {V : ℝ} {ps : List Pc} {T : ℝ} (_ : KPath M Q n V ps T) (_ : T ≤ V + n)
      (_ : ∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < n) ∧ (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < n))
      (hne : ps ≠ []),
      ∀ i, (hi : i + 1 < ps.length) →
        sideInArc (M.key Q (ps[i]'(by omega)).s) (M.key Q (ps.getLast hne).e)
          (M.key Q (ps[i]'(by omega)).e)
  | _, [], _, _, _, _, hne, _, _ => absurd rfl hne
  | V, pc :: ps, T, ⟨hs, V₁, hV, he, hp⟩, hT, hb, hne, i, hi => by
    have hne' : ps ≠ [] := by rintro rfl; simp at hi
    have hlast : (pc :: ps).getLast hne = ps.getLast hne' := List.getLast_cons hne'
    rcases i with _ | i
    · simp [List.getElem_cons_zero]
      rw [hlast]
      have hbp := hb pc (by simp)
      have hbl := hb (ps.getLast hne') (by simp [List.getLast_mem])
      exact sideInArc_unw hn hbp.1.1 hbp.1.2 hbl.2.1 hbl.2.2 hbp.2.1 hbp.2.2 hs he
        (KPath.last hp hne') hV (hp.lt hne') hT
    · simp [List.getElem_cons_succ]
      rw [hlast]
      exact e6_of_kpath hn hp (by linarith) (fun q hq => hb q (by simp [hq])) hne' i
        (by sio at hi)

/-- **A path of walk vertices** is a path of unwrapped keys. -/
theorem kpath_of_upath {n : ℕ} : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    KPath M Q n (u : ℝ) ps (u' : ℝ)
  | _, [], _, h => by simp [UPath] at h; subst h; rfl
  | u, pc :: ps, u', ⟨h1, u₁, h2, h3, h4⟩ => by
    have ek : ∀ v : ℕ, ((v % n : ℕ) : ℝ) + ((v / n : ℕ) : ℝ) * (n : ℝ) = (v : ℝ) := fun v => by
      have := Nat.mod_add_div v n
      exact_mod_cast (show v % n + v / n * n = v by rwx [Nat.mul_comm])
    refine ⟨⟨((u / n : ℕ) : ℤ), ?_⟩, u₁, by exact_mod_cast h2, ⟨((u₁ / n : ℕ) : ℤ), ?_⟩,
      kpath_of_upath h4⟩
    · rw [h1, key_hgt0, Int.cast_natCast]; linarith [ek u]
    · rw [h3, key_hgt0, Int.cast_natCast]; linarith [ek u₁]

end ShootCut

end

end Chazelle.Core
