module

public import Chazelle.Core.ShootCutDecide
public import Chazelle.Core.ShootCutTile

/-!
# WP-G, part 28: the plan of the general case

* `arcWt_ge`: a stretch of `L` counted edges inside the unwrapped interval `[A, T]` of an arc
  (within one lap) weighs at least `L`: every stretch of the main loop is at most `γ` long;
* `key_eq_of_unw`: two keys congruent modulo `n` are equal;
* `plan`: in the general case (not `SAME`, not a single piece) the first walk vertex `c₀` and the
  final one `f` have unwrapped positions `k_s < U₀ ≤ F ≤ T < U₀ + n`
  (`T = k_s + len (k_s, k_e)`), with `F < T` iff a last piece is handed.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideInArc)

namespace ShootCut

/-- **A stretch of counted edges** inside the unwrapped interval of an arc weighs at least its
length. -/
theorem arcWt_ge (C : Chain) {a b A T : ℝ}
    (ha : 0 ≤ a ∧ a < ((2 * C.m + 7 : ℕ) : ℝ)) (hb : 0 ≤ b ∧ b < ((2 * C.m + 7 : ℕ) : ℝ))
    (hA : ∃ i : ℤ, A = a + i * ((2 * C.m + 7 : ℕ) : ℝ))
    (hT : ∃ k : ℤ, T = b + k * ((2 * C.m + 7 : ℕ) : ℝ))
    (hTA : T ≤ A + ((2 * C.m + 7 : ℕ) : ℝ)) {v L : ℕ} (hv6 : 6 ≤ v % (2 * C.m + 7))
    (hvL : v % (2 * C.m + 7) + L ≤ 2 * C.m + 6) (hAv : A ≤ v) (hvT : (v : ℝ) + L ≤ T) :
    L ≤ (chainModel C).arcWt a b := by
  set n := 2 * C.m + 7 with hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by rw [hn]; positivity
  set c := v % n with hc
  unfold Model.arcWt
  have hW : (chainModel C).W.n = n := chainModel_n C
  have hsub : ((Finset.Ico c (c + L) : Finset ℕ) : Set ℕ) ⊆
      {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)} := by
    intro p hp
    simp only [Finset.coe_Ico, Set.mem_Ico] at hp
    refine ⟨by rw [hW]; omega, (chainModel_counted_iff C p (by rw [hW]; omega)).2 ⟨by omega,
      by omega⟩, 1 / 2, by norm_num, by norm_num, ?_⟩
    have ev : (v : ℝ) = (c : ℝ) + ((v / n : ℕ) : ℝ) * n := by
      have := Nat.mod_add_div v n
      exact_mod_cast (show v = c + v / n * n by rw [Nat.mul_comm]; omega)
    have hpn : ((p : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (show p + 1 ≤ n by omega)
    refine sideInArc_unw hn0 ha.1 ha.2 hb.1 hb.2 (by positivity) (by linarith) hA
      (X := (v : ℝ) + ((p - c : ℕ) : ℝ) + 1 / 2) ⟨((v / n : ℕ) : ℤ), ?_⟩ hT ?_ ?_ hTA
    · rw [Int.cast_natCast, ev]
      push_cast [show c ≤ p by omega]
      ring
    · have : (0 : ℝ) ≤ ((p - c : ℕ) : ℝ) := by positivity
      linarith
    · have : ((p - c : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast (show p - c + 1 ≤ L by omega)
      linarith
  have hfin : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}.Finite :=
    (Set.finite_lt_nat _).subset fun p hp => hp.1
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Ico] at this
  omega

/-- **Two keys congruent modulo `n`** in `[0, n)` are equal. -/
theorem key_eq_of_unw {n x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x ∧ x < n) (hy : 0 ≤ y ∧ y < n)
    {i j : ℤ} (h : x + i * n = y + j * n) : x = y := by
  have hij : ((i - j : ℤ) : ℝ) * n = y - x := by push_cast; linarith
  have h1 : ((i - j : ℤ) : ℝ) > -1 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : ((i - j : ℤ) : ℝ) < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h3 : i - j > -1 := by exact_mod_cast h1
  have h4 : i - j < 1 := by exact_mod_cast h2
  have h5 : i - j = 0 := by omega
  rw [h5] at hij
  simp at hij
  linarith

/-- The walk edge `p` is in the uncounted block. -/
def InUB (m p : ℕ) : Prop := p ≤ 5 ∨ p = 2 * m + 6

instance (m p : ℕ) : Decidable (InUB m p) := inferInstanceAs (Decidable (_ ∨ _))

/-- The position of a walk edge in the uncounted block (`0` for `2m + 6`, `p + 1` for `p ≤ 5`). -/
def uIx (p : ℕ) : ℕ := if p ≤ 5 then p + 1 else 0

/-- The core hands a single piece `[s, e]` from `first`. -/
def Done (m e₁ e₂ : ℕ) : Prop :=
  (InUB m e₁ ∧ InUB m e₂ ∧ uIx e₁ < uIx e₂) ∨ (¬ InUB m e₁ ∧ InUB m e₂ ∧ ¬ e₁ + 1 < 2 * m + 6)

/-- The first walk vertex of the main loop. -/
def c0Of (m e₁ : ℕ) : ℕ := if e₁ ≤ 5 ∨ e₁ = 2 * m + 6 then 6 else e₁ + 1

/-- The final walk vertex of the main loop. -/
def fOf (m e₂ : ℕ) : ℕ := if e₂ ≤ 5 ∨ e₂ = 2 * m + 6 then 2 * m + 5 else e₂

/-- **The plan of the general case.** -/
theorem plan (C : Chain) (Q : Polygon) {N : ℕ} {s e : WPos}
    (hs : ProperPos (chainModel C) Q N s) (he : ProperPos (chainModel C) Q N e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hsame : ¬ (s.edge = e.edge ∧ (chainModel C).key Q s < (chainModel C).key Q e))
    (hdone : ¬ Done C.m s.edge e.edge) :
    ∃ U₀ F : ℕ, U₀ % (2 * C.m + 7) = c0Of C.m s.edge ∧ (chainModel C).key Q s < U₀ ∧
      F % (2 * C.m + 7) = fOf C.m e.edge ∧ U₀ ≤ F ∧ F < U₀ + (2 * C.m + 7) ∧
      (F : ℝ) ≤ (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
        ((chainModel C).key Q s) ((chainModel C).key Q e) ∧
      ((InUB C.m e.edge ∨ 0 < (chainModel C).param Q e) →
        (F : ℝ) < (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
          ((chainModel C).key Q s) ((chainModel C).key Q e)) ∧
      (¬ (InUB C.m e.edge ∨ 0 < (chainModel C).param Q e) →
        (F : ℝ) = (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
          ((chainModel C).key Q s) ((chainModel C).key Q e)) := by
  set M := chainModel C
  set ks := M.key Q s with hks
  set ke := M.key Q e with hke
  set n := 2 * C.m + 7 with hn
  have hm1 := C.one_le
  have bs := key_bounds hs
  have be := key_bounds he
  have hkeq : ke = e.edge + M.param Q e := rfl
  have hp0 := he.1
  have hp1 := he.2.1
  have hT1 : ks < ke → ks + len (n : ℝ) ks ke = ke := fun h => by unfold len; rw [ite_eq_left h]; ring
  have hT2 : ¬ ks < ke → ks + len (n : ℝ) ks ke = ke + n := fun h => by
    unfold len; rw [ite_eq_right h]; ring
  set e₁ := s.edge with he₁
  set e₂ := e.edge with he₂
  have cn : ((n : ℕ) : ℝ) = 2 * (C.m : ℝ) + 7 := by rw [hn]; push_cast; ring
  unfold c0Of fOf
  unfold Done InUB uIx at hdone
  rcases (show e₁ ≤ 5 ∨ e₁ = 2 * C.m + 6 ∨ (6 ≤ e₁ ∧ e₁ ≤ 2 * C.m + 5) by omega) with
    h1 | h1 | h1 <;>
  rcases (show e₂ ≤ 5 ∨ e₂ = 2 * C.m + 6 ∨ (6 ≤ e₂ ∧ e₂ ≤ 2 * C.m + 5) by omega) with
    h2 | h2 | h2
  -- the start in `0 … 5`
  · -- the end in `0 … 5`: `e₂ ≤ e₁`
    have hle : e₂ ≤ e₁ := by
      by_contra hc; apply hdone; left
      refine ⟨Or.inl h1, Or.inl h2, ?_⟩
      rw [ite_eq_left h1, ite_eq_left h2]; omega
    have hT : ¬ ks < ke := by
      rcases hle.lt_or_eq with hlt | heq
      · have : (e₂ : ℝ) + 1 ≤ e₁ := by exact_mod_cast hlt
        intro h; linarith [be.2, bs.1]
      · intro h; exact hsame ⟨heq.symm, h⟩
    refine ⟨6, 2 * C.m + 5, ?_, ?_, ?_, by omega, by omega, ?_, fun _ => ?_, fun h => ?_⟩
    · rw [ite_eq_left (Or.inl h1)]; exact Nat.mod_eq_of_lt (by omega)
    · have : (e₁ : ℝ) + 1 ≤ 6 := by exact_mod_cast (show e₁ + 1 ≤ 6 by omega)
      push_cast; linarith [bs.2]
    · rw [ite_eq_left (Or.inl h2)]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT2 hT]; push_cast; rw [cn]; linarith [be.1, show (0 : ℝ) ≤ e₂ by positivity]
    · rw [hT2 hT]; push_cast; rw [cn]; linarith [be.1, show (0 : ℝ) ≤ e₂ by positivity]
    · exact absurd (Or.inl (Or.inl h2)) h
  · -- the end on `2m + 6`
    have hT : ks < ke := by
      have : (e₁ : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show e₁ + 1 ≤ e₂ by omega)
      linarith [bs.2, be.1]
    refine ⟨6, 2 * C.m + 5, ?_, ?_, ?_, by omega, by omega, ?_, fun _ => ?_, fun h => ?_⟩
    · rw [ite_eq_left (Or.inl h1)]; exact Nat.mod_eq_of_lt (by omega)
    · have : (e₁ : ℝ) + 1 ≤ 6 := by exact_mod_cast (show e₁ + 1 ≤ 6 by omega)
      push_cast; linarith [bs.2]
    · rw [ite_eq_left (Or.inr h2)]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT1 hT]
      have : ((2 * C.m + 5 : ℕ) : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show 2 * C.m + 5 + 1 ≤ e₂ by omega)
      linarith [be.1]
    · rw [hT1 hT]
      have : ((2 * C.m + 5 : ℕ) : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show 2 * C.m + 5 + 1 ≤ e₂ by omega)
      linarith [be.1]
    · exact absurd (Or.inl (Or.inr h2)) h
  · -- the end on the double boundary
    have hT : ks < ke := by
      have : (e₁ : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show e₁ + 1 ≤ e₂ by omega)
      linarith [bs.2, be.1]
    have hnU : ¬ (e₂ ≤ 5 ∨ e₂ = 2 * C.m + 6) := by omega
    refine ⟨6, e₂, ?_, ?_, ?_, by omega, by omega, ?_, fun h => ?_, fun h => ?_⟩
    · rw [ite_eq_left (Or.inl h1)]; exact Nat.mod_eq_of_lt (by omega)
    · have : (e₁ : ℝ) + 1 ≤ 6 := by exact_mod_cast (show e₁ + 1 ≤ 6 by omega)
      push_cast; linarith [bs.2]
    · rw [ite_eq_right hnU]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT1 hT]; linarith [be.1]
    · rw [hT1 hT, hkeq]
      rcases h with h | h
      · exact absurd h hnU
      · linarith
    · rw [hT1 hT, hkeq]
      have : M.param Q e = 0 := by
        by_contra hc; exact h (Or.inr (lt_of_le_of_ne hp0 (Ne.symm hc)))
      rw [this]; ring
  -- the start on `2m + 6`
  · exact absurd (Or.inl ⟨Or.inr h1, Or.inl h2, by rw [ite_eq_right (by omega), ite_eq_left h2]; omega⟩)
      hdone
  · -- both on `2m + 6`
    have hT : ¬ ks < ke := by intro h; exact hsame ⟨by omega, h⟩
    refine ⟨6 + n, 2 * C.m + 5 + n, ?_, ?_, ?_, by omega, by omega, ?_, fun _ => ?_, fun h => ?_⟩
    · rw [ite_eq_left (Or.inr h1), Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · have : (e₁ : ℝ) + 1 ≤ ((6 + n : ℕ) : ℝ) := by exact_mod_cast (show e₁ + 1 ≤ 6 + n by omega)
      linarith [bs.2]
    · rw [ite_eq_left (Or.inr h2), Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT2 hT]
      have : ((2 * C.m + 5 + n : ℕ) : ℝ) + 1 ≤ e₂ + n := by
        exact_mod_cast (show 2 * C.m + 5 + n + 1 ≤ e₂ + n by omega)
      linarith [be.1]
    · rw [hT2 hT]
      have : ((2 * C.m + 5 + n : ℕ) : ℝ) + 1 ≤ e₂ + n := by
        exact_mod_cast (show 2 * C.m + 5 + n + 1 ≤ e₂ + n by omega)
      linarith [be.1]
    · exact absurd (Or.inl (Or.inr h2)) h
  · -- the start on `2m + 6`, the end on the double boundary
    have hT : ¬ ks < ke := by
      have : (e₂ : ℝ) + 1 ≤ e₁ := by exact_mod_cast (show e₂ + 1 ≤ e₁ by omega)
      intro h; linarith [be.2, bs.1]
    have hnU : ¬ (e₂ ≤ 5 ∨ e₂ = 2 * C.m + 6) := by omega
    refine ⟨6 + n, e₂ + n, ?_, ?_, ?_, by omega, by omega, ?_, fun h => ?_, fun h => ?_⟩
    · rw [ite_eq_left (Or.inr h1), Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · have : (e₁ : ℝ) + 1 ≤ ((6 + n : ℕ) : ℝ) := by exact_mod_cast (show e₁ + 1 ≤ 6 + n by omega)
      linarith [bs.2]
    · rw [ite_eq_right hnU, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT2 hT]; push_cast; linarith [be.1]
    · rw [hT2 hT, hkeq]
      rcases h with h | h
      · exact absurd h hnU
      · push_cast; linarith
    · rw [hT2 hT, hkeq]
      have : M.param Q e = 0 := by
        by_contra hc; exact h (Or.inr (lt_of_le_of_ne hp0 (Ne.symm hc)))
      rw [this]; push_cast; ring
  -- the start on the double boundary
  · -- the end in `0 … 5`
    have hne : e₁ + 1 < 2 * C.m + 6 := by
      by_contra hc; exact hdone (Or.inr ⟨by omega, Or.inl h2, hc⟩)
    have hT : ¬ ks < ke := by
      have : (e₂ : ℝ) + 1 ≤ e₁ := by exact_mod_cast (show e₂ + 1 ≤ e₁ by omega)
      intro h; linarith [be.2, bs.1]
    refine ⟨e₁ + 1, 2 * C.m + 5, ?_, ?_, ?_, by omega, by omega, ?_, fun _ => ?_, fun h => ?_⟩
    · rw [ite_eq_right (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    · push_cast; linarith [bs.2]
    · rw [ite_eq_left (Or.inl h2)]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT2 hT]; push_cast; rw [cn]; linarith [be.1, show (0 : ℝ) ≤ e₂ by positivity]
    · rw [hT2 hT]; push_cast; rw [cn]; linarith [be.1, show (0 : ℝ) ≤ e₂ by positivity]
    · exact absurd (Or.inl (Or.inl h2)) h
  · -- the end on `2m + 6`
    have hne : e₁ + 1 < 2 * C.m + 6 := by
      by_contra hc; exact hdone (Or.inr ⟨by omega, Or.inr h2, hc⟩)
    have hT : ks < ke := by
      have : (e₁ : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show e₁ + 1 ≤ e₂ by omega)
      linarith [bs.2, be.1]
    refine ⟨e₁ + 1, 2 * C.m + 5, ?_, ?_, ?_, by omega, by omega, ?_, fun _ => ?_, fun h => ?_⟩
    · rw [ite_eq_right (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    · push_cast; linarith [bs.2]
    · rw [ite_eq_left (Or.inr h2)]; exact Nat.mod_eq_of_lt (by omega)
    · rw [hT1 hT]
      have : ((2 * C.m + 5 : ℕ) : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show 2 * C.m + 5 + 1 ≤ e₂ by omega)
      linarith [be.1]
    · rw [hT1 hT]
      have : ((2 * C.m + 5 : ℕ) : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show 2 * C.m + 5 + 1 ≤ e₂ by omega)
      linarith [be.1]
    · exact absurd (Or.inl (Or.inr h2)) h
  · -- both on the double boundary
    have hnU : ¬ (e₂ ≤ 5 ∨ e₂ = 2 * C.m + 6) := by omega
    have hnU1 : ¬ (e₁ ≤ 5 ∨ e₁ = 2 * C.m + 6) := by omega
    rcases (show e₁ < e₂ ∨ e₂ ≤ e₁ by omega) with h3 | h3
    · have hT : ks < ke := by
        have : (e₁ : ℝ) + 1 ≤ e₂ := by exact_mod_cast (show e₁ + 1 ≤ e₂ by omega)
        linarith [bs.2, be.1]
      refine ⟨e₁ + 1, e₂, ?_, ?_, ?_, by omega, by omega, ?_, fun h => ?_, fun h => ?_⟩
      · rw [ite_eq_right hnU1]; exact Nat.mod_eq_of_lt (by omega)
      · push_cast; linarith [bs.2]
      · rw [ite_eq_right hnU]; exact Nat.mod_eq_of_lt (by omega)
      · rw [hT1 hT]; linarith [be.1]
      · rw [hT1 hT, hkeq]
        rcases h with h | h
        · exact absurd h hnU
        · linarith
      · rw [hT1 hT, hkeq]
        have : M.param Q e = 0 := by
          by_contra hc; exact h (Or.inr (lt_of_le_of_ne hp0 (Ne.symm hc)))
        rw [this]; ring
    · have hT : ¬ ks < ke := by
        rcases h3.lt_or_eq with hlt | heq
        · have : (e₂ : ℝ) + 1 ≤ e₁ := by exact_mod_cast hlt
          intro h; linarith [be.2, bs.1]
        · intro h; exact hsame ⟨heq.symm, h⟩
      refine ⟨e₁ + 1, e₂ + n, ?_, ?_, ?_, by omega, by omega, ?_, fun h => ?_, fun h => ?_⟩
      · rw [ite_eq_right hnU1]; exact Nat.mod_eq_of_lt (by omega)
      · push_cast; linarith [bs.2]
      · rw [ite_eq_right hnU, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      · rw [hT2 hT]; push_cast; linarith [be.1]
      · rw [hT2 hT, hkeq]
        rcases h with h | h
        · exact absurd h hnU
        · push_cast; linarith
      · rw [hT2 hT, hkeq]
        have : M.param Q e = 0 := by
          by_contra hc; exact h (Or.inr (lt_of_le_of_ne hp0 (Ne.symm hc)))
        rw [this]; push_cast; ring

end ShootCut

end

end Chazelle.Core
