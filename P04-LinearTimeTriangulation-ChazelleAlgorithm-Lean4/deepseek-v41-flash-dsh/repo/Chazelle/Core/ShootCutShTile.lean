module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutArc
public import Chazelle.Core.SweepHit

/-!
# WP-G, part 37: the ray-shooter's subarc is the union of its pieces

The ray-shooter decomposes its subarc into the pieces of the core (`ArcOK`) and keeps the nearest
first hit on them.

* `kpath_wset`, `arcSet_pieces`: the point set of the subarc is the union of the point sets of
  the pieces;
* `Cand`: a candidate answer on a set (a flag and the abscissa of the hit point), and
  `cand_union`: the nearer of two candidates is a candidate on the union.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Sweep (FirstHitOpt omin firstHitOpt_union firstHit_unique)

namespace ShootCut

/-! ## The union of the pieces -/

/-- Two reals in `(0, n]` that differ by a multiple of `n` are equal. -/
theorem eq_of_unw_pos {n a b : ℝ} (hn : 0 < n) (ha : 0 < a ∧ a ≤ n) (hb : 0 < b ∧ b ≤ n)
    {i j : ℤ} (h : a + i * n = b + j * n) : a = b := by
  have := key_eq_of_unw hn (x := n - a) (y := n - b) ⟨⟡, by linarith⟩
    ⟨⟡, by linarith⟩ (i := j) (j := i) (by linarith)
  linarith

/-- **A path of pieces through unwrapped keys** covers the unwrapped interval. -/
theorem kpath_wset {M : Model} {Q : Polygon} (hn : 0 < M.W.n) :
    ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q (M.W.n : ℝ) V ps V' → ps ≠ [] →
      V' ≤ V + M.W.n →
      (∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < M.W.n) ∧
        (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < M.W.n)) →
      wset M V V' = ⋃ pc ∈ ps, M.arcSet (M.key Q pc.s) (M.key Q pc.e)
  | _, [], _, _, hne, _, _ => absurd rfl hne
  | V, pc :: ps, V', ⟨⟨i, hi⟩, V₁, hV₁, ⟨j, hj⟩, hrest⟩, _, hle, hk => by
    have hn' : (0 : ℝ) < M.W.n := by exact_mod_cast hn
    have hk₀ := hk pc (List.mem_cons_self ..)
    have hV₁' := hrest.le
    -- the first piece ends at `V + len`
    obtain ⟨j', hj'⟩ := T_unw (M.key Q pc.s) (M.key Q pc.e) (M.W.n : ℝ)
    have hL := len_pos (M.W.n : ℝ) (M.key Q pc.s) (M.key Q pc.e) hk₀.1.2 hk₀.2.1
    have hL' := len_le (M.W.n : ℝ) (M.key Q pc.s) (M.key Q pc.e) hk₀.1.1 hk₀.2.2
    have hstep : V₁ - V = len (M.W.n : ℝ) (M.key Q pc.s) (M.key Q pc.e) :=
      eq_of_unw_pos hn' ⟨⟡, by linarith⟩ ⟨hL, hL'⟩ (i := j' + i) (j := j)
        (by push_cast; linarith)
    have hpc : M.arcSet (M.key Q pc.s) (M.key Q pc.e) = wset M V V₁ := by
      Ξ arcSet_step M hk₀.1.1 hk₀.1.2 hk₀.2.1 hk₀.2.2 i, ← hi
      congr 1; linarith
    have e : (⋃ q ∈ pc :: ps, M.arcSet (M.key Q q.s) (M.key Q q.e)) =
        M.arcSet (M.key Q pc.s) (M.key Q pc.e) ∪
          ⋃ q ∈ ps, M.arcSet (M.key Q q.s) (M.key Q q.e) := by
      ext x; simp
    Ξ e, hpc
    by_cases hne' : ps = []
    · subst hne'
      have : V₁ = V' := hrest
      subst this
      simp
    · rw [← kpath_wset hn hrest hne' (⟡) (fun pc' hpc' => hk pc'
        (List.mem_cons_of_mem _ hpc')), wset_union M hV₁.le hV₁']

variable {C : Chain} {Q : Polygon}

/-- **The subarc is the union of its pieces.** -/
theorem arcSet_pieces {s e : WPos} {ps : List Pc} (hA : ArcOK C Q s e ps)
    (hs : 0 ≤ (chainModel C).key Q s ∧ (chainModel C).key Q s < ((2 * C.m + 7 : ℕ) : ℝ))
    (he : 0 ≤ (chainModel C).key Q e ∧ (chainModel C).key Q e < ((2 * C.m + 7 : ℕ) : ℝ))
    (hk : ∀ pc ∈ ps, (0 ≤ (chainModel C).key Q pc.s ∧
        (chainModel C).key Q pc.s < ((2 * C.m + 7 : ℕ) : ℝ)) ∧
      (0 ≤ (chainModel C).key Q pc.e ∧ (chainModel C).key Q pc.e < ((2 * C.m + 7 : ℕ) : ℝ))) :
    (chainModel C).arcSet ((chainModel C).key Q s) ((chainModel C).key Q e) =
      ⋃ pc ∈ ps, (chainModel C).arcSet ((chainModel C).key Q pc.s)
        ((chainModel C).key Q pc.e) := by
  set M := chainModel C
  have hnW : M.W.n = 2 * C.m + 7 := chainModel_n C
  have hn : 0 < M.W.n := ⋄
  have hkp := hA.kp
  rw [← hnW] at hkp hs he hk
  have hL' := len_le (M.W.n : ℝ) (M.key Q s) (M.key Q e) hs.1 he.2
  rw [← kpath_wset hn hkp hA.ne (⟡) hk, arcSet_eq_wset M hs.1 hs.2 he.1 he.2]
  congr 1
  unfold len; split_ifs <;> ring

/-! ## Candidates -/

theorem sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

/-- **A candidate answer** on `S`: flag `1` and the first hit at abscissa `x`, or no hit. -/
def Cand (S : Set Point) (z : Point) (σ : ℝ) (f : ℕ) (x : ℝ) : Prop :=
  (f = 1 → FirstHit S z σ (σ * (x - z.1))) ∧ (f ≠ 1 → NoHit S z σ)

/-- The option of a candidate. -/
noncomputable def candOpt (z : Point) (σ : ℝ) (f : ℕ) (x : ℝ) : Option ℝ :=
  if f = 1 then some (σ * (x - z.1)) else none

theorem cand_iff {S : Set Point} {z : Point} {σ : ℝ} {f : ℕ} {x : ℝ} :
    Cand S z σ f x ↔ FirstHitOpt S z σ (candOpt z σ f x) := by
  unfold Cand candOpt
  by_cases hf : f = 1
  · rw [ite_eq_left hf]; exact ⟨fun h => h.1 hf, fun h => ⟨fun _ => h, fun h' => absurd hf h'⟩⟩
  · rw [ite_eq_right hf]; exact ⟨fun h => h.2 hf, fun h => ⟨fun h' => absurd h' hf, fun _ => h⟩⟩

/-- **The nearer of two candidates** is a candidate on the union. -/
theorem cand_union {S₁ S₂ : Set Point} {z : Point} {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1) {f₁ f₂ : ℕ}
    {x₁ x₂ : ℝ} (h₁ : Cand S₁ z σ f₁ x₁) (h₂ : Cand S₂ z σ f₂ x₂) :
    Cand (S₁ ∪ S₂) z σ (if f₂ = 1 ∧ (f₁ ≠ 1 ∨ σ * x₂ < σ * x₁) then 1 else f₁)
      (if f₂ = 1 ∧ (f₁ ≠ 1 ∨ σ * x₂ < σ * x₁) then x₂ else x₁) := by
  have hu := firstHitOpt_union (cand_iff.1 h₁) (cand_iff.1 h₂)
  Ξ cand_iff
  convert hu using 1
  unfold candOpt omin
  by_cases hf₂ : f₂ = 1 <;> by_cases hf₁ : f₁ = 1
  · by_cases hlt : σ * x₂ < σ * x₁
    · ϴ hf₂, hf₁, hlt, ne_eq, not_true_eq_false, or_true, and_self, ite_true
      congr 1; rw [min_eq_right (⊞)]
    · simp only [hf₂, hf₁, hlt, ne_eq, not_true_eq_false, or_false, and_false, ite_false,
        ite_true]
      congr 1; rw [min_eq_left (by push Not at hlt; nlinarith)]
  · Θ hf₂, hf₁
  · Θ hf₂, hf₁
  · Θ hf₂, hf₁

end ShootCut

end

end Chazelle.Core
