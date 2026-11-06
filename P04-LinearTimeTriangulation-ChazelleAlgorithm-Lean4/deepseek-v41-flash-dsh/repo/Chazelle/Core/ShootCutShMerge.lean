module

public import Chazelle.Core.ShootCutShEdgeH

/-!
# WP-G, part 46: keeping the nearest candidate

`mrg`: the best answer so far (`CandAt` at `140210`, for the set `S₁` shot so far) and a new
candidate (`CandAt` at `140220`, for `S₂`) give the best answer for `S₁ ∪ S₂` (`cand_union`):
the candidate replaces the best one if the best one is empty or the candidate is nearer in the
direction of the ray (one `xLess`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-- Copy the candidate over the best answer. -/
def copyC : Stmt :=
  block (copies [(140210, 140220), (140211, 140221), (140212, 140222), (140213, 140223),
    (140214, 140224), (140215, 140225), (140216, 140226)])

/-- The comparison bit: the candidate is nearer. -/
def cmpT : Stmt := .ifLtN 140241 K1 (xLess 140211 140221 140310) (xLess 140221 140211 140310)

/-- **Keep the nearest.** -/
def mrg : Stmt :=
  .ifLtN 140220 K1 .skip (.ifLtN 140210 K1 copyC (.seq cmpT (.ifLtN 140310 K1 .skip copyC)))

/-- The registers written by `mrg`. -/
def Bmrg (r : ℕ) : Bool := Bk r || decide (140210 ≤ r ∧ r < 140217) || r == 140310

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

theorem CandAt.cand {c : Config} {b : ℕ} {S : Set Point} (h : CandAt P C c b S z σ) :
    ∃ x : ℝ, Cand S z σ (c.nreg b) x ∧ (c.nreg b = 1 → AbsRec P c (b + 1) x C.radius ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ ∧
      c.nreg (b + 5) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ = (x, z.2)) := by
  by_cases h1 : c.nreg b = 1
  · obtain ⟨x, a, f, p, n, q⟩ := h.2.2 h1
    exact ⟨x, ⟨fun _ => f, fun h' => absurd h1 h'⟩, fun _ => ⟨a, p, n, q⟩⟩
  · exact ⟨0, ⟨fun h' => absurd h' h1, fun _ => h.2.1 h1⟩, fun h' => absurd h' h1⟩

theorem CandAt.of_cand {c : Config} {b : ℕ} {S : Set Point} {x : ℝ} (hb : c.nreg b ≤ 1)
    (hc : Cand S z σ (c.nreg b) x)
    (hr : c.nreg b = 1 → AbsRec P c (b + 1) x C.radius ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ ∧
      c.nreg (b + 5) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ = (x, z.2)) :
    CandAt P C c b S z σ :=
  ⟨hb, hc.2, fun h1 => ⟨x, (hr h1).1, hc.1 h1, (hr h1).2⟩⟩

theorem copyC_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W copyC c c' 7 ∧ (∀ j, j < 7 → c'.nreg (140210 + j) = c.nreg (140220 + j)) ∧
      FrameB Bmrg c c' := by
  obtain ⟨c', e, v, k, rr, m, rm, o⟩ := copies_exec (P := P) [(140210, 140220), (140211, 140221),
    (140212, 140222), (140213, 140223), (140214, 140224), (140215, 140225), (140216, 140226)] c hw
    (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v
  refine ⟨c', e, fun j hj => ?_, fun r hr => k r (by simp [Bmrg] at hr ⊢; omega),
    fun r _ => by rw [rr], m, rm, o⟩
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := v
  interval_cases j <;> simp only [Nat.reduceAdd] <;> assumption

/-- The register facts of a candidate copied over the best answer. -/
theorem recs_copied {c c' : Config} {x : ℝ}
    (hk : ∀ j, j < 7 → c'.nreg (140210 + j) = c.nreg (140220 + j))
    (r : c.nreg 140220 = 1 → AbsRec P c (140220 + 1) x C.radius ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (140220 + 5), c.nreg (140220 + 6)⟩ ∧
      c.nreg (140220 + 5) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (140220 + 5), c.nreg (140220 + 6)⟩ = (x, z.2)) :
    c'.nreg 140210 = 1 → AbsRec P c' (140210 + 1) x C.radius ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c'.nreg (140210 + 5), c'.nreg (140210 + 6)⟩ ∧
      c'.nreg (140210 + 5) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c'.nreg (140210 + 5), c'.nreg (140210 + 6)⟩ = (x, z.2) := by
  have h0 := hk 0 (by norm_num)
  simp only [Nat.add_zero] at h0
  intro h1
  obtain ⟨a, p, n, q⟩ := r (by rw [← h0]; exact h1)
  rw [hk 5 (by norm_num), hk 6 (by norm_num)]
  exact ⟨absRec_copy' a (hk 1 (by norm_num)) (hk 2 (by norm_num)) (hk 3 (by norm_num))
    (hk 4 (by norm_num)), p, n, q⟩

theorem mrg_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {S₁ S₂ : Set Point} (hB : CandAt P C c 140210 S₁ z σ) (hC : CandAt P C c 140220 S₂ z σ) :
    ∃ c' k, Exec P W mrg c c' k ∧ k ≤ 270 ∧ CandAt P C c' 140210 (S₁ ∪ S₂) z σ ∧
      FrameB Bmrg c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  have k1 := E.k1
  obtain ⟨x₁, c₁', r₁⟩ := hB.cand
  obtain ⟨x₂, c₂', r₂⟩ := hC.cand
  have hu := cand_union E.hσ c₁' c₂'
  unfold mrg
  by_cases t0 : c.nreg 140220 < c.nreg K1
  · -- no candidate: keep
    have hf₂ : ¬ c.nreg 140220 = 1 := by rw [k1] at t0; omega
    simp only [hf₂, false_and, ↓reduceIte] at hu
    exact ⟨c, _, .ifLtN_true t0 (.skip hw), by norm_num, CandAt.of_cand hB.1 hu r₁,
      FrameB.refl _ _⟩
  have hf₂ : c.nreg 140220 = 1 := by have := hC.1; rw [k1] at t0; omega
  by_cases t1 : c.nreg 140210 < c.nreg K1
  · have hf₁ : ¬ c.nreg 140210 = 1 := by rw [k1] at t1; omega
    simp only [hf₂, hf₁, ne_eq, not_false_eq_true, true_or, and_self, ↓reduceIte] at hu
    obtain ⟨c', e, hk, f⟩ := copyC_exec (P := P) c hw
    have h0 : c'.nreg 140210 = c.nreg 140220 := hk 0 (by norm_num)
    refine ⟨c', _, .ifLtN_false t0 (.ifLtN_true t1 e), by norm_num,
      CandAt.of_cand (by rw [h0, hf₂]) (by rw [h0, hf₂]; exact hu) (recs_copied hk r₂), f⟩
  have hf₁ : c.nreg 140210 = 1 := by have := hB.1; rw [k1] at t1; omega
  obtain ⟨xr₁, -⟩ := r₁ hf₁
  obtain ⟨xr₂, -⟩ := r₂ hf₂
  -- the comparison bit
  have st : ∀ {r : ℕ} {x : ℝ}, AbsRec P c r x C.radius → c.nreg r = 1 → |x| < C.radius :=
    fun {r} {x} h hk => by
      rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hx, -⟩ <;> [omega; omega; exact hx]
  obtain ⟨c₁, k₁, e₁, hk₁, bt, f₁⟩ : ∃ c₁ k₁, Exec P W cmpT c c₁ k₁ ∧ k₁ ≤ 252 ∧
      BitIs c₁ 140310 (σ * x₂ < σ * x₁) ∧ FrameB (Bkb 140310) c c₁ := by
    unfold cmpT
    by_cases hs : c.nreg 140241 < c.nreg K1
    · have hσ : σ = -1 := by
        rcases E.hσ with h | h
        · have := E.sig.2.2 h; rw [k1] at hs; omega
        · exact h
      obtain ⟨c₁, k, ex, hk, b, f⟩ := xLess_exec E.hG hW c hw (dst := 140310) (by norm_num) (by norm_num)
        (by norm_num) k1 (AbsRec.weak xr₁) (AbsRec.weak xr₂) (Or.inr ⟨st xr₁, st xr₂⟩)
      refine ⟨c₁, _, .ifLtN_true hs ex, by omega, b.congr ?_, f⟩
      rw [hσ]; constructor <;> intro h <;> linarith
    · have hσ : σ = 1 := E.sig.2.1 (by rw [k1] at hs; have := E.sig.1; omega)
      obtain ⟨c₁, k, ex, hk, b, f⟩ := xLess_exec E.hG hW c hw (dst := 140310) (by norm_num) (by norm_num)
        (by norm_num) k1 (AbsRec.weak xr₂) (AbsRec.weak xr₁) (Or.inr ⟨st xr₂, st xr₁⟩)
      refine ⟨c₁, _, .ifLtN_false hs ex, by omega, b.congr ?_, f⟩
      rw [hσ]; constructor <;> intro h <;> linarith
  have kp : ∀ r, 140210 ≤ r → r < 140227 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp [Bkb, Bk]; omega)
  have fm₁ : FrameB Bmrg c c₁ := FrameB.wk f₁ (fun r h => by
    simp only [Bkb, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Bmrg, Bool.or_eq_true, beq_iff_eq]
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h)
  have w₁ := e₁.wb_right
  have k1' : c₁.nreg K1 = 1 := by rw [f₁.1 K1 (by decide), k1]
  have t0' : ¬ c.nreg 140220 < c.nreg K1 := t0
  have t1' : ¬ c.nreg 140210 < c.nreg K1 := t1
  by_cases t2 : c₁.nreg 140310 < c₁.nreg K1
  · have hn : ¬ σ * x₂ < σ * x₁ := fun h => by have := bt.2.2 h; rw [k1'] at t2; omega
    simp only [hf₂, hf₁, ne_eq, not_true_eq_false, false_or, hn, and_false, ↓reduceIte] at hu
    refine ⟨c₁, _, .ifLtN_false t0' (.ifLtN_false t1' (.seq e₁ (.ifLtN_true t2 (.skip w₁)))),
      by omega, CandAt.of_cand (by rw [kp _ (by norm_num) (by norm_num), hf₁])
        (by rw [kp _ (by norm_num) (by norm_num), hf₁]; exact hu) (fun h => ?_), fm₁⟩
    obtain ⟨a, p, n, q⟩ := r₁ (by rw [← kp _ (by norm_num) (by norm_num)]; exact h)
    rw [kp _ (by norm_num) (by norm_num), kp _ (by norm_num) (by norm_num)]
    exact ⟨absRec_copy' a (kp _ (by norm_num) (by norm_num)) (kp _ (by norm_num) (by norm_num))
      (kp _ (by norm_num) (by norm_num)) (kp _ (by norm_num) (by norm_num)), p, n, q⟩
  · have hn : σ * x₂ < σ * x₁ := bt.2.1 (by have := bt.1; rw [k1'] at t2; omega)
    simp only [hf₂, hf₁, ne_eq, not_true_eq_false, false_or, hn, and_self, ↓reduceIte] at hu
    obtain ⟨c', e, hk, f⟩ := copyC_exec (P := P) c₁ w₁
    have hk' : ∀ j, j < 7 → c'.nreg (140210 + j) = c.nreg (140220 + j) := fun j hj => by
      rw [hk j hj, kp _ (by omega) (by omega)]
    have h0 : c'.nreg 140210 = c.nreg 140220 := hk' 0 (by norm_num)
    refine ⟨c', _, .ifLtN_false t0' (.ifLtN_false t1' (.seq e₁ (.ifLtN_false t2 e))), by omega,
      CandAt.of_cand (by rw [h0, hf₂]) (by rw [h0, hf₂]; exact hu) (recs_copied hk' r₂),
      fm₁.trans f⟩

end

end ShootCut

end Chazelle.Core
