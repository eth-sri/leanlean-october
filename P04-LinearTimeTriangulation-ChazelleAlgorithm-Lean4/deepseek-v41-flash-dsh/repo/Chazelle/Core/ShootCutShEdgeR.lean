module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShLoad

/-!
# WP-G, part 44: the ray-shooter on one segment of a walk edge (`edgeH`)

`edgeH` answers the segment from the walk position `U` (`140263`, `140264`) to the walk position
`V` (`140265`, `140266`) on the walk edge `140262`: it loads the point records of `U` and `V`,
compares heights and abscissae with the origin, and follows the decision tree `edgeSel`,
loading the record of the position `X = (140262, h + 1)` at the height of the origin when the
height of the origin is strictly between those of `U` and `V`.  The answer is a **candidate**
(`CandAt`) in `140220 … 140226`: flag, abscissa record, walk position.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-- **A candidate answer** at `b` for the set `S`: flag `b`, abscissa record `b + 1 …`, walk
position `b + 5`, `b + 6` of the hit point. -/
def CandAt (P : Polygon) (C : Chain) (c : Config) (b : ℕ) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg b ≤ 1 ∧ (c.nreg b ≠ 1 → NoHit S z σ) ∧
    (c.nreg b = 1 → ∃ x : ℝ, AbsRec P c (b + 1) x C.radius ∧ FirstHit S z σ (σ * (x - z.1)) ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ ∧
      c.nreg (b + 5) < (chainModel C).W.n ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (b + 5), c.nreg (b + 6)⟩ = (x, z.2))

theorem FrameB.wk {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (by cases hb : B r; rfl; exact absurd (hB r hb) (⊚ hr)),
    fun r hr => h.2.1 r (by cases hb : B r; rfl; exact absurd (hB r hb) (⊚ hr)),
    h.2.2⟩

/-- One register update is framed by any set containing the register. -/
theorem frameB_upd {B : ℕ → Bool} (c : Config) {r : ℕ} (v : ℕ) (hB : B r = true) :
    FrameB B c ({ c with nreg := upd c.nreg r v } : Config) :=
  ⟨fun r' hr' => by
    have : r' ≠ r := fun h => by rw [h, hB] at hr'; exact absurd hr' (⌖)
    simp [upd_other _ _ _ this], fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The registers written by the segment machine. -/
def Bedge (r : ℕ) : Bool :=
  Bprim r || decide (50200 ≤ r ∧ r < 50203) || decide (140220 ≤ r ∧ r < 140227) ||
    decide (140262 ≤ r ∧ r < 140330)

theorem Bedge_env (r : ℕ) (h : envR r) : Bedge r = false := by
  unfold envR at h
  simp only [Bedge, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, K1, ALLOC] at h ⊢
  omega

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## Leaves -/

/-- No candidate. -/
def cand0 : Stmt := .instr (.constN 140220 0)

theorem cand0_exec (c : Config) (hw : WordsBounded W c) {S : Set Point} (h : NoHit S z σ) :
    ∃ c' k, Exec P W cand0 c c' k ∧ k = 1 ∧ CandAt P C c' 140220 S z σ ∧
      FrameB Bedge c c' := by
  refine ⟨_, _, Exec.constN hw 140220 0 (by have := hw; exact Nat.zero_le _), rfl,
    ⟨✓, fun _ => h, fun h' => by simp at h'⟩, frameB_upd c 0 (by decide)⟩

/-- The candidate from the record at `A` and the position in `e`, `h`. -/
def candFrom (A e h : ℕ) : Stmt :=
  .seq (block (copies [(140221, A), (140222, A + 1), (140223, A + 2), (140224, A + 3),
    (140225, e), (140226, h)])) (.instr (.constN 140220 1))

theorem candFrom_exec (c : Config) (hw : WordsBounded W c) (hW1 : 1 ≤ W) {A e h : ℕ}
    (hA : A + 4 ≤ 140221 ∨ 140227 ≤ A) (he : e < 140221 ∨ 140227 ≤ e)
    (hh : h < 140221 ∨ 140227 ≤ h) {S : Set Point} {x : ℝ}
    (hx : AbsRec P c A x C.radius) (hF : FirstHit S z σ (σ * (x - z.1)))
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hen : c.nreg e < (chainModel C).W.n)
    (hpos : (chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ = (x, z.2)) :
    ∃ c' k, Exec P W (candFrom A e h) c c' k ∧ k = 7 ∧ CandAt P C c' 140220 S z σ ∧
      FrameB Bedge c c' := by
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P) [(140221, A),
    (140222, A + 1), (140223, A + 2), (140224, A + 3), (140225, e), (140226, h)] c hw
    (by simp; omega) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₁
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := v₁
  have e₂ := Exec.constN (P := P) e₁.wb_right 140220 1 hW1
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 140220 1 } with hc₂
  have g : ∀ r, r ≠ 140220 → c₂.nreg r = c₁.nreg r := fun r hr => by rw [hc₂]; simp [hr]
  refine ⟨c₂, _, .seq e₁ e₂, rfl, ⟨by simp [hc₂], fun h' => by simp [hc₂] at h', fun _ =>
    ⟨x, absRec_copy' hx (by rw [g _ (by norm_num), w1]) (by rw [g _ (by norm_num), w2])
      (by rw [g _ (by norm_num), w3]) (by rw [g _ (by norm_num), w4]), hF,
      by rw [g _ (by norm_num), g _ (by norm_num), w5, w6]; exact hp,
      by rw [g _ (by norm_num), w5]; exact hen,
      by rw [g _ (by norm_num), g _ (by norm_num), w5, w6]; exact hpos⟩⟩, ?_⟩
  refine ⟨fun r hr => ?_, fun r _ => by rw [show c₂.rreg = c₁.rreg from rfl, rr₁], by
    show c₁.nmem = c.nmem; exact m₁, by show c₁.rmem = c.rmem; exact rm₁,
    by show c₁.output = c.output; exact o₁⟩
  simp only [Bedge, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
  rw [g r (by omega), k₁ r (by simp; omega)]

/-! ## Ahead of the origin -/

/-- The bit "the point of the record at `A` is ahead of the origin". -/
def aheadT (A dst : ℕ) : Stmt := .ifLtN 140241 K1 (xLess A 140230 dst) (xLess 140230 A dst)

theorem aheadT_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) {A dst : ℕ}
    (hA : 10500 ≤ A) (hdst : 10500 ≤ dst) {x : ℝ} (hx : AbsRec P c A x C.radius)
    (hne : x ≠ z.1) :
    ∃ c' k, Exec P W (aheadT A dst) c c' k ∧ k ≤ 252 ∧ BitIs c' dst (0 < σ * (x - z.1)) ∧
      FrameB (Bkb dst) c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  unfold aheadT
  by_cases hs : c.nreg 140241 < c.nreg K1
  · have hσ : σ = -1 := by
      rcases E.hσ with h | h
      · have := E.sig.2.2 h; rw [E.k1] at hs; omega
      · exact h
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw hA (⊛) hdst E.k1 (AbsRec.weak hx)
      E.ox (Or.inl hne)
    refine ⟨c', _, .ifLtN_true hs ex, ⋄, bt.congr ?_, f⟩
    rw [hσ]; constructor <;> intro h <;> linarith
  · have hσ : σ = 1 := E.sig.2.1 (by rw [E.k1] at hs; have := E.sig.1; omega)
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw (⊛) hA hdst E.k1 E.ox
      (AbsRec.weak hx) (Or.inl (Ne.symm hne))
    refine ⟨c', _, .ifLtN_false hs ex, ⋄, bt.congr ?_, f⟩
    rw [hσ]; constructor <;> intro h <;> linarith

/-- The bit "`V` is nearer than `U`" (the negation of `σ U.1 ≤ σ V.1`). -/
def nearT (dst : ℕ) : Stmt := .ifLtN 140241 K1 (xLess 140270 140281 dst) (xLess 140281 140270 dst)

theorem nearT_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) {dst : ℕ}
    (hdst : 10500 ≤ dst) {xU xV : ℝ} (hU : AbsRec P c 140270 xU C.radius)
    (hV : AbsRec P c 140281 xV C.radius) :
    ∃ c' k, Exec P W (nearT dst) c c' k ∧ k ≤ 252 ∧ BitIs c' dst (¬ σ * xU ≤ σ * xV) ∧
      FrameB (Bkb dst) c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  have st : ∀ {r : ℕ} {x : ℝ}, AbsRec P c r x C.radius → c.nreg r = 1 → |x| < C.radius :=
    fun {r} {x} h hk => by
      rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hx, -⟩ <;> [omega; omega; exact hx]
  unfold nearT
  by_cases hs : c.nreg 140241 < c.nreg K1
  · have hσ : σ = -1 := by
      rcases E.hσ with h | h
      · have := E.sig.2.2 h; rw [E.k1] at hs; omega
      · exact h
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw (⊛) (by norm_num) hdst E.k1
      (AbsRec.weak hU) (AbsRec.weak hV) (Or.inr ⟨st hU, st hV⟩)
    refine ⟨c', _, .ifLtN_true hs ex, ⋄, bt.congr ?_, f⟩
    rw [hσ]; constructor <;> intro h
    · intro h'; linarith
    · push Not at h; linarith
  · have hσ : σ = 1 := E.sig.2.1 (by rw [E.k1] at hs; have := E.sig.1; omega)
    obtain ⟨c', k, ex, hk, bt, f⟩ := xLess_exec E.hG hW c hw (⊛) (by norm_num) hdst E.k1
      (AbsRec.weak hV) (AbsRec.weak hU) (Or.inr ⟨st hV, st hU⟩)
    refine ⟨c', _, .ifLtN_false hs ex, ⋄, bt.congr ?_, f⟩
    rw [hσ]; constructor <;> intro h
    · intro h'; linarith
    · push Not at h; linarith

end

end ShootCut

end Chazelle.Core
