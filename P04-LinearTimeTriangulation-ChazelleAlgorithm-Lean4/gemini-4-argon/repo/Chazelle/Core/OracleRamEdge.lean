module

public import Chazelle.Core.OracleRamSig
public import Chazelle.Core.OracleScan

/-!
# Lemma 3.6 (WP-H), RAM part 2: testing one edge of the chain

`edgeT` tests the chain edge `ci` (register `120060`) against the query ray and keeps the best
hit so far (registers `120050` flag, `120051` its edge of `Q`, `120052` its chain edge):

1. `e := (s + ci) mod n`, `e₁ := (e + 1) mod n` (`120061`, `120062`);
2. the height of the ray (vertex `hz`, register `120023`) is in the range of edge `e`: `hz = e`,
   `hz = e₁`, or two height tests with the sign kernel (`120063`);
3. the point of the edge at that height is ahead of the origin (always for a box origin; one
   abscissa test otherwise) (`120066`);
4. it improves on the best hit (one abscissa test) (`120067`); then it becomes the best hit.

Registers read: `120010` `n`, `120011` the constant `1`, `120015` `s`, `120023` `hz`, `120024`
the direction bit (`1`: rightwards), `120025 … 120027` the origin (kind `0, 1`: a symbolic point;
`2`: a box point), `120048` the constant `2`.  Main result: `edgeT_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## Small statements -/

/-- `r := r mod n` for `r < 2 n`. -/
def modSub (r nr : ℕ) : Stmt := .ifLtN r nr .skip (.instr (.subN r r nr))

/-- Run `S` if registers `a` and `b` are equal, `T` otherwise. -/
def ifEq (a b : ℕ) (S T : Stmt) : Stmt := .ifLtN a b T (.ifLtN b a T S)

theorem modSub_exec {P : Polygon} {W : ℕ} {r nr : ℕ} (_hr : r ≠ nr) (c : Config)
    (hw : WordsBounded W c) (hv : c.nreg r < 2 * c.nreg nr) :
    ∃ c' k, Exec P W (modSub r nr) c c' k ∧ k ≤ 3 ∧ c'.nreg r = c.nreg r % c.nreg nr ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold modSub
  by_cases h : c.nreg r < c.nreg nr
  · refine spec_ifLtN_true h (spec_skip hw ⟨by omega, Nat.mod_eq_of_lt h |>.symm, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩)
  · refine spec_ifLtN_false h (spec_instr (Exec.subN hw r r nr) fun _ => ?_)
    refine ⟨by omega, ?_, fun r' h' => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · config_simp; rw [Machine.upd_other _ _ _ h']

/-! ## The semantics of one test -/

section Sem

variable (Q : Polygon) (s hz : ℕ) (σ : ℝ) (zo : Option Point)

/-- The edge of `Q` of chain edge `ci`. -/
def eIdx (n s ci : ℕ) : ℕ := (s + ci) % n

/-- The point at abscissa `x` is ahead of the origin (`none`: a box origin, always ahead). -/
def Ahead (x : ℝ) : Prop :=
  match zo with
  | none => True
  | some z => (σ = 1 ∧ z.1 < x) ∨ (σ = -1 ∧ x < z.1)

/-- **The ray hits chain edge `ci`** (height in range, point ahead). -/
def HitC (ci : ℕ) : Prop :=
  Spans Q (eIdx Q.n s ci) hz ∧ Ahead σ zo (xe Q (eIdx Q.n s ci) hz)

/-- **The hit on chain edge `ci` comes before the hit on `cb`.** -/
def BetterC (ci cb : ℕ) : Prop :=
  (σ = 1 ∧ xe Q (eIdx Q.n s ci) hz < xe Q (eIdx Q.n s cb) hz) ∨
    (σ = -1 ∧ xe Q (eIdx Q.n s cb) hz < xe Q (eIdx Q.n s ci) hz)

open Classical in
/-- **One step of the scan**: the new best chain edge. -/
noncomputable def upd1 (best : Option ℕ) (ci : ℕ) : Option ℕ :=
  if HitC Q s hz σ zo ci ∧ (∀ cb, best = some cb → BetterC Q s hz σ ci cb) then some ci else best

end Sem

/-- The best chain edge held in the registers. -/
def bestOf (c : Config) : Option ℕ := if c.nreg 120050 = 1 then some (c.nreg 120052) else none

/-- The best-hit registers are consistent. -/
def BestOK (n s mb : ℕ) (c : Config) : Prop :=
  c.nreg 120050 ≤ 1 ∧ (c.nreg 120050 = 1 → c.nreg 120051 = eIdx n s (c.nreg 120052) ∧
    c.nreg 120052 < mb)

/-- The direction of a direction bit. -/
noncomputable def sgnOf (b : ℕ) : ℝ := if b = 1 then 1 else -1

/-- **The origin registers** `120025 …` describe the origin `zo` (`none`: a box origin). -/
def OriginOK (P : Polygon) (c : Config) (zo : Option Point) : Prop :=
  (c.nreg 120025 = 2 ∧ zo = none) ∨
    (c.nreg 120025 < 2 ∧ ∃ p : SymPt, p.Lt P.n ∧ SymPtIn c 120025 p ∧ zo = some (p.eval (Qof P)))

/-- **The constants the edge test reads.** -/
structure EConst (P : Polygon) (s hz : ℕ) (σb : ℕ) (zo : Option Point) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  two : c.nreg 120048 = 2
  rs : c.nreg 120015 = s
  rhz : c.nreg 120023 = hz
  rσ : c.nreg 120024 = σb
  σle : σb ≤ 1
  org : OriginOK P c zo
  s_lt : s < P.n
  hz_lt : hz < P.n

/-- The registers written by the edge test. -/
def BE (r : ℕ) : Bool :=
  Bk r || decide (120050 ≤ r ∧ r ≤ 120052) || decide (120061 ≤ r ∧ r ≤ 120067)

/-! ## The program -/

/-- The height range test (`120063 := 1` iff the height of `hz` is in the range of `e`). -/
def spansS : Stmt :=
  let gen : Stmt :=
    .seq (sgnS 1 (.vtx 120061) (.vtx 120023) (.vtx 120061))
      (.seq (.instr (.copyN 120064 10010))
        (.seq (sgnS 1 (.vtx 120023) (.vtx 120062) (.vtx 120061))
          (.seq (.instr (.copyN 120065 10010))
            (ifEq 120064 120065 (.instr (.constN 120063 1)) (.instr (.constN 120063 0))))))
  ifEq 120023 120061 (.instr (.constN 120063 1))
    (ifEq 120023 120062 (.instr (.constN 120063 1)) gen)

/-- The ahead test (`120066`). -/
def aheadS : Stmt :=
  .ifLtN 120025 120048
    (.ifLtN 120024 120011
      (.seq (sgnS 0 (.edge 120061 120023) (.regs 120025) (.vtx 120061))
        (.instr (.copyN 120066 10010)))
      (.seq (sgnS 0 (.regs 120025) (.edge 120061 120023) (.vtx 120061))
        (.instr (.copyN 120066 10010))))
    (.instr (.constN 120066 1))

/-- Take the tested edge as the best hit. -/
def takeS : Stmt := block [.constN 120050 1, .copyN 120051 120061, .copyN 120052 120060]

/-- The comparison with the best hit (`120067`), then the update. -/
def betterS : Stmt :=
  .ifLtN 120050 120011 takeS
    (.seq (.ifLtN 120024 120011
        (.seq (sgnS 0 (.edge 120051 120023) (.edge 120061 120023) (.vtx 120061))
          (.instr (.copyN 120067 10010)))
        (.seq (sgnS 0 (.edge 120061 120023) (.edge 120051 120023) (.vtx 120061))
          (.instr (.copyN 120067 10010))))
      (.ifLtN 120067 120011 .skip takeS))

/-- **The edge test.** -/
def edgeT : Stmt :=
  .seq (.instr (.addN 120061 120015 120060)) (.seq (modSub 120061 120010)
    (.seq (.instr (.addN 120062 120061 120011)) (.seq (modSub 120062 120010)
      (.seq spansS (.ifLtN 120063 120011 .skip
        (.seq aheadS (.ifLtN 120066 120011 .skip betterS)))))))

end

end OracleR

end Chazelle.Core

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## Execution lemmas -/

section Exec
variable {P : Polygon} {W : ℕ}

theorem ifEq_eq_exec {a b : ℕ} {S T : Stmt} {c c' : Config} {k : ℕ} (h : c.nreg a = c.nreg b)
    (hS : Exec P W S c c' k) : Exec P W (ifEq a b S T) c c' (k + 2 + 2) :=
  .ifLtN_false (by omega) (.ifLtN_false (by omega) hS)

theorem ifEq_ne_exec {a b : ℕ} {S T : Stmt} {c c' : Config} {k : ℕ} (h : c.nreg a ≠ c.nreg b)
    (hT : Exec P W T c c' k) : ∃ k', Exec P W (ifEq a b S T) c c' k' ∧ k' ≤ k + 3 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ⟨_, .ifLtN_true hlt hT, by omega⟩
  · exact ⟨_, .ifLtN_false (by omega) (.ifLtN_true hgt hT), by omega⟩

/-- The value of a `copyN` after a statement. -/
theorem copy_exec {c : Config} (hw : WordsBounded W c) (r a : ℕ) :
    ∃ c', Exec P W (.instr (.copyN r a)) c c' 1 ∧ c'.nreg r = c.nreg a ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') :=
  ⟨_, Exec.copyN hw r a, by config_simp, fun r' h => by config_simp; rw [Machine.upd_other _ _ _ h]⟩

theorem const_exec {c : Config} (hw : WordsBounded W c) (r v : ℕ) (hv : v ≤ W) :
    ∃ c', Exec P W (.instr (.constN r v)) c c' 1 ∧ c'.nreg r = v ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') :=
  ⟨_, Exec.constN hw r v hv, by config_simp, fun r' h => by
    config_simp; rw [Machine.upd_other _ _ _ h]⟩

/-- **The height range test.** -/
theorem spansS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hD : DistinctHeights (Qof P))
    (c : Config) (hw : WordsBounded W c) (he : c.nreg 120061 < P.n)
    (he1 : c.nreg 120062 = (c.nreg 120061 + 1) % P.n) (hhz : c.nreg 120023 < P.n) :
    ∃ c' k, Exec P W spansS c c' k ∧ k ≤ 520 ∧ c'.nreg 120063 ≤ 1 ∧
      (c'.nreg 120063 = 1 ↔ Spans (Qof P) (c.nreg 120061) (c.nreg 120023)) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : 0 < P.n := by omega
  set e := c.nreg 120061
  set e1 := c.nreg 120062
  set hz := c.nreg 120023
  have he1n : e1 < P.n := by rw [he1]; exact Nat.mod_lt _ hn
  have hsp := spans_iff (Qof P) hD (show e < (Qof P).n by omega) (show hz < (Qof P).n by omega)
  rw [hQn, ← he1] at hsp
  by_cases h1 : hz = e
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120063 1 (by omega)
    refine ⟨c₁, _, ifEq_eq_exec (T := ifEq 120023 120062 (.instr (.constN 120063 1)) _) h1 e₁,
      by omega, by rw [v₁], ?_⟩
    rw [v₁, hsp]; simp [h1]
  by_cases h2 : hz = e1
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120063 1 (by omega)
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := .instr (.constN 120063 1)) h1
      (ifEq_eq_exec (T := _) h2 e₁)
    refine ⟨c₁, k', ex', by omega, by rw [v₁], ?_⟩
    rw [v₁, hsp]; simp [h2]
  -- two height tests
  have hl : ∀ i, i < P.n → (SymPt.vtx i).Lt P.n := fun i hi => hi
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 1 (by norm_num)
    (.vtx 120061) (.vtx 120023) (.vtx 120061) c hw (by decide) (by decide) (by decide)
    rfl rfl rfl (hl _ he) (hl _ hhz) (hl _ he)
  obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec (P := P) e₁.wb_right 120064 10010
  have g₂ : ∀ r, Bk r = false → r ≠ 120064 → c₂.nreg r = c.nreg r := fun r hr hr' =>
    (r₂ r hr').trans (f₁.1 r hr)
  have x61 : c₂.nreg 120061 = e := g₂ _ (by decide) (by decide)
  have x62 : c₂.nreg 120062 = e1 := g₂ _ (by decide) (by decide)
  have x23 : c₂.nreg 120023 = hz := g₂ _ (by decide) (by decide)
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, s₃⟩ := sgnS_exec (P := P) hG hW 1 (by norm_num)
    (.vtx 120023) (.vtx 120062) (.vtx 120061) c₂ e₂.wb_right (by decide) (by decide) (by decide)
    rfl rfl rfl (by rw [x23]; exact hl _ hhz) (by rw [x62]; exact hl _ he1n)
    (by rw [x61]; exact hl _ he)
  obtain ⟨c₄, e₄, v₄, r₄⟩ := copy_exec (P := P) e₃.wb_right 120065 10010
  rw [x61, x62, x23] at s₃
  simp only [SignTest, SymPt.eval] at s₁ s₃
  have t1 : c₄.nreg 120064 = c₁.nreg 10010 := by
    rw [r₄ _ (by decide), f₃.1 _ (by decide), v₂]
  have t2 : c₄.nreg 120065 = c₃.nreg 10010 := v₄
  have ne1 := hD hz e (by omega) (by omega) h1
  have ne2 := hD hz e1 (by omega) (by omega) h2
  -- the final comparison of the two bits
  obtain ⟨c₅, k₅, e₅, hk₅, u₅, v₅⟩ : ∃ c₅ k₅, Exec P W (ifEq 120064 120065
      (.instr (.constN 120063 1)) (.instr (.constN 120063 0))) c₄ c₅ k₅ ∧ k₅ ≤ 6 ∧
      c₅.nreg 120063 ≤ 1 ∧ (c₅.nreg 120063 = 1 ↔ c₁.nreg 10010 = c₃.nreg 10010) := by
    by_cases hq : c₄.nreg 120064 = c₄.nreg 120065
    · obtain ⟨c₅, e₅, v₅, -⟩ := const_exec (P := P) e₄.wb_right 120063 1 (by omega)
      refine ⟨c₅, _, ifEq_eq_exec hq e₅, by omega, by rw [v₅], ?_⟩
      rw [v₅, ← t1, ← t2]; simp [hq]
    · obtain ⟨c₅, e₅, v₅, -⟩ := const_exec (P := P) e₄.wb_right 120063 0 (by omega)
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := .instr (.constN 120063 1)) hq e₅
      refine ⟨c₅, k', ex', by omega, by rw [v₅]; omega, ?_⟩
      rw [v₅, ← t1, ← t2]; simp [hq]
  have ex : Exec P W (.seq (sgnS 1 (.vtx 120061) (.vtx 120023) (.vtx 120061))
      (.seq (.instr (.copyN 120064 10010))
        (.seq (sgnS 1 (.vtx 120023) (.vtx 120062) (.vtx 120061))
          (.seq (.instr (.copyN 120065 10010))
            (ifEq 120064 120065 (.instr (.constN 120063 1)) (.instr (.constN 120063 0)))))))
      c c₅ (k₁ + (1 + (k₃ + (1 + k₅)))) := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  obtain ⟨k₆, ex₆, hk₆⟩ := ifEq_ne_exec (S := .instr (.constN 120063 1)) h2 ex
  obtain ⟨k₇, ex₇, hk₇⟩ := ifEq_ne_exec (S := .instr (.constN 120063 1)) h1 ex₆
  refine ⟨c₅, k₇, ex₇, by omega, u₅, ?_⟩
  rw [v₅, hsp]
  simp only [h1, h2, false_or, or_self]
  constructor
  · intro hq
    by_cases ha : ((Qof P).vtx e).2 < ((Qof P).vtx hz).2
    · have := s₁.2 ha
      left; refine ⟨ha, ?_⟩
      exact s₃.1 (by omega)
    · have h0 : c₁.nreg 10010 = 0 := by have := mt s₁.1 ha; omega
      right
      refine ⟨?_, lt_of_le_of_ne (not_lt.1 ha) ne1⟩
      have h0' : c₃.nreg 10010 = 0 := by omega
      have := mt s₃.2 (by omega)
      exact lt_of_le_of_ne (not_lt.1 this) (Ne.symm ne2)
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · have := s₁.2 ha; have := s₃.2 hb; omega
    · have h0 : ¬ ((Qof P).vtx e).2 < ((Qof P).vtx hz).2 := by linarith
      have h0' : ¬ ((Qof P).vtx hz).2 < ((Qof P).vtx e1).2 := by linarith
      have := mt s₁.1 h0; have := mt s₃.1 h0'; omega

/-- **The ahead test.** -/
theorem aheadS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {σb : ℕ} {zo : Option Point}
    (c : Config) (hw : WordsBounded W c) (he : c.nreg 120061 < P.n) (hhz : c.nreg 120023 < P.n)
    (hone : c.nreg 120011 = 1) (htwo : c.nreg 120048 = 2) (hσ : c.nreg 120024 = σb) (hσ1 : σb ≤ 1)
    (horg : OriginOK P c zo) :
    ∃ c' k, Exec P W aheadS c c' k ∧ k ≤ 250 ∧ c'.nreg 120066 ≤ 1 ∧
      (c'.nreg 120066 = 1 ↔ Ahead (sgnOf σb) zo (xe (Qof P) (c.nreg 120061) (c.nreg 120023))) := by
  rcases horg with ⟨hk2, rfl⟩ | ⟨hk2, p, hp, hpin, rfl⟩
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 120066 1 (by omega)
    exact ⟨c₁, _, .ifLtN_false (by omega) e₁, by omega, by rw [v₁], by rw [v₁]; simp [Ahead]⟩
  · have hle : (SymPt.onEdge (c.nreg 120061) (c.nreg 120023)).Lt P.n := ⟨he, hhz⟩
    have hlv : (SymPt.vtx (c.nreg 120061)).Lt P.n := he
    by_cases hs : σb < 1
    · have hσv : sgnOf σb = -1 := by unfold sgnOf; rw [ite_eq_right (by omega)]
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 0 (by norm_num)
        (.edge 120061 120023) (.regs 120025) (.vtx 120061) c hw (by decide) (by decide)
        (by decide) rfl hpin rfl hle hp hlv
      obtain ⟨c₂, e₂, v₂, -⟩ := copy_exec (P := P) e₁.wb_right 120066 10010
      refine ⟨c₂, _, .ifLtN_true (by omega) (.ifLtN_true (by omega) (.seq e₁ e₂)), by omega,
        by rwa [v₂], ?_⟩
      rw [v₂, s₁, hσv]
      simp only [SignTest, SymPt.eval, Ahead, xe]
      constructor
      · intro h; exact Or.inr ⟨by norm_num, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · norm_num at h
        · exact h
    · have hσv : sgnOf σb = 1 := by unfold sgnOf; rw [ite_eq_left (by omega)]
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 0 (by norm_num)
        (.regs 120025) (.edge 120061 120023) (.vtx 120061) c hw (by decide) (by decide)
        (by decide) hpin rfl rfl hp hle hlv
      obtain ⟨c₂, e₂, v₂, -⟩ := copy_exec (P := P) e₁.wb_right 120066 10010
      refine ⟨c₂, _, .ifLtN_true (by omega) (.ifLtN_false (by omega) (.seq e₁ e₂)), by omega,
        by rwa [v₂], ?_⟩
      rw [v₂, s₁, hσv]
      simp only [SignTest, SymPt.eval, Ahead, xe]
      constructor
      · intro h; exact Or.inl ⟨by norm_num, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · norm_num at h

/-- **Taking the tested edge.** -/
theorem takeS_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W takeS c c' k ∧ k ≤ 3 ∧ c'.nreg 120050 = 1 ∧
      c'.nreg 120051 = c.nreg 120061 ∧ c'.nreg 120052 = c.nreg 120060 := by
  unfold takeS
  exec_block
  · omega
  · refine ⟨by omega, by config_simp, by config_simp, by config_simp⟩

open Classical in
/-- **The comparison with the best hit, and the update.** -/
theorem betterS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {s hz σb : ℕ} (c : Config)
    (hw : WordsBounded W c) (he : c.nreg 120061 = eIdx P.n s (c.nreg 120060))
    (hn : 0 < P.n) (hhz : c.nreg 120023 = hz) (hhzn : hz < P.n) (hone : c.nreg 120011 = 1)
    (hσ : c.nreg 120024 = σb) (hσ1 : σb ≤ 1) {mb : ℕ} (hcim : c.nreg 120060 < mb)
    (hb : BestOK P.n s mb c) :
    ∃ c' k, Exec P W betterS c c' k ∧ k ≤ 260 ∧ BestOK P.n s mb c' ∧
      bestOf c' = if (∀ cb, bestOf c = some cb → BetterC (Qof P) s hz (sgnOf σb)
        (c.nreg 120060) cb) then some (c.nreg 120060) else bestOf c := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  set ci := c.nreg 120060
  have hen : c.nreg 120061 < P.n := by rw [he]; exact Nat.mod_lt _ hn
  -- taking the edge
  have take : ∀ d : Config, WordsBounded W d → d.nreg 120060 = ci →
      d.nreg 120061 = eIdx P.n s ci →
      ∃ d' k, Exec P W takeS d d' k ∧ k ≤ 3 ∧ BestOK P.n s mb d' ∧ bestOf d' = some ci := by
    intro d hd h60 h61
    obtain ⟨d', k, ex, hk, v50, v51, v52⟩ := takeS_exec (P := P) d hd (by omega)
    refine ⟨d', k, ex, hk, ⟨by omega, fun _ => ⟨by rw [v51, v52, h61, h60], by rwa [v52, h60]⟩⟩, ?_⟩
    unfold bestOf; rw [ite_eq_left v50, v52, h60]
  by_cases hf : c.nreg 120050 < 1
  · have hnone : bestOf c = none := by unfold bestOf; rw [ite_eq_right (by omega)]
    obtain ⟨c', k, ex, hk, hb', hv⟩ := take c hw rfl he
    refine ⟨c', _, .ifLtN_true (by omega) ex, by omega, hb', ?_⟩
    rw [hv, hnone, ite_eq_left (by simp)]
  · have hf1 : c.nreg 120050 = 1 := by have := hb.1; omega
    have hsome : bestOf c = some (c.nreg 120052) := by unfold bestOf; rw [ite_eq_left hf1]
    have heb := (hb.2 hf1).1
    have hebn : c.nreg 120051 < P.n := by rw [heb]; exact Nat.mod_lt _ hn
    have hl1 : (SymPt.onEdge (c.nreg 120051) (c.nreg 120023)).Lt P.n := ⟨hebn, by omega⟩
    have hl2 : (SymPt.onEdge (c.nreg 120061) (c.nreg 120023)).Lt P.n := ⟨hen, by omega⟩
    have hlv : (SymPt.vtx (c.nreg 120061)).Lt P.n := hen
    -- the comparison bit
    obtain ⟨c₂, k₂, e₂, hk₂, g₂, u₂, v₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120024 120011
        (.seq (sgnS 0 (.edge 120051 120023) (.edge 120061 120023) (.vtx 120061))
          (.instr (.copyN 120067 10010)))
        (.seq (sgnS 0 (.edge 120061 120023) (.edge 120051 120023) (.vtx 120061))
          (.instr (.copyN 120067 10010)))) c c₂ k₂ ∧ k₂ ≤ 250 ∧
        (∀ r, Bk r = false → r ≠ 120067 → c₂.nreg r = c.nreg r) ∧ c₂.nreg 120067 ≤ 1 ∧
        (c₂.nreg 120067 = 1 ↔ BetterC (Qof P) s hz (sgnOf σb) ci (c.nreg 120052)) := by
      have ee : ∀ x, eIdx (Qof P).n s x = eIdx P.n s x := fun x => by rw [hQn]
      by_cases hs : σb < 1
      · have hσv : sgnOf σb = -1 := by unfold sgnOf; rw [ite_eq_right (by omega)]
        obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 0 (by norm_num)
          (.edge 120051 120023) (.edge 120061 120023) (.vtx 120061) c hw (by decide) (by decide)
          (by decide) rfl rfl rfl hl1 hl2 hlv
        obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec (P := P) e₁.wb_right 120067 10010
        refine ⟨c₂, _, .ifLtN_true (by omega) (.seq e₁ e₂), by omega,
          fun r hr hr' => (r₂ r hr').trans (f₁.1 r hr), by rwa [v₂], ?_⟩
        rw [v₂, s₁, hσv]
        simp only [SignTest, SymPt.eval, BetterC, xe, ee, ← he, ← heb, hhz]
        constructor
        · intro h; exact Or.inr ⟨by norm_num, h⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · norm_num at h
          · exact h
      · have hσv : sgnOf σb = 1 := by unfold sgnOf; rw [ite_eq_left (by omega)]
        obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 0 (by norm_num)
          (.edge 120061 120023) (.edge 120051 120023) (.vtx 120061) c hw (by decide) (by decide)
          (by decide) rfl rfl rfl hl2 hl1 hlv
        obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec (P := P) e₁.wb_right 120067 10010
        refine ⟨c₂, _, .ifLtN_false (by omega) (.seq e₁ e₂), by omega,
          fun r hr hr' => (r₂ r hr').trans (f₁.1 r hr), by rwa [v₂], ?_⟩
        rw [v₂, s₁, hσv]
        simp only [SignTest, SymPt.eval, BetterC, xe, ee, ← he, ← heb, hhz]
        constructor
        · intro h; exact Or.inl ⟨by norm_num, h⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact h
          · norm_num at h
    have c60 : c₂.nreg 120060 = ci := g₂ _ (by decide) (by decide)
    have c61 : c₂.nreg 120061 = eIdx P.n s ci := (g₂ _ (by decide) (by decide)).trans he
    have c11 : c₂.nreg 120011 = 1 := (g₂ _ (by decide) (by decide)).trans hone
    have hb₂ : BestOK P.n s mb c₂ := by
      refine ⟨by rw [g₂ _ (by decide) (by decide)]; exact hb.1, fun h => ?_⟩
      rw [g₂ _ (by decide) (by decide)] at h ⊢
      rw [g₂ _ (by decide) (by decide)]
      exact hb.2 h
    have hbo₂ : bestOf c₂ = bestOf c := by
      unfold bestOf
      rw [g₂ 120050 (by decide) (by decide), g₂ 120052 (by decide) (by decide)]
    have hall : (∀ cb, bestOf c = some cb → BetterC (Qof P) s hz (sgnOf σb) ci cb) ↔
        BetterC (Qof P) s hz (sgnOf σb) ci (c.nreg 120052) := by
      rw [hsome]
      constructor
      · intro h; exact h _ rfl
      · intro h cb hcb; cases hcb; exact h
    by_cases hbt : c₂.nreg 120067 < 1
    · refine ⟨c₂, _, .ifLtN_false (by omega) (.seq e₂ (.ifLtN_true (by rwa [c11])
        (.skip e₂.wb_right))), by omega, hb₂, ?_⟩
      rw [hbo₂, ite_eq_right (fun h => by have := v₂.2 (hall.1 h); omega)]
    · obtain ⟨c₃, k₃, e₃, hk₃, hb₃, hv₃⟩ := take c₂ e₂.wb_right c60 c61
      refine ⟨c₃, _, .ifLtN_false (by omega) (.seq e₂ (.ifLtN_false (by rwa [c11])
        e₃)), by omega, hb₃, ?_⟩
      rw [hv₃, ite_eq_left (hall.2 (v₂.1 (by omega)))]

theorem add_exec {c : Config} (hw : WordsBounded W c) (r a b : ℕ) (h : c.nreg a + c.nreg b ≤ W) :
    ∃ c', Exec P W (.instr (.addN r a b)) c c' 1 ∧ c'.nreg r = c.nreg a + c.nreg b ∧
      (∀ r', r' ≠ r → c'.nreg r' = c.nreg r') ∧ c'.nmem = c.nmem :=
  ⟨_, Exec.addN hw r a b h, by config_simp, fun r' h' => by
    config_simp; rw [Machine.upd_other _ _ _ h'], rfl⟩

/-- The origin registers survive a statement that does not write them. -/
theorem originOK_congr {c c' : Config} {zo : Option Point}
    (h : ∀ r, 120025 ≤ r → r ≤ 120027 → c'.nreg r = c.nreg r) (ho : OriginOK P c zo) :
    OriginOK P c' zo := by
  rcases ho with ⟨h1, h2⟩ | ⟨h1, p, hp, hin, h2⟩
  · exact Or.inl ⟨by rwa [h _ le_rfl (by norm_num)], h2⟩
  · refine Or.inr ⟨by rwa [h _ le_rfl (by norm_num)], p, hp, ?_, h2⟩
    cases p with
    | vtx i =>
      simp only [SymPtIn] at hin ⊢
      rwa [h _ le_rfl (by norm_num), h 120026 (by norm_num) (by norm_num)]
    | onEdge e h' =>
      simp only [SymPtIn] at hin ⊢
      rwa [h _ le_rfl (by norm_num), h 120026 (by norm_num) (by norm_num),
        h 120027 (by norm_num) le_rfl]

/-- **The edge test** of chain edge `ci` (register `120060`). -/
theorem edgeT_exec (hG : GoodEnv P) (hW : 2 * P.n + 3 ≤ W) (hD : DistinctHeights (Qof P))
    {s hz σb : ℕ} {zo : Option Point} (c : Config) (hw : WordsBounded W c)
    (hc : EConst P s hz σb zo c) (hci : c.nreg 120060 < P.n) {mb : ℕ} (hcim : c.nreg 120060 < mb)
    (hb : BestOK P.n s mb c) :
    ∃ c' k, Exec P W edgeT c c' k ∧ k ≤ 1100 ∧ BestOK P.n s mb c' ∧
      bestOf c' = upd1 (Qof P) s hz (sgnOf σb) zo (bestOf c) (c.nreg 120060) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : 0 < P.n := by have := hc.s_lt; omega
  have hsn := hc.s_lt
  -- e := (s + ci) mod n
  obtain ⟨c₁, e₁, v₁, r₁, -⟩ := add_exec (P := P) hw 120061 120015 120060
    (by rw [hc.rs]; omega)
  rw [hc.rs] at v₁
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120061) (nr := 120010)
    (by decide) c₁ e₁.wb_right (by rw [v₁, r₁ _ (by decide), hc.n]; omega)
  rw [v₁, r₁ _ (by decide), hc.n] at v₂
  obtain ⟨c₃, e₃, v₃, r₃, -⟩ := add_exec (P := P) e₂.wb_right 120062 120061 120011 (by
    rw [v₂, r₂ _ (by decide), r₁ _ (by decide), hc.one]
    have := Nat.mod_lt (s + c.nreg 120060) hn; omega)
  rw [v₂, r₂ _ (by decide), r₁ _ (by decide), hc.one] at v₃
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, -⟩ := modSub_exec (P := P) (r := 120062) (nr := 120010)
    (by decide) c₃ e₃.wb_right (by
      rw [v₃, r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide), hc.n]
      have := Nat.mod_lt (s + c.nreg 120060) hn; omega)
  rw [v₃, r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide), hc.n] at v₄
  set ci := c.nreg 120060
  have R₄ : ∀ r, r ≠ 120061 → r ≠ 120062 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [r₄ r h2, r₃ r h2, r₂ r h1, r₁ r h1]
  have x61 : c₄.nreg 120061 = eIdx P.n s ci := by rwa [r₄ _ (by decide), r₃ _ (by decide)]
  have x62 : c₄.nreg 120062 = (c₄.nreg 120061 + 1) % P.n := by rw [v₄, x61]; rfl
  have hen : eIdx P.n s ci < P.n := Nat.mod_lt _ hn
  have x23 : c₄.nreg 120023 = hz := (R₄ _ (by decide) (by decide)).trans hc.rhz
  -- the height range
  obtain ⟨c₅, k₅, e₅, hk₅, u₅, v₅⟩ := spansS_exec (P := P) hG (by omega) hD c₄ e₄.wb_right
    (by rwa [x61]) x62 (by rw [x23]; exact hc.hz_lt)
  have f₅ := exec_frameB e₅ (B := fun r => Bk r || decide (120063 ≤ r ∧ r ≤ 120065)) (by decide)
  have R₅ : ∀ r, Bk r = false → (r < 120063 ∨ 120065 < r) → c₅.nreg r = c₄.nreg r :=
    fun r h1 h2 => f₅.1 r (by simp only [h1, Bool.false_or, decide_eq_false_iff_not]; omega)
  rw [x61, x23] at v₅
  have hQe : eIdx (Qof P).n s ci = eIdx P.n s ci := by rw [hQn]
  have hbo₅ : bestOf c₅ = bestOf c := by
    unfold bestOf
    rw [R₅ 120050 (by decide) (by omega), R₅ 120052 (by decide) (by omega),
      R₄ 120050 (by decide) (by decide), R₄ 120052 (by decide) (by decide)]
  have hb₅ : BestOK P.n s mb c₅ := by
    unfold BestOK
    rwa [R₅ 120050 (by decide) (by omega), R₅ 120052 (by decide) (by omega),
      R₅ 120051 (by decide) (by omega), R₄ 120050 (by decide) (by decide),
      R₄ 120052 (by decide) (by decide), R₄ 120051 (by decide) (by decide)]
  have G₅ : ∀ r, Bk r = false → (r < 120061 ∨ 120065 < r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => (R₅ r h1 (by omega)).trans (R₄ r (by omega) (by omega))
  have c11 : c₅.nreg 120011 = 1 := (G₅ _ (by decide) (by omega)).trans hc.one
  by_cases hsp : c₅.nreg 120063 < 1
  · -- not in range: nothing changes
    have hnsp : ¬ Spans (Qof P) (eIdx P.n s ci) hz := fun h => by have := v₅.2 h; omega
    refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_true
      (by rwa [c11]) (.skip e₅.wb_right)))))), by omega, hb₅, ?_⟩
    unfold upd1 HitC
    rw [hQe, ite_eq_right (fun h => hnsp h.1.1), hbo₅]
  have hsp1 : Spans (Qof P) (eIdx P.n s ci) hz := v₅.1 (by omega)
  -- ahead
  have x61' : c₅.nreg 120061 = eIdx P.n s ci := (R₅ _ (by decide) (by omega)).trans x61
  have x23' : c₅.nreg 120023 = hz := (R₅ _ (by decide) (by omega)).trans x23
  obtain ⟨c₆, k₆, e₆, hk₆, u₆, v₆⟩ := aheadS_exec (P := P) hG (by omega) (σb := σb) (zo := zo)
    c₅ e₅.wb_right (by rwa [x61']) (by rw [x23']; exact hc.hz_lt) c11
    ((G₅ _ (by decide) (by omega)).trans hc.two) ((G₅ _ (by decide) (by omega)).trans hc.rσ)
    hc.σle (originOK_congr (fun r h1 h2 => G₅ r (by
      simp only [Bk, decide_eq_false_iff_not, not_and, not_lt]; omega) (by omega)) hc.org)
  rw [x61', x23'] at v₆
  have f₆ := exec_frameB e₆ (B := fun r => Bk r || decide (r = 120066)) (by decide)
  have R₆ : ∀ r, Bk r = false → r ≠ 120066 → c₆.nreg r = c₅.nreg r :=
    fun r h1 h2 => f₆.1 r (by simp only [h1, Bool.false_or, decide_eq_false_iff_not]; exact h2)
  have c11' : c₆.nreg 120011 = 1 := (R₆ _ (by decide) (by decide)).trans c11
  by_cases hah : c₆.nreg 120066 < 1
  · have hna : ¬ Ahead (sgnOf σb) zo (xe (Qof P) (eIdx P.n s ci) hz) := fun h => by
      have := v₆.2 h; omega
    refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false
      (by rwa [c11]) (.seq e₆ (.ifLtN_true (by rwa [c11'])
        (.skip e₆.wb_right)))))))),
      by omega, ?_, ?_⟩
    · unfold BestOK
      rwa [R₆ 120050 (by decide) (by decide), R₆ 120052 (by decide) (by decide),
        R₆ 120051 (by decide) (by decide)]
    · unfold upd1 HitC
      rw [hQe, ite_eq_right (fun h => hna h.1.2)]
      unfold bestOf
      rwa [R₆ 120050 (by decide) (by decide), R₆ 120052 (by decide) (by decide)]
  have hah1 : Ahead (sgnOf σb) zo (xe (Qof P) (eIdx P.n s ci) hz) := v₆.1 (by omega)
  -- the comparison and the update
  have G₆ : ∀ r, Bk r = false → (r < 120061 ∨ 120066 < r) → c₆.nreg r = c.nreg r :=
    fun r h1 h2 => (R₆ r h1 (by omega)).trans (G₅ r h1 (by omega))
  obtain ⟨c₇, k₇, e₇, hk₇, hb₇, v₇⟩ := betterS_exec (P := P) hG (by omega) (s := s) (hz := hz)
    (σb := σb) c₆ e₆.wb_right (by
      rw [R₆ _ (by decide) (by decide), x61', G₆ _ (by decide) (by omega)]) hn
    ((R₆ _ (by decide) (by decide)).trans x23') hc.hz_lt c11'
    ((G₆ _ (by decide) (by omega)).trans hc.rσ) hc.σle (mb := mb)
      (by rwa [G₆ _ (by decide) (by omega)]) (by
      unfold BestOK
      rwa [R₆ 120050 (by decide) (by decide), R₆ 120052 (by decide) (by decide),
        R₆ 120051 (by decide) (by decide)])
  have c60 : c₆.nreg 120060 = ci := G₆ _ (by decide) (by omega)
  have hbo₆ : bestOf c₆ = bestOf c := by
    unfold bestOf
    rwa [R₆ 120050 (by decide) (by decide), R₆ 120052 (by decide) (by decide)]
  rw [c60, hbo₆] at v₇
  refine ⟨c₇, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false
    (by rwa [c11]) (.seq e₆ (.ifLtN_false (by rwa [c11']) e₇))))))),
    by omega, hb₇, ?_⟩
  rw [v₇]
  unfold upd1 HitC
  rw [hQe]
  by_cases hall : ∀ cb, bestOf c = some cb → BetterC (Qof P) s hz (sgnOf σb) ci cb
  · rw [ite_eq_left hall, ite_eq_left ⟨⟨hsp1, hah1⟩, hall⟩]
  · rw [ite_eq_right hall, ite_eq_right (fun h => hall h.2)]

end Exec

end

end OracleR

end Chazelle.Core
