module

public import Chazelle.Golf

public import Chazelle.Core.SignKernelMath
public import Chazelle.Programs.Tactics

/-!
# The sign kernel, part 2: RAM building blocks (WP-A)

* `wr B s`: every instruction of `s` is a straight-line register write into a register
  accepted by `B` (no stores, no `emit`); `exec_frameB`: such a statement leaves every other
  register, both memories and the output unchanged.
* `lexStmt`: the lexicographic sign of a list of real registers (`lexStmt_spec`).
* `succIdx`: `(e + 1) % n` (`succIdx_spec`); `normR`: the sign normalisation of an edge
  point's denominator (`normR_spec`); `loadPt`: the representation `symRep P s` of a symbolic
  point read from its registers (`loadPt_spec`).

Register map (band `bSign = 1`): inputs `10000 … 10009`, output `10010`; constants
`nreg 10020 = n`, `nreg 10021 = 1`, `nreg 10022 = 2`, `nreg 10023 = 3`, `rreg 10020 = 0`;
load scratch `10040 … 10050`; point representations at `10100`, `10110`, `10120` (six reals:
`x0 x1 d0 d1 y0 y1`); coefficient lists `10200 … 10220`, scratch `10300, 10301`; the selected
list `10400 … 10404`; sign bits `10410` (positive), `10411` (zero).
-/

namespace Chazelle.Core

namespace SignK

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## A generic frame for register-writing statements -/

/-- The instruction writes only a register accepted by `B` (natural or real), and is not a
store, an `emit` or a control instruction. -/
def wrOK (B : ℕ → Bool) : Instr → Bool
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => B r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => B r
  | .loadR r _ | .readX r _ | .readY r _ => B r
  | _ => false

/-- Every instruction of the statement satisfies `wrOK B`. -/
def wr (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOK B i
  | .seq s t => wr B s && wr B t
  | .ifLtN _ _ t e => wr B t && wr B e
  | .ifLtR _ _ t e => wr B t && wr B e
  | .whileLtN _ _ b => wr B b
  | .whileLtR _ _ b => wr B b

/-- Registers outside `B`, both memories and the output agree. -/
def FrameB (B : ℕ → Bool) (c c' : Config) : Prop :=
  (∀ r, B r = false → c'.nreg r = c.nreg r) ∧ (∀ r, B r = false → c'.rreg r = c.rreg r) ∧
    c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

theorem FrameB.refl (B : ℕ → Bool) (c : Config) : FrameB B c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem FrameB.trans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameB B c₁ c₂)
    (h₂ : FrameB B c₂ c₃) : FrameB B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), fun r hr => (h₂.2.1 r hr).trans (h₁.2.1 r hr),
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-- **Frame of a register-writing statement**: an execution of a statement all of whose
instructions write registers accepted by `B` changes no other register, no memory cell and
not the output. -/
theorem exec_frameB {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wr B s = true) : FrameB B c c' := by
  induction h with
  | skip _ => exact FrameB.refl B _
  | @instr ins c c' _ he _ _ =>
    simp only [wr] at hs
    cases ins <;> simp only [wrOK, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine ⟨fun j hj => ?_, fun j hj => ?_, rfl, rfl, rfl⟩ <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wr, Bool.and_eq_true] at hs
    exact (ih₁ hs.1).trans (ih₂ hs.2)
  | ifLtN_true _ _ ih =>
    simp only [wr, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [wr, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [wr, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [wr, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact FrameB.refl B _
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)
  | whileLtR_false _ _ => exact FrameB.refl B _
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)


/-! ## The lexicographic sign of a list of real registers -/

/-- The lexicographic sign of the real registers `rs` (`Z` holds `0`): `nreg Pb := 1` iff the
lowest nonzero entry is positive, `nreg Zb := 1` iff all entries vanish. -/
def lexStmt (Z Pb Zb : ℕ) : List ℕ → Stmt
  | [] => block [.constN Pb 0, .constN Zb 1]
  | r :: rs => .ifLtR Z r (block [.constN Pb 1, .constN Zb 0])
      (.ifLtR r Z (block [.constN Pb 0, .constN Zb 0]) (lexStmt Z Pb Zb rs))

/-- **Spec of `lexStmt`**: cost `≤ 4 · |rs| + 2`; the two bits are `≤ 1` and decide
`lexPos` and `allZero` of the register values. -/
theorem lexStmt_spec {P : Polygon} {W : ℕ} (Z Pb Zb : ℕ) (hne : Pb ≠ Zb) (hW : 1 ≤ W) :
    ∀ (rs : List ℕ) (c : Config), WordsBounded W c → c.rreg Z = 0 →
    ∃ c' k, Exec P W (lexStmt Z Pb Zb rs) c c' k ∧ k ≤ 4 * rs.length + 2 ∧
      c'.nreg Pb ≤ 1 ∧ c'.nreg Zb ≤ 1 ∧ (c'.nreg Pb = 1 ↔ lexPos (rs.map c.rreg)) ∧
      (c'.nreg Zb = 1 ↔ allZero (rs.map c.rreg)) := by
  intro rs
  induction rs with
  | nil =>
    intro c hc hZ
    ϴ lexStmt
    exec_block
    · omega
    · omega
    · Θ hne, lexPos, allZero
  | cons r rs ih =>
    intro c hc hZ
    ϴ lexStmt
    by_cases h1 : c.rreg Z < c.rreg r
    · refine spec_ifLtR_true h1 ?_
      have hp : 0 < c.rreg r := hZ ▸ h1
      exec_block
      · omega
      · omega
      · refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        Θ hne, lexPos, allZero, hp, hp.ne'
    · by_cases h2 : c.rreg r < c.rreg Z
      · refine spec_ifLtR_false h1 (spec_ifLtR_true h2 ?_)
        have hn : c.rreg r < 0 := hZ ▸ h2
        exec_block
        · omega
        · omega
        · refine ⟨by simp only [List.length_cons]; omega, ?_⟩
          Θ hne, lexPos, allZero, hn.ne, not_lt.2 hn.le
      · refine spec_ifLtR_false h1 (spec_ifLtR_false h2 ?_)
        have h0 : c.rreg r = 0 := by
          rw [hZ] at h1 h2
          exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)
        obtain ⟨c', k, ex, hk, a, b, e1, e2⟩ := ih c hc hZ
        refine ⟨c', k, ex, by simp only [List.length_cons]; omega, a, b, ?_, ?_⟩
        · Θ lexPos, h0, e1
        · Θ allZero, h0, e2

/-! ## Loading a symbolic point -/

/-- `nreg 10040 := (nreg a + 1) % n` (with `nreg 10020 = n`, `nreg 10021 = 1`). -/
def succIdx (a : ℕ) : Stmt :=
  .seq (block [.addN 10040 a 10021]) (.ifLtN 10040 10020 .skip (block [.constN 10040 0]))

/-- **Spec of `succIdx`**: cost `≤ 4`, the successor index modulo `n`, only natural register
`10040` written. -/
theorem succIdx_spec {P : Polygon} {W : ℕ} (a : ℕ) (c : Config) (hc : WordsBounded W c)
    (ha : c.nreg a < P.n) (h1 : c.nreg 10021 = 1) (hn : c.nreg 10020 = P.n) (hW : P.n ≤ W) :
    ∃ c' k, Exec P W (succIdx a) c c' k ∧ k ≤ 4 ∧ c'.nreg 10040 = (c.nreg a + 1) % P.n ∧
      c'.rreg = c.rreg ∧ (∀ r, r ≠ 10040 → c'.nreg r = c.nreg r) := by
  unfold succIdx
  refine spec_seq ?_
  exec_block
  · rw [h1]; omega
  · by_cases hlt : c.nreg a + 1 < P.n
    · refine spec_ifLtN_true (by config_simp; rw [h1, hn]; exact hlt) ?_
      refine spec_skip ‹_› ?_
      refine ⟨⋄, by config_simp; rw [h1, Nat.mod_eq_of_lt hlt], rfl,
        fun r hr => by config_simp; simp [hr]⟩
    · refine spec_ifLtN_false (by config_simp; rw [h1, hn]; exact hlt) ?_
      have he : c.nreg a + 1 = P.n := ⋄
      exec_block
      · omega
      · exact ⟨⋄, by config_simp; rw [he, Nat.mod_self], rfl,
          fun r hr => by config_simp; simp [hr]⟩

/-- A representation held in the six real registers from `ob` on. -/
def RepAt (c : Config) (ob : ℕ) (r : Rep) : Prop :=
  c.rreg ob = r.x0 ∧ c.rreg (ob + 1) = r.x1 ∧ c.rreg (ob + 2) = r.d0 ∧ c.rreg (ob + 3) = r.d1 ∧
    c.rreg (ob + 4) = r.y0 ∧ c.rreg (ob + 5) = r.y1

/-- The sign normalisation of an edge representation (`edgeRep` in terms of its inputs). -/
noncomputable def normRep (u1 dx dy x0 x1 y0 y1 : ℝ) : Rep :=
  if dy < 0 then Rep.neg ⟨x0, x1, dy, dx, y0, y1⟩
  else if 0 < dy then ⟨x0, x1, dy, dx, y0, y1⟩
  else if dx < 0 then Rep.neg ⟨x0, x1, dy, dx, y0, y1⟩
  else if 0 < dx then ⟨x0, x1, dy, dx, y0, y1⟩
  else ⟨u1, 0, 1, 0, y0, y1⟩

theorem edgeRep_eq (u w v : Point) :
    edgeRep u w v = normRep u.1 (w.1 - u.1) (w.2 - u.2)
      (u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1))
      (u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1)) v.2 v.1 := rfl

/-- Negate the numerator and the denominator at `ob`. -/
def negR (ob : ℕ) : Stmt :=
  block [.subR ob 10020 ob, .subR (ob + 1) 10020 (ob + 1), .subR (ob + 2) 10020 (ob + 2),
    .subR (ob + 3) 10020 (ob + 3)]

/-- The degenerate edge: abscissa `u.1`, denominator `1`. -/
def degR (ob : ℕ) : Stmt :=
  block [.copyR ob 10041, .constR (ob + 1) 0, .constR (ob + 2) 1, .constR (ob + 3) 0]

/-- The sign normalisation (`dy` in `rreg 10046`, `dx` in `rreg 10045`, `u.1` in `10041`). -/
def normR (ob : ℕ) : Stmt :=
  .ifLtR 10046 10020 (negR ob) (.ifLtR 10020 10046 .skip
    (.ifLtR 10045 10020 (negR ob) (.ifLtR 10020 10045 .skip (degR ob))))

/-- **Spec of `normR`**: cost `≤ 12`, the normalised representation. -/
theorem normR_spec {P : Polygon} {W : ℕ} (ob : ℕ) (hob : ob = 10100 ∨ ob = 10110 ∨ ob = 10120)
    {u1 dx dy x0 x1 y0 y1 : ℝ} (c : Config) (hc : WordsBounded W c) (hZ : c.rreg 10020 = 0)
    (hdx : c.rreg 10045 = dx) (hdy : c.rreg 10046 = dy) (hu : c.rreg 10041 = u1)
    (hr : RepAt c ob ⟨x0, x1, dy, dx, y0, y1⟩) :
    ∃ c' k, Exec P W (normR ob) c c' k ∧ k ≤ 12 ∧
      RepAt c' ob (normRep u1 dx dy x0 x1 y0 y1) := by
  rcases hob with rfl | rfl | rfl <;>
  · obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
    simp only [Nat.reduceAdd] at r0 r1 r2 r3 r4 r5
    ϴ normR, negR, degR, Nat.reduceAdd
    by_cases h1 : dy < 0
    · refine spec_ifLtR_true (by rw [hdy, hZ]; exact h1) ?_
      exec_block
      refine ⟨⋄, ?_⟩
      ϴ normRep, h1, ↓reduceIte, RepAt, Rep.neg, Nat.reduceAdd
      config_simp
      ϴ hZ, r0, r1, r2, r3, r4, r5, and_self
    by_cases h2 : 0 < dy
    · refine spec_ifLtR_false (by rw [hdy, hZ]; exact h1) ?_
      refine spec_ifLtR_true (by rw [hdy, hZ]; exact h2) ?_
      refine spec_skip hc ⟨⋄, ?_⟩
      ϴ normRep, h1, h2, ↓reduceIte, RepAt, Nat.reduceAdd
      exact ⟨r0, r1, r2, r3, r4, r5⟩
    have h0 : dy = 0 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    by_cases h3 : dx < 0
    · refine spec_ifLtR_false (by rw [hdy, hZ]; exact h1) ?_
      refine spec_ifLtR_false (by rw [hdy, hZ]; exact h2) ?_
      refine spec_ifLtR_true (by rw [hdx, hZ]; exact h3) ?_
      exec_block
      refine ⟨⋄, ?_⟩
      ϴ normRep, h1, h2, h3, ↓reduceIte, RepAt, Rep.neg, Nat.reduceAdd
      config_simp
      ϴ hZ, r0, r1, r2, r3, r4, r5, and_self
    by_cases h4 : 0 < dx
    · refine spec_ifLtR_false (by rw [hdy, hZ]; exact h1) ?_
      refine spec_ifLtR_false (by rw [hdy, hZ]; exact h2) ?_
      refine spec_ifLtR_false (by rw [hdx, hZ]; exact h3) ?_
      refine spec_ifLtR_true (by rw [hdx, hZ]; exact h4) ?_
      refine spec_skip hc ⟨⋄, ?_⟩
      ϴ normRep, h1, h2, h3, h4, ↓reduceIte, RepAt, Nat.reduceAdd
      exact ⟨r0, r1, r2, r3, r4, r5⟩
    · refine spec_ifLtR_false (by rw [hdy, hZ]; exact h1) ?_
      refine spec_ifLtR_false (by rw [hdy, hZ]; exact h2) ?_
      refine spec_ifLtR_false (by rw [hdx, hZ]; exact h3) ?_
      refine spec_ifLtR_false (by rw [hdx, hZ]; exact h4) ?_
      exec_block
      refine ⟨⋄, ?_⟩
      ϴ normRep, h1, h2, h3, h4, ↓reduceIte, RepAt, Nat.reduceAdd
      config_simp
      ϴ hu, r4, r5, Int.cast_zero, Int.cast_one, and_self


/-- Load a vertex: `x0 = x`, `x1 = 0`, `d = 1`, `y0 = y`, `y1 = x`. -/
def loadVtx (nb ob : ℕ) : Stmt :=
  block [.readX ob (nb + 1), .constR (ob + 1) 0, .constR (ob + 2) 1, .constR (ob + 3) 0,
    .readY (ob + 4) (nb + 1), .readX (ob + 5) (nb + 1)]

/-- Load an edge point (`u` = start of the edge, `w` = its end, index in `nreg 10040`, `v` =
the height vertex): the unnormalised representation `x0 = u.1 dy + (v.2 - u.2) dx`,
`x1 = u.1 dx + (v.1 - u.1) dx`, `d = (dy, dx)`, `y = (v.2, v.1)`. -/
def loadEdge (nb ob : ℕ) : Stmt :=
  block [.readX 10041 (nb + 1), .readY 10042 (nb + 1), .readX 10043 10040, .readY 10044 10040,
    .readX (ob + 5) (nb + 2), .readY (ob + 4) (nb + 2), .subR 10045 10043 10041,
    .subR 10046 10044 10042, .subR 10047 (ob + 4) 10042, .subR 10048 (ob + 5) 10041,
    .mulR 10049 10041 10046, .mulR 10050 10047 10045, .addR ob 10049 10050,
    .mulR 10049 10041 10045, .mulR 10050 10048 10045, .addR (ob + 1) 10049 10050,
    .copyR (ob + 2) 10046, .copyR (ob + 3) 10045]

/-- Load the symbolic point held in `nreg nb … nb + 2` as a representation at `rreg ob … ob + 5`. -/
def loadPt (nb ob : ℕ) : Stmt :=
  .ifLtN nb 10021 (loadVtx nb ob) (.seq (succIdx (nb + 1)) (.seq (loadEdge nb ob) (normR ob)))

/-- **Spec of `loadPt`** (for the three slots used by the kernel): cost `≤ 40`, the registers
from `ob` on hold `symRep P s`. -/
theorem loadPt_spec {P : Polygon} {W : ℕ} (nb ob : ℕ)
    (hj : (nb = 10000 ∧ ob = 10100) ∨ (nb = 10003 ∧ ob = 10110) ∨ (nb = 10006 ∧ ob = 10120))
    (c : Config) (hc : WordsBounded W c) (hn : c.nreg 10020 = P.n) (h1 : c.nreg 10021 = 1)
    (hZ : c.rreg 10020 = 0) (hW : P.n ≤ W) (s : SymPt) (hs : s.Lt P.n) (hin : SymPtIn c nb s) :
    ∃ c' k, Exec P W (loadPt nb ob) c c' k ∧ k ≤ 40 ∧ RepAt c' ob (symRep P s) := by
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · cases s with
    | vtx i =>
      obtain ⟨hk, hi⟩ := hin
      simp only [Nat.reduceAdd] at hi
      ϴ loadPt, loadVtx, Nat.reduceAdd
      refine spec_ifLtN_true (by rw [hk, h1]; norm_num) ?_
      exec_block
      refine ⟨⋄, ?_⟩
      ϴ RepAt, symRep, Nat.reduceAdd
      config_simp
      ϴ hi, Int.cast_zero, Int.cast_one, and_self
    | onEdge e h =>
      obtain ⟨hk, he, hh⟩ := hin
      simp only [Nat.reduceAdd] at he hh
      ϴ loadPt, loadEdge, Nat.reduceAdd
      refine spec_ifLtN_false (by rw [hk, h1]; norm_num) ?_
      refine spec_seq ?_
      refine spec_use (succIdx_spec _ c hc (by rw [he]; exact hs.1) h1 hn hW) ?_
      rintro c1 k1 hk1 hw1 ⟨hidx, hrr, hnr⟩
      have e1 : c1.nreg _ = e := (hnr _ (⊛)).trans he
      have e2 : c1.nreg _ = h := (hnr _ (⊛)).trans hh
      rw [he] at hidx
      refine spec_seq ?_
      exec_block
      refine spec_use (normR_spec _ (⊛) _ ‹_›
        (u1 := (P.vtx e).1) (dx := (P.vtx ((e + 1) % P.n)).1 - (P.vtx e).1)
        (dy := (P.vtx ((e + 1) % P.n)).2 - (P.vtx e).2)
        (x0 := (P.vtx e).1 * ((P.vtx ((e + 1) % P.n)).2 - (P.vtx e).2) +
          ((P.vtx h).2 - (P.vtx e).2) * ((P.vtx ((e + 1) % P.n)).1 - (P.vtx e).1))
        (x1 := (P.vtx e).1 * ((P.vtx ((e + 1) % P.n)).1 - (P.vtx e).1) +
          ((P.vtx h).1 - (P.vtx e).1) * ((P.vtx ((e + 1) % P.n)).1 - (P.vtx e).1))
        (y0 := (P.vtx h).2) (y1 := (P.vtx h).1)
        (by config_simp; rw [hrr, hZ]) (by config_simp; rw [hidx, e1])
        (by config_simp; rw [hidx, e1]) (by config_simp; rw [e1])
        (by simp only [RepAt, Nat.reduceAdd]; config_simp; simp only [hidx, e1, e2, and_self]))
        ?_
      intro c' k2 hk2 _ hrep
      refine ⟨⋄, ?_⟩
      Ξ symRep, edgeRep_eq
      exact hrep


/-! ## The prelude, the coefficient lists, the selection and the final bit -/

/-- Constants: `nreg 10020 := n`, `nreg 10021 := 1`, `nreg 10022 := 2`, `nreg 10023 := 3`,
`rreg 10020 := 0`. -/
def prelude : Stmt :=
  block [.inputSize 10020, .constN 10021 1, .constN 10022 2, .constN 10023 3, .constR 10020 0]

/-- **Spec of `prelude`**: cost `5`. -/
theorem prelude_spec {P : Polygon} {W : ℕ} (c : Config) (hc : WordsBounded W c) (hW : P.n + 3 ≤ W) :
    ∃ c' k, Exec P W prelude c c' k ∧ k ≤ 5 ∧ c'.nreg 10020 = P.n ∧ c'.nreg 10021 = 1 ∧
      c'.nreg 10022 = 2 ∧ c'.nreg 10023 = 3 ∧ c'.rreg 10020 = 0 := by
  unfold prelude
  exec_block
  · omega
  · omega
  · omega
  · omega
  · refine ⟨⋄, ?_⟩
    config_simp
    simp

/-- The coefficient lists of all tests, from the representations at `10100`, `10110`, `10120`:
`A = x_b d_a - x_a d_b` at `10200`, `C = x_c d_a - x_a d_c` at `10203`, `y_b - y_a` at `10206`,
`y_c - y_a` at `10208`, `B = d_c (y_c - y_a)` at `10210`, `E = d_b (y_b - y_a)` at `10213`,
`A B - C E` at `10216 … 10220`; scratch `10300, 10301`.  Exactly `71` instructions. -/
def polyStmt : Stmt :=
  block [.mulR 10300 10110 10102, .mulR 10301 10100 10112, .subR 10200 10300 10301,
    .mulR 10300 10110 10103, .mulR 10301 10111 10102, .addR 10300 10300 10301,
    .mulR 10301 10100 10113, .subR 10300 10300 10301, .mulR 10301 10101 10112,
    .subR 10201 10300 10301, .mulR 10300 10111 10103, .mulR 10301 10101 10113,
    .subR 10202 10300 10301, .mulR 10300 10120 10102, .mulR 10301 10100 10122,
    .subR 10203 10300 10301, .mulR 10300 10120 10103, .mulR 10301 10121 10102,
    .addR 10300 10300 10301, .mulR 10301 10100 10123, .subR 10300 10300 10301,
    .mulR 10301 10101 10122, .subR 10204 10300 10301, .mulR 10300 10121 10103,
    .mulR 10301 10101 10123, .subR 10205 10300 10301, .subR 10206 10114 10104,
    .subR 10207 10115 10105, .subR 10208 10124 10104, .subR 10209 10125 10105,
    .mulR 10210 10122 10208, .mulR 10300 10122 10209, .mulR 10301 10123 10208,
    .addR 10211 10300 10301, .mulR 10212 10123 10209, .mulR 10213 10112 10206,
    .mulR 10300 10112 10207, .mulR 10301 10113 10206, .addR 10214 10300 10301,
    .mulR 10215 10113 10207, .mulR 10300 10200 10210, .mulR 10301 10203 10213,
    .subR 10216 10300 10301, .mulR 10300 10200 10211, .mulR 10301 10201 10210,
    .addR 10300 10300 10301, .mulR 10301 10203 10214, .subR 10300 10300 10301,
    .mulR 10301 10204 10213, .subR 10217 10300 10301, .mulR 10300 10200 10212,
    .mulR 10301 10201 10211, .addR 10300 10300 10301, .mulR 10301 10202 10210,
    .addR 10300 10300 10301, .mulR 10301 10203 10215, .subR 10300 10300 10301,
    .mulR 10301 10204 10214, .subR 10300 10300 10301, .mulR 10301 10205 10213,
    .subR 10218 10300 10301, .mulR 10300 10201 10212, .mulR 10301 10202 10211,
    .addR 10300 10300 10301, .mulR 10301 10204 10215, .subR 10300 10300 10301,
    .mulR 10301 10205 10214, .subR 10219 10300 10301, .mulR 10300 10202 10212,
    .mulR 10301 10205 10215, .subR 10220 10300 10301]

/-- **Spec of `polyStmt`**: cost `≤ 71`; the registers hold `xPoly`, `yPoly` and `dPoly` of the
three representations. -/
theorem polyStmt_spec {P : Polygon} {W : ℕ} (c : Config) (hc : WordsBounded W c) {ra rb rc : Rep}
    (ha : RepAt c 10100 ra) (hb : RepAt c 10110 rb) (hcc : RepAt c 10120 rc) :
    ∃ c' k, Exec P W polyStmt c c' k ∧ k ≤ 71 ∧
      [c'.rreg 10200, c'.rreg 10201, c'.rreg 10202, 0, 0] = xPoly ra rb ∧
      [c'.rreg 10206, c'.rreg 10207, 0, 0, 0] = yPoly ra rb ∧
      [c'.rreg 10216, c'.rreg 10217, c'.rreg 10218, c'.rreg 10219, c'.rreg 10220] =
        dPoly ra rb rc := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hcc
  simp only [Nat.reduceAdd] at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 c3 c4 c5
  unfold polyStmt
  exec_block
  refine ⟨⋄, ?_, ?_, ?_⟩ <;>
    simp only [xPoly, yPoly, dPoly, List.cons.injEq, and_true] <;> config_simp <;>
    ϴ a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, and_self

/-- Select the coefficient list of test `nreg 10009` into `rreg 10400 … 10404`. -/
def selStmt : Stmt :=
  .ifLtN 10009 10021
    (block [.copyR 10400 10200, .copyR 10401 10201, .copyR 10402 10202, .constR 10403 0,
      .constR 10404 0])
    (.ifLtN 10009 10022
      (block [.copyR 10400 10206, .copyR 10401 10207, .constR 10402 0, .constR 10403 0,
        .constR 10404 0])
      (block [.copyR 10400 10216, .copyR 10401 10217, .copyR 10402 10218, .copyR 10403 10219,
        .copyR 10404 10220]))

theorem testPoly_of_two_le {op : ℕ} (h : 2 ≤ op) (a b c : Rep) : testPoly op a b c = dPoly a b c := by
  match op, h with
  | n + 2, _ => rfl

/-- **Spec of `selStmt`**: cost `≤ 9`; the selected registers hold `testPoly op`. -/
theorem selStmt_spec {P : Polygon} {W : ℕ} (c : Config) (hc : WordsBounded W c) {ra rb rc : Rep}
    (h1 : c.nreg 10021 = 1) (h2 : c.nreg 10022 = 2)
    (hx : [c.rreg 10200, c.rreg 10201, c.rreg 10202, 0, 0] = xPoly ra rb)
    (hy : [c.rreg 10206, c.rreg 10207, 0, 0, 0] = yPoly ra rb)
    (hd : [c.rreg 10216, c.rreg 10217, c.rreg 10218, c.rreg 10219, c.rreg 10220] =
      dPoly ra rb rc) :
    ∃ c' k, Exec P W selStmt c c' k ∧ k ≤ 9 ∧
      [10400, 10401, 10402, 10403, 10404].map c'.rreg = testPoly (c.nreg 10009) ra rb rc := by
  unfold selStmt
  by_cases hA : c.nreg 10009 < 1
  · refine spec_ifLtN_true (by rw [h1]; exact hA) ?_
    have hop : c.nreg 10009 = 0 := ⋄
    exec_block
    refine ⟨⋄, ?_⟩
    Ξ hop, testPoly, ← hx
    config_simp
    simp
  · refine spec_ifLtN_false (by rw [h1]; exact hA) ?_
    by_cases hB : c.nreg 10009 < 2
    · refine spec_ifLtN_true (by rw [h2]; exact hB) ?_
      have hop : c.nreg 10009 = 1 := ⋄
      exec_block
      refine ⟨⋄, ?_⟩
      Ξ hop, testPoly, ← hy
      config_simp
      simp
    · refine spec_ifLtN_false (by rw [h2]; exact hB) ?_
      exec_block
      refine ⟨⋄, ?_⟩
      rw [testPoly_of_two_le (⋄), ← hd]
      config_simp
      simp

/-- The output bit: the positivity bit for tests `0, 1, 2`, the zero bit for test `3`. -/
def finStmt : Stmt :=
  .ifLtN 10009 10023 (.instr (.copyN 10010 10410)) (.instr (.copyN 10010 10411))

/-- **Spec of `finStmt`**: cost `≤ 3`. -/
theorem finStmt_spec {P : Polygon} {W : ℕ} (c : Config) (hc : WordsBounded W c)
    (h3 : c.nreg 10023 = 3) :
    ∃ c' k, Exec P W finStmt c c' k ∧ k ≤ 3 ∧
      (c.nreg 10009 < 3 → c'.nreg 10010 = c.nreg 10410) ∧
      (¬ c.nreg 10009 < 3 → c'.nreg 10010 = c.nreg 10411) := by
  unfold finStmt
  by_cases h : c.nreg 10009 < 3
  · refine spec_ifLtN_true (by rw [h3]; exact h) ?_
    refine spec_instr (Exec.copyN hc _ _) fun _ => ⟨⋄, fun _ => by config_simp, fun h' =>
      (h' h).elim⟩
  · refine spec_ifLtN_false (by rw [h3]; exact h) ?_
    refine spec_instr (Exec.copyN hc _ _) fun _ => ⟨⋄, fun h' => (h h').elim,
      fun _ => by config_simp⟩

end

end SignK

end Chazelle.Core
