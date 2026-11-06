module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.WalkKey
public import Chazelle.Core.BruteOK

/-!
# WP-K: sign tests on symbolic points held in registers

A thin layer over the sign kernel (`WalkKey.sig_exec`): the three points of a test are described
by *sources* (`Src`): a vertex whose index is in a register, or an edge point whose edge and
height vertex are in two registers.  `testS op x y z d` loads the three points into the kernel's
input registers, runs the kernel and copies the answer bit into register `d`
(`testS_exec`: at most `245` steps, only the kernel's registers `10000 … 10499` and `d` change).
-/

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- A symbolic point in registers: a vertex (index register) or an edge point (edge and height
registers). -/
inductive Src where
  | v (r : ℕ)
  | e (r₁ r₂ : ℕ)

/-- Load a source into the three kernel registers from `s`. -/
def Src.load (s : ℕ) : Src → Stmt
  | .v r => block [.constN s 0, .copyN (s + 1) r]
  | .e r₁ r₂ => block [.constN s 1, .copyN (s + 1) r₁, .copyN (s + 2) r₂]

/-- The symbolic point of a source in a configuration. -/
def Src.pt (c : Config) : Src → SymPt
  | .v r => .vtx (c.nreg r)
  | .e r₁ r₂ => .onEdge (c.nreg r₁) (c.nreg r₂)

/-- The registers of a source are outside the kernel's registers. -/
def Src.Out : Src → Prop
  | .v r => r < 10000 ∨ 10500 ≤ r
  | .e r₁ r₂ => (r₁ < 10000 ∨ 10500 ≤ r₁) ∧ (r₂ < 10000 ∨ 10500 ≤ r₂)

/-- A sign test with its answer bit copied to register `d`. -/
def testS (op : ℕ) (x y z : Src) (d : ℕ) : Stmt :=
  .seq (x.load 10000) (.seq (y.load 10003) (.seq (z.load 10006)
    (.seq (.instr (.constN 10009 op)) (.seq signProg (.instr (.copyN d 10010))))))

theorem load_exec {P : Polygon} {W : ℕ} (hW : 1 ≤ W) (s : ℕ) (hs : 10000 ≤ s ∧ s + 3 ≤ 10500)
    (x : Src) (hx : x.Out) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (x.load s) c c' k ∧ k ≤ 3 ∧ SymPtIn c' s (x.pt c) ∧
      (∀ r, (r < s ∨ s + 3 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  cases x with
  | v r =>
    ϴ' Src.Out at hx
    unfold Src.load
    exec_block
    · omega
    · refine ⟨⋄, ?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
      · ϴ Src.pt, SymPtIn
        refine ⟨?_, ?_⟩ <;> simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other]
      · simp (disch := omega) only [Machine.upd_other]
  | e r₁ r₂ =>
    ϴ' Src.Out at hx
    unfold Src.load
    exec_block
    · omega
    · refine ⟨⋄, ?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
      · ϴ Src.pt, SymPtIn
        refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other]
      · simp (disch := omega) only [Machine.upd_other]

theorem src_pt_eq {x : Src} (hx : x.Out) {c c' : Config}
    (h : ∀ r, (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) : x.pt c' = x.pt c := by
  cases x with
  | v r => simp only [Src.pt, Src.Out] at hx ⊢; Ξ h r hx
  | e r₁ r₂ => simp only [Src.pt, Src.Out] at hx ⊢; Ξ h r₁ hx.1, h r₂ hx.2

/-- The write set of a test: the kernel's registers and the destination. -/
def Bt (d : ℕ) (r : ℕ) : Bool := Bk r || decide (r = d)

/-- **A sign test into register `d`** (at most `245` steps). -/
theorem testS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ}
    (hop : op ≤ 3) {x y z : Src} (hx : x.Out) (hy : y.Out) (hz : z.Out) {d : ℕ}
    (c : Config) (hw : WordsBounded W c) (hlx : (x.pt c).Lt P.n) (hly : (y.pt c).Lt P.n)
    (hlz : (z.pt c).Lt P.n) :
    ∃ c' k, Exec P W (testS op x y z d) c c' k ∧ k ≤ 245 ∧ FrameB (Bt d) c c' ∧
      c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op ((x.pt c).eval (Qof P)) ((y.pt c).eval (Qof P))
        ((z.pt c).eval (Qof P))) := by
  have hW1 : 1 ≤ W := ⋄
  obtain ⟨c₁, k₁, e₁, hk₁, s₁, r₁, rr₁, m₁, rm₁, o₁⟩ :=
    load_exec (P := P) hW1 10000 (⋄) x hx c hw
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, r₂, rr₂, m₂, rm₂, o₂⟩ :=
    load_exec (P := P) hW1 10003 (⋄) y hy c₁ e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, rr₃, m₃, rm₃, o₃⟩ :=
    load_exec (P := P) hW1 10006 (⋄) z hz c₂ e₂.wb_right
  have e₄ := Exec.constN (P := P) e₃.wb_right 10009 op (⋄)
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 10009 op }
  have q₄ : ∀ r, r ≠ 10009 → c₄.nreg r = c₃.nreg r := fun r hr => ⊚ c₄, hr
  -- the points survive
  have hy₁ : y.pt c₁ = y.pt c := src_pt_eq hy fun r hr => r₁ r (⋄)
  have hz₁ : z.pt c₂ = z.pt c := by
    rw [src_pt_eq hz fun r hr => r₂ r (⋄)]
    exact src_pt_eq hz fun r hr => r₁ r (⋄)
  have S₁ : SymPtIn c₄ 10000 (x.pt c) := symPtIn_of_eq s₁ fun j h1 h2 => by
    rw [q₄ j (⋄), r₃ j (by omega), r₂ j (by omega)]
  have S₂ : SymPtIn c₄ 10003 (y.pt c) := by
    Ξ ← hy₁
    exact symPtIn_of_eq s₂ fun j h1 h2 => by rw [q₄ j (⋄), r₃ j (by omega)]
  have S₃ : SymPtIn c₄ 10006 (z.pt c) := by
    Ξ ← hz₁
    exact symPtIn_of_eq s₃ fun j h1 h2 => by rw [q₄ j (⋄)]
  have hop₄ : c₄.nreg 10009 = op := ⊚ c₄
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ e₄.wb_right hG hW
    (by rw [hop₄]; exact hop) hlx hly hlz S₁ S₂ S₃
  rw [hop₄] at sig₅
  have e₆ := Exec.copyN (P := P) e₅.wb_right d 10010
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg d (c₅.nreg 10010) }
  have ex : Exec P W (testS op x y z d) c c₆ (k₁ + (k₂ + (k₃ + (1 + (k₅ + 1))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have hd : c₆.nreg d = c₅.nreg 10010 := ⊚ c₆
  refine ⟨c₆, _, ex, ⋄, ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩, by rw [hd]; exact bit₅,
    by rw [hd]; exact sig₅⟩
  · have hr' : Bk r = false ∧ r ≠ d := by
      unfold Bt at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; exact hr
    have hnk : r < 10000 ∨ 10500 ≤ r := by
      have := hr'.1; unfold Bk at this; simp only [decide_eq_false_iff_not] at this; omega
    ϴ c₆
    rw [upd_other _ _ _ hr'.2, f₅.1 r hr'.1, q₄ r (⋄), r₃ r (by omega), r₂ r (by omega),
      r₁ r (⋄)]
  · have hr' : Bk r = false := by
      unfold Bt at hr; simp only [Bool.or_eq_false_iff] at hr; exact hr.1
    ϴ c₆
    Ξ f₅.2.1 r hr', rr₃, rr₂, rr₁
  · simp only [c₆]; rw [f₅.2.2.1, m₃, m₂, m₁]
  · simp only [c₆]; rw [f₅.2.2.2.1, rm₃, rm₂, rm₁]
  · simp only [c₆]; rw [f₅.2.2.2.2, o₃, o₂, o₁]

end

end Brute

end Chazelle.Core
