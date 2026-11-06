module

public import Chazelle.Core.BruteSig
public import Chazelle.Core.DownPhaseDrvRLib

/-!
# Down-phase base (D9), RAM: sign tests on points held in register triples

The host points of a region are symbolic points of `Q` whose kind (vertex or edge point) is known
only at run time; the base keeps them in register triples `x, x + 1, x + 2` in the layout of the
sign kernel (`SymPtIn`: kind `0` vertex / `1` edge point, then the indices).

* `tstR op x y z d`: copies the three triples into the kernel's input registers, runs the sign
  kernel `SignK.signProg` (test `op`) and copies the answer bit into `d` (`tstR_exec`: at most `245`
  steps, writes only the kernel's registers `10000 … 10499` and `d`).
* `symPtIn_copy`: a triple copied register by register holds the same symbolic point.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- A triple copied register by register holds the same symbolic point. -/
theorem symPtIn_copy {c c' : Config} {x s : ℕ} {p : SymPt} (h : SymPtIn c x p)
    (h0 : c'.nreg s = c.nreg x) (h1 : c'.nreg (s + 1) = c.nreg (x + 1))
    (h2 : c'.nreg (s + 2) = c.nreg (x + 2)) : SymPtIn c' s p := by
  cases p with
  | vtx i => exact ⟨h0.trans h.1, h1.trans h.2⟩
  | onEdge e hh => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩

/-- Register frames compose. -/
theorem fbTrans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameB B c₁ c₂) (h₂ : FrameB B c₂ c₃) :
    FrameB B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), fun r hr => (h₂.2.1 r hr).trans (h₁.2.1 r hr),
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-- A register frame for fewer registers is one for more. -/
theorem fbMono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    fun r hr => h.2.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Copy a register triple into the kernel registers from `s`. -/
def ldP (s x : ℕ) : List Instr := [.copyN s x, .copyN (s + 1) (x + 1), .copyN (s + 2) (x + 2)]

/-- **A sign test on three points held in register triples**, answer bit into `d`. -/
def tstR (op x y z d : ℕ) : Stmt :=
  .seq (block (ldP 10000 x ++ ldP 10003 y ++ ldP 10006 z ++ [.constN 10009 op]))
    (.seq signProg (.instr (.copyN d 10010)))

/-- A register triple outside the kernel's registers. -/
def OutK (x : ℕ) : Prop := x + 3 ≤ 10000 ∨ 10500 ≤ x

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **A sign test on register triples** (at most `245` steps). -/
theorem tstR_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ} (hop : op ≤ 3) {x y z d : ℕ}
    (hx : OutK x) (hy : OutK y) (hz : OutK z) (c : Config) (hw : WordsBounded W c)
    {s₁ s₂ s₃ : SymPt} (i₁ : SymPtIn c x s₁) (i₂ : SymPtIn c y s₂) (i₃ : SymPtIn c z s₃)
    (l₁ : s₁.Lt P.n) (l₂ : s₂.Lt P.n) (l₃ : s₃.Lt P.n) :
    ∃ c' k, Exec P W (tstR op x y z d) c c' k ∧ k ≤ 245 ∧ FrameB (Brute.Bt d) c c' ∧
      c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op (s₁.eval (Qof P)) (s₂.eval (Qof P)) (s₃.eval (Qof P))) := by
  unfold OutK at hx hy hz
  have hop' : op ≤ W := by omega
  -- the loads
  obtain ⟨c₁, k₁, e₁, hk₁, q₁, q₂, q₃, q₉, hf₁⟩ : ∃ c₁ k₁, Exec P W (block (ldP 10000 x ++
      ldP 10003 y ++ ldP 10006 z ++ [.constN 10009 op])) c c₁ k₁ ∧ k₁ = 10 ∧
      SymPtIn c₁ 10000 s₁ ∧ SymPtIn c₁ 10003 s₂ ∧ SymPtIn c₁ 10006 s₃ ∧ c₁.nreg 10009 = op ∧
      FrameB Bk c c₁ := by
    obtain ⟨c₁, k₁, e₁, hk₁, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, fr⟩ :
        ∃ c₁ k₁, Exec P W (block (ldP 10000 x ++ ldP 10003 y ++ ldP 10006 z ++
          [.constN 10009 op])) c c₁ k₁ ∧ k₁ = 10 ∧
        c₁.nreg 10000 = c.nreg x ∧ c₁.nreg 10001 = c.nreg (x + 1) ∧
        c₁.nreg 10002 = c.nreg (x + 2) ∧ c₁.nreg 10003 = c.nreg y ∧
        c₁.nreg 10004 = c.nreg (y + 1) ∧ c₁.nreg 10005 = c.nreg (y + 2) ∧
        c₁.nreg 10006 = c.nreg z ∧ c₁.nreg 10007 = c.nreg (z + 1) ∧
        c₁.nreg 10008 = c.nreg (z + 2) ∧ c₁.nreg 10009 = op ∧
        (∀ r, (r < 10000 ∨ 10010 ≤ r) → c₁.nreg r = c.nreg r) ∧
        c₁.rreg = c.rreg ∧ c₁.nmem = c.nmem ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
      simp only [ldP, List.cons_append, List.nil_append]
      exec_block
      · exact hop'
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;>
          (try intro r hr) <;> config_simp <;>
          (try simp only [Machine.upd_apply]) <;> (try split_ifs) <;> (try omega) <;>
          (repeat rw [ite_eq_right (by omega)])
    refine ⟨c₁, k₁, e₁, hk₁, symPtIn_copy i₁ r0 r1 r2, symPtIn_copy i₂ r3 r4 r5,
      symPtIn_copy i₃ r6 r7 r8, r9, ⟨fun r hr => ?_, fun r _ => by rw [fr.2.1], fr.2.2.1,
      fr.2.2.2.1, fr.2.2.2.2⟩⟩
    · have : r < 10000 ∨ 10500 ≤ r := by unfold Bk at hr; simp at hr; omega
      exact fr.1 r (by omega)
  -- the kernel
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, s₂'⟩ := sig_exec (P := P) c₁ e₁.wb_right hG hW
    (by rwa [q₉]) l₁ l₂ l₃ q₁ q₂ q₃
  rw [q₉] at s₂'
  -- the answer
  have e₃ := Exec.copyN (P := P) e₂.wb_right d 10010
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg d (c₂.nreg 10010) }
  refine ⟨c₃, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega, ?_, by simp [c₃, b₂],
    by simp [c₃]; exact s₂'⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : Bk r = false ∧ r ≠ d := by
      unfold Brute.Bt at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      exact hr
    simp only [c₃]
    rw [Machine.upd_other _ _ _ hr'.2, f₂.1 r hr'.1, hf₁.1 r hr'.1]
  · have hr' : Bk r = false := by
      unfold Brute.Bt at hr; simp only [Bool.or_eq_false_iff] at hr; exact hr.1
    simp only [c₃]; rw [f₂.2.1 r hr', hf₁.2.1 r hr']
  · simp only [c₃]; rw [f₂.2.2.1, hf₁.2.2.1]
  · simp only [c₃]; rw [f₂.2.2.2.1, hf₁.2.2.2.1]
  · simp only [c₃]; rw [f₂.2.2.2.2, hf₁.2.2.2.2]

end exec

end

end DrvB

end Chazelle.Core
