module

public import Chazelle.Machine.Structured

/-! Evaluation of straight-line blocks that write only natural-number registers. The
permission predicate specifies which destinations the caller is willing to clobber. -/

namespace Chazelle.Machine

@[expose] public section

/-- The effect of a register instruction, with read-only memory `m`. -/
def regI (m : ℕ → ℕ) : Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | .constN r k, f => upd f r k
  | .copyN r a, f => upd f r (f a)
  | .addN r a b, f => upd f r (f a + f b)
  | .subN r a b, f => upd f r (f a - f b)
  | .loadN r a, f => upd f r (m (f a))
  | _, f => f

/-- The register effect of a block. -/
def regB (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | [], f => f
  | i :: l, f => regB m l (regI m i f)

/-- Destination of a supported instruction. -/
def dstI : Instr → ℕ
  | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => r
  | _ => 0

theorem regI_other (m f : ℕ → ℕ) (i : Instr) {q : ℕ} (hq : dstI i ≠ q) :
    regI m i f q = f q := by
  cases i <;> simp only [regI, dstI] at hq ⊢ <;> exact upd_other _ _ _ (Ne.symm hq)

/-- A block leaves the registers it does not write. -/
theorem regB_other (m : ℕ → ℕ) : ∀ (l : List Instr) (f : ℕ → ℕ) {q : ℕ},
    (∀ i ∈ l, dstI i ≠ q) → regB m l f q = f q
  | [], _, _, _ => rfl
  | i :: l, f, q, h => by
    rw [regB, regB_other m l _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact regI_other m f i (h i List.mem_cons_self)

/-- The destination permission and word bound for one register instruction. -/
def okRegI (allow : ℕ → Prop) (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN r k => allow r ∧ k ≤ W
  | .addN r a b => allow r ∧ f a + f b ≤ W
  | .copyN r _ | .subN r _ _ | .loadN r _ => allow r
  | _ => False

/-- Check the side conditions at each intermediate register state of a block. -/
def okRegB (allow : ℕ → Prop) (W : ℕ) (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → Prop
  | [], _ => True
  | i :: l, f => okRegI allow W f i ∧ okRegB allow W m l (regI m i f)

theorem okRegI.dst {allow : ℕ → Prop} {W : ℕ} {f : ℕ → ℕ} {i : Instr}
    (h : okRegI allow W f i) : allow (dstI i) := by
  cases i <;> simp only [okRegI, dstI] at h ⊢ <;> first | exact h | exact h.1

theorem okRegB.keeps {allow : ℕ → Prop} {W : ℕ} {m : ℕ → ℕ} {l : List Instr} {f : ℕ → ℕ}
    (h : okRegB allow W m l f) {q : ℕ} (hq : ¬ allow q) : regB m l f q = f q := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih => exact (ih h.2).trans (regI_other m f i fun e => hq (e ▸ h.1.dst))

/-- Symbolic execution of one checked register instruction. -/
theorem Exec.regInstr {P : Polygon} {W : ℕ} {c : Config} {i : Instr} {allow : ℕ → Prop}
    (hw : WordsBounded W c) (h : okRegI allow W c.nreg i) :
    Exec P W (.instr i) c { c with nreg := regI c.nmem i c.nreg } 1 := by
  cases i with
  | constN r v => exact .constN hw r v h.2
  | copyN r a => exact .copyN hw r a
  | addN r a b => exact .addN hw r a b h.2
  | subN r a b => exact .subN hw r a b
  | loadN r a => exact .loadN hw r a
  | _ => exact False.elim h

/-- Symbolic execution of a checked register block. -/
theorem Exec.regBlock {P : Polygon} {W : ℕ} {c : Config} {l : List Instr} {allow : ℕ → Prop}
    (hw : WordsBounded W c) (h : okRegB allow W c.nmem l c.nreg) :
    Exec P W (Stmt.block l) c { c with nreg := regB c.nmem l c.nreg } l.length := by
  induction l generalizing c with
  | nil => exact .block_nil hw
  | cons i l ih =>
    have e := Exec.regInstr (P := P) hw h.1
    exact .block_cons e (ih e.wb_right h.2)

end

end Chazelle.Machine
