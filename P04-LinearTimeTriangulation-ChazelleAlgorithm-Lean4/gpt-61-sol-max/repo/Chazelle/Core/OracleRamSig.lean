module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.WalkKey

/-!
# Lemma 3.6 (WP-H), RAM part 1: calling the sign kernel on registers

`sgnS op s₁ s₂ s₃` loads three symbolic points from registers (`SymSrc`: a vertex index, an edge
point `(e, h)`, or three consecutive registers in the `SymPtIn` layout) into the input slots of
the sign kernel (`10000`, `10003`, `10006`), sets the test `op`, and runs the kernel.
`sgnS_exec`: at most `245` steps, only the registers `10000 … 10499` written (`WalkKey.Bk`), the
answer bit in `10010`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- **A source of a symbolic point** in registers. -/
inductive SymSrc where
  /-- The vertex whose index is in register `r`. -/
  | vtx (r : ℕ)
  /-- The point of the edge in register `re` at the height of the vertex in register `rh`. -/
  | edge (re rh : ℕ)
  /-- Three registers `r, r + 1, r + 2` in the `SymPtIn` layout. -/
  | regs (r : ℕ)

/-- The instructions loading a source into the slot `t`. -/
def SymSrc.load (t : ℕ) : SymSrc → List Instr
  | .vtx r => [.constN t 0, .copyN (t + 1) r]
  | .edge re rh => [.constN t 1, .copyN (t + 1) re, .copyN (t + 2) rh]
  | .regs r => [.copyN t r, .copyN (t + 1) (r + 1), .copyN (t + 2) (r + 2)]

/-- The source holds the symbolic point `p` in `c`. -/
def SymSrc.Holds (c : Config) : SymSrc → SymPt → Prop
  | .vtx r, p => p = .vtx (c.nreg r)
  | .edge re rh, p => p = .onEdge (c.nreg re) (c.nreg rh)
  | .regs r, p => SymPtIn c r p

/-- The registers read by a source avoid the kernel's registers. -/
def SymSrc.Out : SymSrc → Prop
  | .vtx r => Bk r = false
  | .edge re rh => Bk re = false ∧ Bk rh = false
  | .regs r => Bk r = false ∧ Bk (r + 1) = false ∧ Bk (r + 2) = false

/-- A frame for fewer registers is a frame for more. -/
theorem FrameB.mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ <;>
  grind

instance (s : SymSrc) : Decidable s.Out := by
  cases s <;> unfold SymSrc.Out <;> infer_instance

/-- **Calling the sign kernel** on three sources with the test `op`. -/
def sgnS (op : ℕ) (s₁ s₂ s₃ : SymSrc) : Stmt :=
  .seq (block (s₁.load 10000)) (.seq (block (s₂.load 10003)) (.seq (block (s₃.load 10006))
    (.seq (.instr (.constN 10009 op)) signProg)))

theorem wr_load (t : ℕ) (ht : 10000 ≤ t ∧ t + 2 < 10500) (s : SymSrc) :
    wr Bk (block (s.load t)) = true := by
  cases s <;> simp [SymSrc.load, block, wr, wrOK, Bk] <;> omega

/-- Two sources agree on configurations that agree on their registers. -/
theorem holds_congr {c c' : Config} {s : SymSrc} {p : SymPt} (hs : s.Out)
    (hc : ∀ r, Bk r = false → c'.nreg r = c.nreg r) (h : s.Holds c p) : s.Holds c' p := by
  cases s with
  | vtx r => simp only [SymSrc.Holds] at h ⊢; ram_grind
  | edge re rh =>
    simp only [SymSrc.Holds] at h ⊢; ram_grind
  | regs r =>
    simp only [SymSrc.Holds] at h ⊢
    cases p with
    | vtx i =>
      simp only [SymPtIn] at h ⊢
      ram_grind
    | onEdge e h' =>
      simp only [SymPtIn] at h ⊢
      ram_grind

/-- Close a goal about explicit register updates by case analysis. -/
macro "upd_solve" : tactic =>
  `(tactic| (simp only [Machine.upd_apply]; (repeat' split_ifs) <;> first | rfl | omega | simp_all))

/-- **Loading a source** into the slot `t`. -/
theorem load_exec {P : Polygon} {W : ℕ} (t : ℕ) (hW : 1 ≤ W) (s : SymSrc) (c : Config)
    (hw : WordsBounded W c) (hs : s.Out) (hts : ∀ r, Bk r = false → r ≠ t ∧ r ≠ t + 1 ∧ r ≠ t + 2)
    {p : SymPt} (hp : s.Holds c p) :
    ∃ c' k, Exec P W (block (s.load t)) c c' k ∧ k ≤ 3 ∧ SymPtIn c' t p ∧
      (∀ r, r ≠ t → r ≠ t + 1 → r ≠ t + 2 → c'.nreg r = c.nreg r) := by
  cases s with
  | vtx r =>
    simp only [SymSrc.Holds] at hp
    subst hp
    have h1 := hts r hs
    simp only [SymSrc.load]
    exec_block
    · omega
    simp_all [SymPtIn] 
  | edge re rh =>
    simp only [SymSrc.Holds] at hp
    subst hp
    have h1 := hts re hs.1
    have h2 := hts rh hs.2
    simp only [SymSrc.load]
    exec_block
    · omega
    · refine ⟨by omega, ?_, fun r' h1' h2' h3' => ?_⟩
      · simp_all [SymPtIn] 
      simp_all
  | regs r =>
    simp only [SymSrc.Holds] at hp
    
    
    have h3 := hts (r + 2) hs.2.2
    simp only [SymSrc.load]
    exec_block
    refine ⟨by omega, ?_, fun r' h1' h2' h3' => ?_⟩
    · cases p with
      | vtx i =>
        simp only [SymPtIn] at hp ⊢
        obtain ⟨hp1, hp2⟩ := hp
        refine ⟨?_, ?_⟩ <;> upd_solve
      | onEdge e h =>
        simp only [SymPtIn] at hp ⊢
        config_simp
        obtain ⟨hp1, hp2, hp3⟩ := hp
        refine ⟨?_, ?_, ?_⟩ <;> upd_solve
    · config_simp
      upd_solve

theorem Bk_false_ne {r : ℕ} (h : Bk r = false) (t : ℕ) (ht : 10000 ≤ t ∧ t + 2 < 10500) :
    r ≠ t ∧ r ≠ t + 1 ∧ r ≠ t + 2 := by
  ram_grind

/-- **The sign kernel on three sources.** -/
theorem sgnS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (op : ℕ)
    (hop : op ≤ 3) (s₁ s₂ s₃ : SymSrc) (c : Config) (hw : WordsBounded W c) (o₁ : s₁.Out)
    (o₂ : s₂.Out) (o₃ : s₃.Out) {p₁ p₂ p₃ : SymPt} (h₁ : s₁.Holds c p₁) (h₂ : s₂.Holds c p₂)
    (h₃ : s₃.Holds c p₃) (l₁ : p₁.Lt P.n) (l₂ : p₂.Lt P.n) (l₃ : p₃.Lt P.n) :
    ∃ c' k, Exec P W (sgnS op s₁ s₂ s₃) c c' k ∧ k ≤ 245 ∧ FrameB Bk c c' ∧
      c'.nreg 10010 ≤ 1 ∧
      (c'.nreg 10010 = 1 ↔ SignTest op (p₁.eval (Qof P)) (p₂.eval (Qof P)) (p₃.eval (Qof P))) := by
  have hW1 : 1 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, i₁, r₁⟩ := load_exec (P := P) 10000 hW1 s₁ c hw o₁
    (fun r hr => Bk_false_ne hr 10000 (by norm_num)) h₁
  have f₁ := exec_frameB e₁ (wr_load 10000 (by norm_num) s₁)
  obtain ⟨c₂, k₂, e₂, hk₂, i₂, r₂⟩ := load_exec (P := P) 10003 hW1 s₂ c₁ e₁.wb_right o₂
    (fun r hr => Bk_false_ne hr 10003 (by norm_num)) (holds_congr o₂ f₁.1 h₂)
  have f₂ := exec_frameB e₂ (wr_load 10003 (by norm_num) s₂)
  obtain ⟨c₃, k₃, e₃, hk₃, i₃, r₃⟩ := load_exec (P := P) 10006 hW1 s₃ c₂ e₂.wb_right o₃
    (fun r hr => Bk_false_ne hr 10006 (by norm_num))
    (holds_congr o₃ (fun r hr => (f₂.1 r hr).trans (f₁.1 r hr)) h₃)
  have f₃ := exec_frameB e₃ (wr_load 10006 (by norm_num) s₃)
  have w₄ := WordsBounded.upd_nreg e₃.wb_right (show op ≤ W by omega) c₃.pc (r := 10009)
  have e₄ := Exec.constN e₃.wb_right 10009 op (P := P) (show op ≤ W by omega)
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 10009 op } with hc₄
  -- the slots survive the later loads
  have keep : ∀ (d : Config) (t : ℕ) (q : SymPt), SymPtIn d t q →
      ∀ d' : Config, (∀ r, r = t ∨ r = t + 1 ∨ r = t + 2 → d'.nreg r = d.nreg r) →
        SymPtIn d' t q := by
    intro d t q hq d' hd
    cases q with
    | vtx i =>
      core_grind
    | onEdge e h =>
      core_grind
  have j₁ : SymPtIn c₄ 10000 p₁ := keep c₁ 10000 p₁ i₁ c₄ fun r hr => by
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ (by omega), r₃ r (by omega) (by omega) (by omega),
      r₂ r (by omega) (by omega) (by omega)]
  have j₂ : SymPtIn c₄ 10003 p₂ := keep c₂ 10003 p₂ i₂ c₄ fun r hr => by
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ (by omega), r₃ r (by omega) (by omega) (by omega)]
  have j₃ : SymPtIn c₄ 10006 p₃ := keep c₃ 10006 p₃ i₃ c₄ fun r hr => by
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ (by omega)]
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ w₄ hG hW
    (by rw [hc₄]; config_simp; omega) l₁ l₂ l₃ j₁ j₂ j₃
  have op₄ : c₄.nreg 10009 = op := by ram_simp 
  rw [op₄] at sig₅
  have f₄ : FrameB Bk c₃ c₄ := by
    refine ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ (by simp only [Bk, decide_eq_false_iff_not, not_and, not_lt] at hr; omega)]
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (1 + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    f₁.trans (f₂.trans (f₃.trans (f₄.trans f₅))), bit₅, sig₅⟩

end

end OracleR

end Chazelle.Core
