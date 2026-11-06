module

public import Chazelle.Core.ClusterBfsRam
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics

/-!
# WP-I, part 9: phase frames and the fill procedure

* `PFr Rg Am c0 c`: from `c0` to `c` only the registers accepted by `Rg` and the memory cells
  accepted by `Am` change (real registers, real memory and output unchanged); `PFr.refl`,
  `PFr.trans`, `PFr.mono`, `PFr.nreg` (a register update), `PFr.nmem` (a store).
* `fillStmt`: fill `[b, b + n)` with the value `x` (registers `130150` base, `130151` length,
  `130152` value; scratch `130153`, `130154`), in at most `5 n + 2` steps (`fillStmt_exec`).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- **Phase frame**: only registers accepted by `Rg` and memory accepted by `Am` change. -/
def PFr (Rg Am : ℕ → Prop) (c0 c : Config) : Prop :=
  (∀ r, ¬ Rg r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Am a → c.nmem a = c0.nmem a

namespace PFr

variable {Rg Am : ℕ → Prop}

theorem refl (c : Config) : PFr Rg Am c c := ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem trans {c0 c1 c2 : Config} (h1 : PFr Rg Am c0 c1) (h2 : PFr Rg Am c1 c2) :
    PFr Rg Am c0 c2 :=
  ⟨fun r hr => (h2.1 r hr).trans (h1.1 r hr), h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, fun a ha => (h2.2.2.2.2 a ha).trans (h1.2.2.2.2 a ha)⟩

theorem mono {Rg' Am' : ℕ → Prop} {c0 c : Config} (h : PFr Rg Am c0 c)
    (hR : ∀ r, Rg r → Rg' r) (hA : ∀ a, Am a → Am' a) : PFr Rg' Am' c0 c :=
  ⟨fun r hr => h.1 r (fun h' => hr (hR r h')), h.2.1, h.2.2.1, h.2.2.2.1,
    fun a ha => h.2.2.2.2 a (fun h' => ha (hA a h'))⟩

theorem nreg {c0 c : Config} (h : PFr Rg Am c0 c) {f : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) : PFr Rg Am c0 { c with nreg := f } :=
  ⟨fun r hr => (hf r hr).trans (h.1 r hr), h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem nmem {c0 c : Config} (h : PFr Rg Am c0 c) {a x : ℕ} (ha : Am a) :
    PFr Rg Am c0 { c with nmem := upd c.nmem a x } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun b hb => by
    show upd c.nmem a x b = c0.nmem b
    rw [Machine.upd_other _ _ _ (fun e => hb (by rwx [e]))]; exact h.2.2.2.2 b hb⟩

theorem nreg_nmem {c0 c : Config} (h : PFr Rg Am c0 c) {f : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) {a x : ℕ} (ha : Am a) :
    PFr Rg Am c0 { c with nreg := f, nmem := upd c.nmem a x } :=
  ⟨fun r hr => (hf r hr).trans (h.1 r hr), h.2.1, h.2.2.1, h.2.2.2.1, fun b hb => by
    show upd c.nmem a x b = c0.nmem b
    rw [Machine.upd_other _ _ _ (fun e => hb (by rwx [e]))]; exact h.2.2.2.2 b hb⟩

theorem of_eq {c0 c : Config} (h : PFr Rg Am c0 c) {f g : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) (hg : ∀ a, ¬ Am a → g a = c.nmem a) :
    PFr Rg Am c0 { c with nreg := f, nmem := g } :=
  ⟨fun r hr => (hf r hr).trans (h.1 r hr), h.2.1, h.2.2.1, h.2.2.2.1,
    fun a ha => (hg a ha).trans (h.2.2.2.2 a ha)⟩

end PFr

/-! ## Filling an array -/

/-- One cell of the fill. -/
def fillCell : Stmt := block [.addN 130154 130150 130153, .storeN 130154 130152,
  .addN 130153 130153 130001]

/-- **Fill** `[b, b + n)` with `x`. -/
def fillStmt : Stmt := .seq (.instr (.constN 130153 0)) (.whileLtN 130153 130151 fillCell)

/-- The registers of the fill. -/
def FillScr (r : ℕ) : Prop := r = 130153 ∨ r = 130154

section fill

variable {P : Polygon} {W : ℕ}

/-- **The fill**: `[b, b + n)` holds `x` afterwards, nothing else changes but the scratch
registers `130153`, `130154`; cost `≤ 5 n + 3`. -/
theorem fillStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hb : c.nreg 130150 + c.nreg 130151 ≤ W) (hn : c.nreg 130151 + 1 ≤ W) :
    ∃ c' k, Exec P W fillStmt c c' k ∧ k ≤ 5 * c.nreg 130151 + 3 ∧
      PFr FillScr (fun a => c.nreg 130150 ≤ a ∧ a < c.nreg 130150 + c.nreg 130151) c c' ∧
      ∀ i, i < c.nreg 130151 → c'.nmem (c.nreg 130150 + i) = c.nreg 130152 := by
  have e0 := Exec.constN (P := P) hw 130153 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130153 0 }
  obtain ⟨c', k, e, hk, hI⟩ := forN (P := P) (W := W) (ri := 130153) (rn := 130151)
    (body := fillCell)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130153 = j ∧ c'.nreg 130151 = c.nreg 130151 ∧
      PFr FillScr (fun a => c.nreg 130150 ≤ a ∧ a < c.nreg 130150 + c.nreg 130151) c c' ∧
      ∀ i, i < j → c'.nmem (c.nreg 130150 + i) = c.nreg 130152)
    (c.nreg 130151) 3 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hm2⟩ => by
      have r1 : c2.nreg 130150 = c.nreg 130150 := hf2.1 _ (by ufo FillScr)
      have r2 : c2.nreg 130152 = c.nreg 130152 := hf2.1 _ (by ufo FillScr)
      have r3 : c2.nreg 130001 = 1 := (hf2.1 _ (by ufo FillScr)).trans hone
      unfold fillCell
      exec_block
      · rwo [r1, hi2]
      · config_simp; rwo [hi2, r3]
      · refine ⟨le_refl _, ‹_›, by config_simp; rw [hi2, r3], by config_simp; exact hn2, ?_,
          fun i hi => ?_⟩
        · refine PFr.nreg_nmem hf2 (fun r hr => ?_) ?_
          · simp only [Machine.upd_apply]; unfold FillScr at hr; splao
          · rwo [r1, hi2]
        · config_simp
          rw [r1, hi2, r2]
          rw [Machine.upd_apply]
          split_ifs with h
          · rfl
          · exact hm2 i (by omega))
    (j₀ := 0) ⟨e0.wb_right, by simp [c1], by simp [c1], PFr.nreg (PFr.refl c) (fun r hr => by
      simp only [Machine.upd_apply]; unfold FillScr at hr; splao),
      fun i hi => by omega⟩ (Nat.zero_le _)
  exact ⟨c', 1 + k, .seq e0 e, by omega, hI.2.2.2.1, hI.2.2.2.2⟩

end fill

end

end Chazelle.Core.Cluster
