module

public import Chazelle.Golf

public import Chazelle.Core.MergeAsmMath
public import Chazelle.Core.GranNFBounds

/-!
# WP-F merge assembly, part 2: the straight-line pieces of the merge program

Registers of band `bMerge` (`100000 …`): inputs `0 … 7, 9`, output `8` (as in `MergeSpec`), and

| register | content |
|---|---|
| `100010` | the model descriptor `B` (built at the allocator) |
| `100011 … 100015` | scratch of the descriptor copy |
| `100020`, `100021` | constants `1`, `5` |
| `100030 … 100036` | the maximum-degree loop: index, pointer, maximum, scratch, count, scratch |
| `100040 … 100045` | `γ₀`, scratch, `m`, `2 m`, (unused), `γ_R = min γ₀ (2 m) + 1` |

* `setF`: the arguments of the fusion (band `bFuse`);
* `descS`: a model descriptor of the whole chain at the allocator (`0`, then a copy of the five
  words of the whole-chain descriptor), the allocator bumped by `6`;
* `mdInit`, `mdLoop`: the largest length of the exit lists of the regions of the fused normal
  form (its degree, `degLe_of_lens`);
* `gamS`: `γ_R = min γ₀ (2 m) + 1` (every weight is at most the size `2 m`);
* `setR`, `setG`, `outS`: the arguments of restoration and granularity enforcement, the output.
-/

namespace Chazelle.Core

namespace MergeAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The program -/

/-- The arguments of the fusion. -/
def setF : Stmt := block [.copyN 70000 100000, .copyN 70001 100001, .copyN 70002 100002,
  .copyN 70003 100003, .copyN 70004 100004, .copyN 70005 100005, .copyN 70006 100007,
  .copyN 70008 100009]

/-- A model descriptor of the whole chain at the allocator. -/
def descS : Stmt := block [.constN 100020 1, .constN 100021 5, .copyN 100010 ALLOC,
  .constN 100011 0, .storeN 100010 100011, .copyN 100012 100002, .addN 100013 100010 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014,
  .constN 100015 6, .addN ALLOC ALLOC 100015]

/-- Initialisation of the maximum-degree loop (normal form at `70007`). -/
def mdInit : Stmt := block [.constN 100035 2, .addN 100036 70007 100035, .loadN 100034 100036,
  .constN 100035 5, .addN 100036 70007 100035, .loadN 100031 100036,
  .constN 100035 2, .addN 100031 100031 100035, .constN 100030 0, .constN 100032 0]

/-- One step of the maximum-degree loop. -/
def mdBody : Stmt :=
  .seq (block [.loadN 100033 100031])
    (.seq (.ifLtN 100032 100033 (block [.copyN 100032 100033]) .skip)
      (block [.addN 100031 100031 100021, .addN 100030 100030 100020]))

/-- The maximum-degree loop. -/
def mdLoop : Stmt := .whileLtN 100030 100034 mdBody

/-- `γ_R = min γ₀ (2 m) + 1` in `100045`. -/
def gamS : Stmt :=
  .seq (block [.copyN 100040 100005, .constN 100041 2, .addN 100041 100002 100041,
      .loadN 100042 100041, .addN 100043 100042 100042])
    (.seq (.ifLtN 100040 100043 (block [.copyN 100045 100040]) (block [.copyN 100045 100043]))
      (block [.addN 100045 100045 100020]))

/-- The arguments of restoration. -/
def setR : Stmt := block [.copyN 80000 100010, .copyN 80001 70007, .copyN 80002 100032,
  .copyN 80003 100007, .copyN 80004 100045, .copyN 80006 100009]

/-- The arguments of granularity enforcement. -/
def setG : Stmt := block [.copyN 90000 100010, .copyN 90001 80005, .copyN 90002 100007,
  .copyN 90003 100006]

/-- The output. -/
def outS : Stmt := block [.copyN 100008 90004]

/-- **The merge** (Lemma 3.5): fuse, restore conformality, restore granularity. -/
def mergeMk (fMk : Stmt → Stmt) (rMk : Stmt → Stmt → Stmt) (gS : Stmt) (sh cu : Stmt) : Stmt :=
  .seq setF (.seq (fMk sh) (.seq descS (.seq mdInit (.seq mdLoop (.seq gamS (.seq setR
    (.seq (rMk sh cu) (.seq setG (.seq gS outS)))))))))

/-! ## Register-only blocks -/

/-- A band predicate. -/
def inBand (b : ℕ) (r : ℕ) : Bool := decide (bandOf r = b)

theorem wr_setF : wr (inBand bFuse) setF = true := ⌖
theorem wr_setR : wr (inBand bRestore) setR = true := ⌖
theorem wr_setG : wr (inBand bGran) setG = true := ⌖
theorem wr_mdInit : wr (inBand bMerge) mdInit = true := ⌖
theorem wr_mdLoop : wr (inBand bMerge) mdLoop = true := ⌖
theorem wr_gamS : wr (inBand bMerge) gamS = true := ⌖

theorem setF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setF c c' k ∧ k = 8 ∧
      rd c' bFuse 0 = rd c bMerge 0 ∧ rd c' bFuse 1 = rd c bMerge 1 ∧
      rd c' bFuse 2 = rd c bMerge 2 ∧ rd c' bFuse 3 = rd c bMerge 3 ∧
      rd c' bFuse 4 = rd c bMerge 4 ∧ rd c' bFuse 5 = rd c bMerge 5 ∧
      rd c' bFuse 6 = rd c bMerge 7 ∧ rd c' bFuse 8 = rd c bMerge 9 ∧
      FrameB (inBand bFuse) c c' := by
  have ⟨c', k, e, hk, h⟩ : ∃ c' k, Exec P W setF c c' k ∧ k = 8 ∧
      (rd c' bFuse 0 = rd c bMerge 0 ∧ rd c' bFuse 1 = rd c bMerge 1 ∧
      rd c' bFuse 2 = rd c bMerge 2 ∧ rd c' bFuse 3 = rd c bMerge 3 ∧
      rd c' bFuse 4 = rd c bMerge 4 ∧ rd c' bFuse 5 = rd c bMerge 5 ∧
      rd c' bFuse 6 = rd c bMerge 7 ∧ rd c' bFuse 8 = rd c bMerge 9) := by
    unfold setF
    exec_block
    exact ⟨rfl, ⊚ rd, bandReg, bFuse, bMerge⟩
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, exec_frameB e wr_setF⟩

theorem setR_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setR c c' k ∧ k = 6 ∧
      rd c' bRestore 0 = c.nreg 100010 ∧ rd c' bRestore 1 = rd c bFuse 7 ∧
      rd c' bRestore 2 = c.nreg 100032 ∧ rd c' bRestore 3 = rd c bMerge 7 ∧
      rd c' bRestore 4 = c.nreg 100045 ∧ rd c' bRestore 6 = rd c bMerge 9 ∧
      FrameB (inBand bRestore) c c' := by
  have ⟨c', k, e, hk, h⟩ : ∃ c' k, Exec P W setR c c' k ∧ k = 6 ∧
      (rd c' bRestore 0 = c.nreg 100010 ∧ rd c' bRestore 1 = rd c bFuse 7 ∧
      rd c' bRestore 2 = c.nreg 100032 ∧ rd c' bRestore 3 = rd c bMerge 7 ∧
      rd c' bRestore 4 = c.nreg 100045 ∧ rd c' bRestore 6 = rd c bMerge 9) := by
    unfold setR
    exec_block
    exact ⟨rfl, ⊚ rd, bandReg, bFuse, bMerge, bRestore⟩
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    exec_frameB e wr_setR⟩

theorem setG_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setG c c' k ∧ k = 4 ∧
      rd c' bGran 0 = c.nreg 100010 ∧ rd c' bGran 1 = rd c bRestore 5 ∧
      rd c' bGran 2 = rd c bMerge 7 ∧ rd c' bGran 3 = rd c bMerge 6 ∧
      FrameB (inBand bGran) c c' := by
  have ⟨c', k, e, hk, h⟩ : ∃ c' k, Exec P W setG c c' k ∧ k = 4 ∧
      (rd c' bGran 0 = c.nreg 100010 ∧ rd c' bGran 1 = rd c bRestore 5 ∧
      rd c' bGran 2 = rd c bMerge 7 ∧ rd c' bGran 3 = rd c bMerge 6) := by
    unfold setG
    exec_block
    exact ⟨rfl, ⊚ rd, bandReg, bGran, bMerge, bRestore⟩
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2, exec_frameB e wr_setG⟩

theorem outS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W outS c c' k ∧ k = 1 ∧ rd c' bMerge 8 = rd c bGran 4 ∧
      FrameB (fun r => r == 100008) c c' := by
  have ⟨c', k, e, hk, h⟩ : ∃ c' k, Exec P W outS c c' k ∧ k = 1 ∧
      rd c' bMerge 8 = rd c bGran 4 := by
    unfold outS
    exec_block
    exact ⟨rfl, ⊚ rd, bandReg, bGran, bMerge⟩
  exact ⟨c', k, e, hk, h, exec_frameB e (⌖)⟩

/-! ## `γ_R` -/

theorem gamS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h20 : c.nreg 100020 = 1) {g m : ℕ} (hg : rd c bMerge 5 = g)
    (hm : c.nmem (rd c bMerge 2 + 2) = m) (hgW : g + 1 ≤ W) (hmW : 2 * m ≤ W)
    (h2W : rd c bMerge 2 + 2 ≤ W) :
    ∃ c' k, Exec P W gamS c c' k ∧ k ≤ 9 ∧ c'.nreg 100045 = min g (2 * m) + 1 ∧
      FrameB (inBand bMerge) c c' ∧ (∀ r, r < 100040 → c'.nreg r = c.nreg r) := by
  have hg' : c.nreg 100005 = g := hg
  have hm' : c.nmem (c.nreg 100002 + 2) = m := hm
  have h2W' : c.nreg 100002 + 2 ≤ W := h2W
  obtain ⟨c₁, k₁, e₁, hk₁, v40, v43, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 100040 100005,
      .constN 100041 2, .addN 100041 100002 100041, .loadN 100042 100041,
      .addN 100043 100042 100042]) c c₁ k₁ ∧
      k₁ = 5 ∧ c₁.nreg 100040 = g ∧ c₁.nreg 100043 = 2 * m ∧
      ∀ r, r < 100040 → c₁.nreg r = c.nreg r := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hg', hm']; omega)
    refine ⟨rfl, ?_, ?_, fun r hr => ?_⟩
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hg']
    · simp (disch := omega) only [Machine.upd_same,
        hm']
      ring
    · simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have tail : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 100045 = min g (2 * m) →
      c₂.nreg 100020 = 1 → ∃ c₃, Exec P W (block [.addN 100045 100045 100020]) c₂ c₃ 1 ∧
        c₃.nreg 100045 = min g (2 * m) + 1 ∧ ∀ r, r ≠ 100045 → c₃.nreg r = c₂.nreg r :=
    fun c₂ hw₂ h45 h20' => by
      have e := Exec.addN (P := P) hw₂ 100045 100045 100020 (by
        rw [h45, h20']; have := min_le_left g (2 * m); omega)
      exact ⟨_, .seq e (.skip e.wb_right), by simp only [upd_same]; rw [h45, h20'],
        fun r hr => by simp only [upd_other _ _ _ hr]⟩
  by_cases hlt : c₁.nreg 100040 < c₁.nreg 100043
  · have e₂ := Exec.copyN (P := P) hw₁ 100045 100040
    obtain ⟨c₃, e₃, v₃, r₃⟩ := tail _ e₂.wb_right (by
        simp only [upd_same]; rw [v40]; rw [v40, v43] at hlt; omega)
      (by simp only [upd_other _ _ _ (show (100020 : ℕ) ≠ 100045 by decide)]
          rw [r₁ _ (by decide), h20])
    have ex : Exec P W gamS c c₃ (k₁ + ((1 + 0) + 1 + 1)) :=
      .seq e₁ (.seq (.ifLtN_true hlt (.seq e₂ (.skip e₂.wb_right))) e₃)
    refine ⟨c₃, _, ex, by omega, v₃, exec_frameB ex wr_gamS, fun r hr => ?_⟩
    rw [r₃ r (by omega)]
    simp only [upd_other _ _ _ (show r ≠ 100045 by omega)]; exact r₁ r hr
  · have e₂ := Exec.copyN (P := P) hw₁ 100045 100043
    obtain ⟨c₃, e₃, v₃, r₃⟩ := tail _ e₂.wb_right (by
        simp only [upd_same]; rw [v43]; rw [v40, v43] at hlt; omega)
      (by simp only [upd_other _ _ _ (show (100020 : ℕ) ≠ 100045 by decide)]
          rw [r₁ _ (by decide), h20])
    have ex : Exec P W gamS c c₃ (k₁ + ((1 + 0) + 2 + 1)) :=
      .seq e₁ (.seq (.ifLtN_false hlt (.seq e₂ (.skip e₂.wb_right))) e₃)
    refine ⟨c₃, _, ex, by omega, v₃, exec_frameB ex wr_gamS, fun r hr => ?_⟩
    rw [r₃ r (by omega)]
    simp only [upd_other _ _ _ (show r ≠ 100045 by omega)]; exact r₁ r hr

end

end MergeAsm

end Chazelle.Core
