module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvInit

/-!
# The sweep (WP-D), stages 2–3: the initialisation, part 2 (the top of `C₁`, the descriptor)

* `symS`: the symbolic point of the top of `C₁` (`cT1 = sw 645 … 647`), by `callSym` on the
  descriptor of `C₁` (`sw 20`) at the walk position `(6, 0)` (a copy of the top);
* `md1S`: the model descriptor `MD₁` of `C₁` in fresh memory: `0`, then a copy of the five words of
  the chain descriptor at `sw 20`, with `CD₁ = MD₁ + 1`; the allocator moves by `6`.

Frames: `frame_of_irs` (a run step from its own start is a frame of the sweep and oracle bands),
`frame_regs` (a register-only step).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

def iE : ℕ := sw 705
def iH : ℕ := sw 706
def iY : ℕ := sw 707
def iA : ℕ := sw 710
def iV : ℕ := sw 711

set_option hygiene false in
/-- Register arithmetic on the named registers of the initialisation. -/
macro "swoInit2" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only [iL, iT, iG, iE, iH, iY, iA, iV,
  iO, iB, MD₁, CD₁, K0, K1, K2, K3, K4, K5, K6, ALLOC, cT1, TBR, TLR, cTB, sw] at *; omega))

/-! ## Frames -/

/-- A run step from its own start is a frame of `ioBands`. -/
theorem frame_of_irs {W : ℕ} {c c' : Config} {k : ℕ} (hI : IInv W c c') (hf : IFr c c' k) :
    Frame ioBands c c' k :=
  ⟨hf.1, hf.2.1, hI.hm, hI.hrm, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

/-- A step changing only registers of `ioBands` (not the allocator) is a frame. -/
theorem frame_regs {c c' : Config} (k : ℕ) (hr : ∀ r, bandOf r ∉ ioBands → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : Frame ioBands c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC alloc_not_io
  exact ⟨fun r h _ => hr r h, fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by rw [hA], by rw [hA]; omega⟩

theorem frame_ioB {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame (B ∪ B) c c' k) :
    Frame B c c' k := by
  Ξ' Finset.union_self at h; exact h

/-- Registers of the sweep's band are in `ioBands`. -/
theorem sw_io {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∈ ioBands := by
  rw [band_sw h1 h2]; exact bSweep_mem

/-! ## The top of `C₁` -/

/-- The copy of the symbolic point. -/
def symCp : List Instr := [.copyN cT1 iY, .copyN (cT1 + 1) (iY + 1), .copyN (cT1 + 2) (iY + 2)]

/-- The symbolic point of the top of `C₁` into `cT1`. -/
def symS : Stmt :=
  .seq (block [.constN iE 6, .constN iH 0]) (.seq (callSym (sw 20) iE iH iY) (block symCp))


/-- **The top of `C₁`**: a symbolic point in `cT1`; only the oracle bands, the allocator and
`sw 645 … 647`, `sw 705 … 709` change. -/
theorem symS_exec {P : Polygon} {W : ℕ} {c : Config} {J : Merge.Junction}
    (hw : WordsBounded W c) (hctx : ChainCtx P W c (sw 20) J.left)
    (hroom : c.nreg ALLOC + 31006 ≤ W) :
    ∃ c' k, Exec P W symS c c' k ∧ k ≤ 31011 ∧ Frame ioBands c c' k ∧
      (∃ s : SymPt, SymPtIn c' cT1 s ∧ s.Lt P.n ∧ s.eval (Qof P) = J.left.top) ∧
      ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → (r < sw 645 ∨ sw 647 < r) →
        (r < sw 705 ∨ sw 709 < r) → c'.nreg r = c.nreg r := by
  have hW6 : 6 ≤ W := by have := hctx.2.2.2.2.2; omega
  have e₁ := exec_regB (P := P) [.constN iE 6, .constN iH 0] hw
    (by simp only [okW, okWI]; exact ⟨hW6, by omega, trivial⟩)
  set c₁ : Config := { c with nreg := regB c.nmem [.constN iE 6, .constN iH 0] c.nreg } with hc₁
  have hw₁ := e₁.wb_right
  have q1 : ∀ r, r ≠ iE → r ≠ iH → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    simp only [hc₁, regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have qE : c₁.nreg iE = 6 := by
    simp only [hc₁, regB, regI]; rw [upd_other _ _ _ (by swoInit2), upd_same]
  have qH : c₁.nreg iH = 0 := by simp only [hc₁, regB, regI]; rw [upd_same]
  have hI₁ : IInv W c₁ c₁ := ⟨hw₁, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hctx₁ : ChainCtx P W c₁ (sw 20) J.left :=
    hctx.transport (q1 _ (by swoInit2) (by swoInit2)) (fun _ _ => rfl)
      (by rw [q1 _ (by swoInit2) (by swoInit2)])
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := q1 _ (by swoInit2)
    (by swoInit2)
  have hm1 := J.left.one_le
  have hpar : (chainModel J.left).param (Qof P) ⟨6, 0⟩ = 0 := rfl
  obtain ⟨c₂, k₂, e₂, hk₂, hI₂, hf₂, ⟨s, hs, hsl, hse⟩, hk2, -, -⟩ :=
    callSym_irs (P := P) (re := iE) (rh := iH) (o := iY) hI₁ hctx₁
      (by swoInit2) (by swoInit2) (by rw [qE])
      (by rw [qE]; omega) (by rw [qE, qH]; exact ⟨by rw [hpar], by rw [hpar]; norm_num,
        Nat.zero_le _⟩)
      (by rw [qE, qH]; exact ⟨fun _ => hpar, fun _ => rfl⟩) (by rw [hA₁]; exact hroom)
  rw [qE, qH] at hse
  have hpos : (chainModel J.left).pos (Qof P) ⟨6, 0⟩ = J.left.top := by
    show Chazelle.Chain.sidePt _ _ _ = _
    rw [hpar, Chazelle.Chain.sidePt_zero, walk_vtx_six]
  rw [hpos] at hse
  have hw₂ := e₂.wb_right
  have e₃ := exec_regB (P := P) symCp hw₂ (by
    simp only [symCp, okW, okWI]; exact ⟨trivial, trivial, trivial, trivial⟩)
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem symCp c₂.nreg } with hc₃
  have q3 : ∀ r, (r < sw 645 ∨ sw 647 < r) → c₃.nreg r = c₂.nreg r := fun r hr => by
    simp only [hc₃, symCp, regB, regI, cT1, sw] at hr ⊢
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  refine ⟨c₃, 2 + (k₂ + 3), .seq e₁ (.seq e₂ e₃), by omega, ?_, ⟨s, ?_, hsl, hse⟩, ?_⟩
  · have f₁ : Frame ioBands c c₁ 2 := frame_regs 2 (fun r hr => q1 r
      (fun h => hr (by rw [h]; exact sw_io (by swoInit2) (by swoInit2)))
      (fun h => hr (by rw [h]; exact sw_io (by swoInit2) (by swoInit2))))
      rfl rfl rfl rfl
    have f₂ := frame_of_irs hI₂ hf₂
    have f₃ : Frame ioBands c₂ c₃ 3 := frame_regs 3 (fun r hr => q3 r (by
      by_contra h
      exact hr (sw_io (by swoInit2) (by swoInit2)))) rfl rfl rfl rfl
    exact frame_ioB (frame_ioB (f₁.trans (f₂.trans f₃)))
  · refine symPtIn_transport hs ?_ ?_ ?_ <;>
    simp only [hc₃, symCp, regB, regI, cT1, iY, sw, Nat.reduceAdd] <;>
    simp only [upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  · intro r hr hrA h1 h2
    rw [q3 r h1, hk2 r hr (by swoInit2) hrA]
    exact q1 r (by swoInit2) (by swoInit2)

/-! ## The model descriptor of `C₁` -/


/-- The head: `MD₁ := ALLOC`, `CD₁ := ALLOC + 1`, `0` at `MD₁`. -/
def mdHead : List Instr := [.copyN MD₁ ALLOC, .addN CD₁ ALLOC K1, .storeN MD₁ K0]

/-- Copy word `k` of the descriptor at `sw 20` to `CD₁ + k`. -/
def mdCpW (k : ℕ) : List Instr := [.addN iA (sw 20) k, .loadN iV iA, .addN iA CD₁ k, .storeN iA iV]

/-- **The model descriptor of `C₁`.** -/
def md1S : Stmt :=
  .seq (block mdHead) (.seq (block (mdCpW K0)) (.seq (block (mdCpW K1)) (.seq (block (mdCpW K2))
    (.seq (block (mdCpW K3)) (.seq (block (mdCpW K4)) (.instr (.addN ALLOC ALLOC K6)))))))

/-- The state during the copy: `j` words copied. -/
def MdInv (c : Config) (A S j : ℕ) (c' : Config) : Prop :=
  c'.nreg MD₁ = A ∧ c'.nreg CD₁ = A + 1 ∧ c'.nmem A = 0 ∧
    (∀ i, i < j → c'.nmem (A + 1 + i) = c.nmem (S + i)) ∧
    (∀ a, a < A → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output

theorem mdCpW_step {P : Polygon} {W : ℕ} {c c₁ : Config} {A S j k : ℕ}
    (hw : WordsBounded W c₁) (hI : MdInv c A S j c₁) (hS : c.nreg (sw 20) = S)
    (hSA : S + 5 ≤ A) (hAW : A + 6 ≤ W) (hj : j < 5) (hk : c.nreg k = j)
    (hk1 : k ≠ MD₁) (hk2 : k ≠ CD₁) (hk3 : k ≠ iA) (hk4 : k ≠ iV) :
    ∃ c₂, Exec P W (block (mdCpW k)) c₁ c₂ 4 ∧ MdInv c A S (j + 1) c₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  have n20 : c₁.nreg (sw 20) = S := by
    rw [h6 _ (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2), hS]
  have nk : c₁.nreg k = j := Ρ h6 _ hk1 hk2 hk3 hk4, hk
  have e₁ := Exec.addN (P := P) hw iA (sw 20) k (by rw [n20, nk]; omega)
  have e₂ := Exec.loadN (P := P) e₁.wb_right iV iA
  have e₃ := Exec.addN (P := P) e₂.wb_right iA CD₁ k (by
    simp only
    rw [upd_other _ _ _ (by swoInit2), upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ hk4, upd_other _ _ _ hk3, h2, nk]; omega)
  have e₄ := Exec.storeN (P := P) e₃.wb_right iA iV
  refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
    (Exec.block_nil e₄.wb_right)))), ?_⟩
  have vA : ∀ v, upd (upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) iA
      ((upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) CD₁ +
        (upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) k) iA = A + 1 + j := by
    intro v
    rw [upd_same, upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ (by swoInit2), upd_other _ _ _ hk4,
      upd_other _ _ _ hk3, h2, nk]
  have vV : ∀ v, upd (upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) iA
      ((upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) CD₁ +
        (upd (upd c₁.nreg iA (c₁.nreg (sw 20) + c₁.nreg k)) iV v) k) iV = v := by
    intro v
    Ξ upd_other _ _ _ (by swoInit2), upd_same
  simp only
  Ξ vA, vV, upd_same, n20, nk
  have hsrc : c₁.nmem (S + j) = c.nmem (S + j) := h5 _ (⋄)
  refine ⟨?_, ?_, ?_, fun i hi => ?_, fun a ha => ?_, fun r r1 r2 r3 r4 => ?_, h7, h8, h9⟩ <;>
    simp only
  · rw [upd_other _ _ _ (by swoInit2), upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ (by swoInit2), h1]
  · rw [upd_other _ _ _ (by swoInit2), upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ (by swoInit2), h2]
  · Ξ upd_other _ _ _ (⋄), h3
  · rcases Nat.lt_or_ge i j with h | h
    · Ξ upd_other _ _ _ (⋄), h4 i h
    · Ξ show i = j by omega, upd_same, hsrc
  · Ξ upd_other _ _ _ (⋄), h5 a ha
  · Ξ upd_other _ _ _ r3, upd_other _ _ _ r4, upd_other _ _ _ r3, h6 r r1 r2 r3 r4


theorem mdHead_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (k0 : c.nreg K0 = 0) (k1 : c.nreg K1 = 1) (hW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c₁ k, Exec P W (block mdHead) c c₁ k ∧ k = 3 ∧
      MdInv c (c.nreg ALLOC) (c.nreg (sw 20)) 0 c₁ := by
  unfold mdHead MdInv
  ϴ' MD₁, CD₁, K0, K1, ALLOC, iA, iV, sw, Nat.reduceAdd at *
  exec_block
  · config_simp; rw [k1]; omega
  · refine ⟨rfl, by config_simp, by config_simp; rw [k1], by config_simp; rw [k0],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun a ha => ?_, fun r h1 h2 _ _ => ?_,
      rfl, rfl, rfl⟩
    · config_simp; Ξ upd_other _ _ _ (⋄)
    · config_simp; Ξ upd_other _ _ _ h2, upd_other _ _ _ h1


/-- **The model descriptor of `C₁`** at the allocator `A`: `0` at `A`, the five words of the
descriptor at `sw 20` at `A + 1 …`; `MD₁ = A`, `CD₁ = A + 1`, the allocator at `A + 6`. -/
theorem md1S_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hK : Consts c)
    (hS : c.nreg (sw 20) + 5 ≤ c.nreg ALLOC) (hW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W md1S c c' k ∧ k = 24 ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      c'.nreg MD₁ = c.nreg ALLOC ∧ c'.nreg CD₁ = c.nreg ALLOC + 1 ∧ c'.nmem (c.nreg ALLOC) = 0 ∧
      (∀ i, i < 5 → c'.nmem (c.nreg ALLOC + 1 + i) = c.nmem (c.nreg (sw 20) + i)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ ALLOC → r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  set A := c.nreg ALLOC with hA
  set S := c.nreg (sw 20) with hSd
  obtain ⟨c₁, kH, eH, hkH, I₁⟩ := mdHead_exec (P := P) hw k0 k1 hW
  have hSA := hS
  have nk : ∀ q, (q = K0 ∨ q = K1 ∨ q = K2 ∨ q = K3 ∨ q = K4) →
      q ≠ MD₁ ∧ q ≠ CD₁ ∧ q ≠ iA ∧ q ≠ iV := by
    rintro q (rfl | rfl | rfl | rfl | rfl) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> swoInit2
  obtain ⟨c₂, e₄, I₂⟩ := mdCpW_step (P := P) eH.wb_right I₁ rfl hSA (⋄) (⊛) k0
    (nk K0 (✓)).1 (nk K0 (✓)).2.1 (nk K0 (✓)).2.2.1 (nk K0 (✓)).2.2.2
  obtain ⟨c₃, e₅, I₃⟩ := mdCpW_step (P := P) e₄.wb_right I₂ rfl hSA (⋄) (⊛) k1
    (nk K1 (✓)).1 (nk K1 (✓)).2.1 (nk K1 (✓)).2.2.1 (nk K1 (✓)).2.2.2
  obtain ⟨c₄, e₆, I₄⟩ := mdCpW_step (P := P) e₅.wb_right I₃ rfl hSA (⋄) (⊛) k2
    (nk K2 (✓)).1 (nk K2 (✓)).2.1 (nk K2 (✓)).2.2.1 (nk K2 (✓)).2.2.2
  obtain ⟨c₅, e₇, I₅⟩ := mdCpW_step (P := P) e₆.wb_right I₄ rfl hSA (⋄) (⊛) k3
    (nk K3 (✓)).1 (nk K3 (✓)).2.1 (nk K3 (✓)).2.2.1 (nk K3 (✓)).2.2.2
  obtain ⟨c₆, e₈, I₆⟩ := mdCpW_step (P := P) e₇.wb_right I₅ rfl hSA (⋄) (⊛) k4
    (nk K4 (✓)).1 (nk K4 (✓)).2.1 (nk K4 (✓)).2.2.1 (nk K4 (✓)).2.2.2
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := I₆
  have gA : c₆.nreg ALLOC = A := g6 _ (by swoInit2)
    (by swoInit2) (by swoInit2) (by swoInit2)
  have g6' : c₆.nreg K6 = 6 := by
    rw [g6 _ (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2), k6]
  have e₉ := Exec.addN (P := P) e₈.wb_right ALLOC ALLOC K6 (by rw [gA, g6']; omega)
  refine ⟨_, _, .seq eH (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))), ⋄, ?_, ?_, ?_,
    g3, g4, g5, fun r h0 h1 h2 h3 h4 => ?_, g7, g8, g9⟩
  · simp only [upd_same]; Ξ gA, g6'
  · simp only; Ξ upd_other _ _ _ (by swoInit2), g1
  · simp only; Ξ upd_other _ _ _ (by swoInit2), g2
  · simp only; Ξ upd_other _ _ _ h0, g6 r h1 h2 h3 h4

end

end SweepEv

end Chazelle.Core
