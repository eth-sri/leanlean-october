module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBPLoop
public import Chazelle.Core.DownPhaseDrvBPieces
public import Chazelle.Core.DownPhaseDrvGLeaf

/-!
# Down-phase base (D9), RAM: the straight-line pieces of a region

* `rdS`: the region record (`p = r216031 = RB + 5 r + 2`): the number of ranges `r212034`
  (`mem[p - 2]` arcs, or `1` when `K = 0`) and the arc list `r212033 = LB + mem[p - 1]`;
* `host0`: the host `[.run 0 (n - 1)]` of the whole walk (`K = 0`), four fresh words;
* `mxS`: `MX := max MX NP`;
* `resPS`: the point array, `3 NP` fresh words;
* `incS`: the next region.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)

@[expose] public section

/-- The region record. -/
def rdS : Stmt :=
  .seq (block [.subN 212032 216031 212002, .loadN 212034 212032, .addN 212032 212032 212000,
    .loadN 212033 212032, .addN 212033 212033 216016])
    (.ifLtN 212001 212012 .skip (.instr (.constN 212034 1)))

/-- The host of the whole walk (`K = 0`). -/
def host0 : Stmt :=
  block [.copyN 212022 9999, .addN 9999 9999 212000, .addN 9999 9999 212000,
    .addN 9999 9999 212000, .addN 9999 9999 212000, .storeN 212022 212000,
    .addN 212032 212022 212000, .storeN 212032 212001, .addN 212032 212032 212000,
    .storeN 212032 212001, .addN 212032 212032 212000, .subN 212035 212010 212000,
    .storeN 212032 212035, .copyN 212016 212010, .copyN 212021 212000]

/-- `MX := max MX NP`. -/
def mxS : Stmt := .ifLtN 212018 212016 (.instr (.copyN 212018 212016)) .skip

/-- One step of the reservation of the point array. -/
def resPB : Stmt :=
  block [.addN 9999 9999 212000, .addN 9999 9999 212000, .addN 9999 9999 212000,
    .addN 212035 212035 212000]

/-- The reservation of the point array (`PA = r212015`, `3 NP` words). -/
def resPS : Stmt :=
  .seq (block [.copyN 212015 9999, .constN 212035 0]) (.whileLtN 212035 212016 resPB)

/-- The next region. -/
def incS : Stmt := block [.addN 212014 212014 212000, .addN 216031 216031 216006]

theorem host_len_le (n : ℕ) (H : Host) : H.length ≤ (H.pts n).length := by
  induction H with
  | nil => simp
  | cons it H ih =>
    have : 1 ≤ (it.pts n).length := by
      cases it with
      | run a l => simp [HostItem.pts]
      | pt x => simp [HostItem.pts]
    simp only [Host.pts, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The region record.** -/
theorem rdS_exec (c : Config) (hw : WordsBounded W c) {p LB K : ℕ}
    (h31 : c.nreg 216031 = p) (h16 : c.nreg 216016 = LB) (hK : c.nreg 212012 = K) (hp : 2 ≤ p)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hLB : LB + c.nmem (p - 1) ≤ W) :
    ∃ c' k, Exec P W rdS c c' k ∧ k ≤ 8 ∧
      c'.nreg 212034 = (if K = 0 then 1 else c.nmem (p - 2)) ∧
      c'.nreg 212033 = LB + c.nmem (p - 1) ∧
      FrameB (fun r => decide (212032 ≤ r ∧ r ≤ 212034)) c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v33, g⟩ : ∃ c₁ k₁, Exec P W (block [.subN 212032 216031 212002,
      .loadN 212034 212032, .addN 212032 212032 212000, .loadN 212033 212032,
      .addN 212033 212033 216016]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 212034 = c.nmem (p - 2) ∧
      c₁.nreg 212033 = LB + c.nmem (p - 1) ∧ c₁.nreg 212001 = 0 ∧ c₁.nreg 212012 = K := by
    have hp1 : p - 2 + 1 = p - 1 := by omega
    have hpW := hw.1 216031
    exec_block
    all_goals try (config_simp; simp only [h31, c2, c0, h16, hp1]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h31, c2, c0, h16, c1, hK, hp1]
    · ring
  have w₁ := e₁.wb_right
  by_cases h0 : K = 0
  · have e₂ := Exec.constN (P := P) w₁ 212034 1 (by have := hw.1 212000; omega)
    have ex : Exec P W rdS c _ (k₁ + (1 + 2)) := .seq e₁ (.ifLtN_false (by show ¬ c₁.nreg 212001 < c₁.nreg 212012; have := g.1; have := g.2; omega) e₂)
    refine ⟨_, _, ex, by omega, by simp [h0], ?_, exec_frameB ex (by decide)⟩
    simp only [Machine.upd_other _ _ _ (show (212033 : ℕ) ≠ 212034 by norm_num)]; exact v33
  · have ex : Exec P W rdS c c₁ (k₁ + (0 + 1)) :=
      .seq e₁ (.ifLtN_true (by show c₁.nreg 212001 < c₁.nreg 212012; have := g.1; have := g.2; omega) (.skip w₁))
    exact ⟨c₁, _, ex, by omega, by rw [ite_eq_right h0]; exact v34, v33, exec_frameB ex (by decide)⟩


/-- A frame of band `bDownDrv` from a register frame within the band and the allocator. -/
theorem frame21 {B : ℕ → Bool} {c c' : Config} {k : ℕ}
    (hB : ∀ r, B r = true → bandOf r = bDownDrv ∨ r = ALLOC) (hf : FrameM B c c')
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hrr : c'.rreg = c.rreg)
    (hA1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (hA2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bDownDrv} c c' k := by
  refine ⟨fun r hr hra => hf.1 r ?_, fun r _ => by rw [hrr], hm, fun a _ => by rw [hf.2.2.1],
    hf.2.2.2, hA1, hA2⟩
  cases h : B r
  · rfl
  · rcases hB r h with h' | h'
    · exact absurd (by rw [h']; exact Finset.mem_singleton_self _) hr
    · exact absurd h' hra

set_option maxHeartbeats 4000000 in
/-- **The host of the whole walk** (`K = 0`). -/
theorem host0_exec (c : Config) (hw : WordsBounded W c) {n : ℕ} (hn : c.nreg 212010 = n)
    (_hn1 : 1 ≤ n) (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0)
    (hA : c.nreg ALLOC + 4 ≤ W) :
    ∃ c' k, Exec P W host0 c c' k ∧ k = 15 ∧ c'.nreg 212022 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      HostAt c'.nmem (c.nreg ALLOC) [HostItem.run 0 (n - 1)] ∧
      c'.nreg 212016 = n ∧ c'.nreg 212021 = 1 ∧
      (∀ a, (a < c.nreg ALLOC ∨ c.nreg ALLOC + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameM (fun r => decide (r = 212016 ∨ r = 212021 ∨ r = 212022 ∨ r = 212032 ∨
        r = 212035 ∨ r = 9999)) c c' ∧ Frame {bDownDrv} c c' k := by
  set A := c.nreg ALLOC with hAd
  have hA' : c.nreg 9999 = A := rfl
  obtain ⟨c', k, ex, hk, v22, vA, m0, m1, m2, m3, v16, v21, hm, hrr⟩ : ∃ c' k,
      Exec P W host0 c c' k ∧ k = 15 ∧ c'.nreg 212022 = A ∧ c'.nreg 9999 = A + 4 ∧
      c'.nmem A = 1 ∧ c'.nmem (A + 1) = 0 ∧ c'.nmem (A + 2) = 0 ∧ c'.nmem (A + 3) = n - 1 ∧
      c'.nreg 212016 = n ∧ c'.nreg 212021 = 1 ∧
      (∀ a, (a < A ∨ A + 4 ≤ a) → c'.nmem a = c.nmem a) ∧ c'.rreg = c.rreg := by
    unfold host0
    exec_block
    all_goals try (config_simp; simp only [hA', c0, c1, hn]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hA', c0, c1, hn]
  have FM : FrameM (fun r => decide (r = 212016 ∨ r = 212021 ∨ r = 212022 ∨ r = 212032 ∨
      r = 212035 ∨ r = 9999)) c c' := BuildRam.exec_frameM ex (⌖)
  refine ⟨c', k, ex, hk, v22, vA, ⟨by rw [m0]; rfl, fun i hi => ?_⟩, v16, v21, hm, FM,
    frame21 (fun r h => ?_) FM (fun a ha => hm a (Or.inl ha)) hrr (by show A ≤ c'.nreg 9999; omega)
      (by show c'.nreg 9999 ≤ A + k; omega)⟩
  · simp only [List.length_singleton] at hi
    have : i = 0 := ⋄
    subst this
    exact ⟨m1, m2, m3⟩
  · simp only [decide_eq_true_eq] at h
    rcases h with h | h | h | h | h | h <;> subst h
    · left; decide
    · left; decide
    · left; decide
    · left; decide
    · left; decide
    · right; rfl

/-- **`MX := max MX NP`.** -/
theorem mxS_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mxS c c' k ∧ k ≤ 2 ∧
      c'.nreg 212018 = max (c.nreg 212018) (c.nreg 212016) ∧
      FrameB (fun r => decide (r = 212018)) c c' := by
  by_cases h : c.nreg 212018 < c.nreg 212016
  · have e := Exec.copyN (P := P) hw 212018 212016
    have ex : Exec P W mxS c _ _ := .ifLtN_true h e
    refine ⟨_, _, ex, le_refl _, ?_, exec_frameB ex (⌖)⟩
    simp only [Machine.upd_same]; omega
  · have ex : Exec P W mxS c c _ := .ifLtN_false h (.skip hw)
    exact ⟨c, _, ex, le_refl _, ⋄, FrameB.refl _ _⟩

set_option maxHeartbeats 4000000 in
/-- **The reservation of the point array.** -/
theorem resPS_exec (c : Config) (hw : WordsBounded W c) {NP : ℕ} (h16 : c.nreg 212016 = NP)
    (c0 : c.nreg 212000 = 1) (hA : c.nreg ALLOC + 3 * NP ≤ W) :
    ∃ c' k, Exec P W resPS c c' k ∧ k ≤ 6 * NP + 4 ∧ c'.nreg 212015 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * NP ∧
      FrameB (fun r => decide (r = 212015 ∨ r = 212035 ∨ r = 9999)) c c' ∧
      Frame {bDownDrv} c c' k := by
  set A := c.nreg ALLOC with hAd
  have hA' : c.nreg 9999 = A := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, v15, v35, g₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 212015 9999,
      .constN 212035 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212015 = A ∧ c₁.nreg 212035 = 0 ∧
      ∀ r, r ≠ 212015 → r ≠ 212035 → c₁.nreg r = c.nreg r := by
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, fun r a b => ?_⟩ <;> config_simp
      · exact hA'
      · Θ a, b
  have B₁ : FrameB (fun r => decide (r = 212015 ∨ r = 212035 ∨ r = 9999)) c c₁ :=
    exec_frameB e₁ (⌖)
  have F₁ : Frame {bDownDrv} c c₁ k₁ := frame21 (fun r h => by
      simp only [decide_eq_true_eq] at h
      rcases h with h | h | h <;> subst h
      · left; decide
      · left; decide
      · right; rfl) (FrameB.toM B₁) (fun a _ => Ρ B₁.2.2.1)
    (funext fun r => WalkKey.exec_rframe e₁ (B := fun _ => false) (⌖) r rfl)
    (by rw [g₁ _ (⌖) (by decide)]) (by rw [g₁ _ (by decide) (by decide)]; omega)
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 212035 = j ∧
    e.nreg 212016 = NP ∧ e.nreg 9999 = A + 3 * j ∧
    FrameB (fun r => decide (r = 212015 ∨ r = 212035 ∨ r = 9999)) c e ∧ e.nreg 212015 = A
  have I0 : Inv 0 c₁ := ⟨e₁.wb_right, v35, by rw [g₁ _ (⌖) (by decide), h16],
    by rw [g₁ _ (⌖) (by decide)]; simp [hA'], B₁, v15⟩
  obtain ⟨c', k, ex, ⟨w', j35, j16, jA, fr, j15⟩, hk, F⟩ := DrvG.forLoopF (P := P) (W := W)
    (ir := 212035) (nr := 212016) (body := resPB) (B := {bDownDrv}) Inv 4 NP
    (fun j e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun j e hj ⟨hw, h1, h2, h3, fr, h15⟩ => by
      have c0e : e.nreg 212000 = 1 := by rw [fr.1 _ (⌖), c0]
      obtain ⟨e', k', ex, hk', v35, vA⟩ : ∃ e' k', Exec P W resPB e e' k' ∧ k' = 4 ∧
          e'.nreg 212035 = j + 1 ∧ e'.nreg 9999 = A + 3 * (j + 1) := by
        unfold resPB
        exec_block
        all_goals try (config_simp; simp only [h1, h3, c0e]; omega)
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [h1, h3, c0e]; ring
      have fb : FrameB (fun r => decide (r = 212035 ∨ r = 9999)) e e' := exec_frameB ex (⌖)
      refine ⟨e', k', ex, ⟨ex.wb_right, v35, by rw [fb.1 _ (⌖), h2], vA,
        fr.trans (fbMono fb fun r h => by simp only [decide_eq_true_eq] at h ⊢; omega),
        by rw [fb.1 _ (⌖), h15]⟩,
        ⋄, frame21 (fun r h => ?_) (FrameB.toM fb) (fun a _ => by rw [fb.2.2.1])
          (funext fun r => WalkKey.exec_rframe ex (B := fun _ => false) (⌖) r rfl)
          (by show e.nreg 9999 ≤ e'.nreg 9999; omega)
          (by show e'.nreg 9999 ≤ e.nreg 9999 + k'; omega)⟩
      simp only [decide_eq_true_eq] at h
      rcases h with h | h <;> subst h
      · left; decide
      · right; rfl)
    I0 (Nat.zero_le _)
  have F' := F₁.trans F
  rw [Finset.union_self] at F'
  refine ⟨c', _, .seq e₁ ex, by rw [Nat.sub_zero] at hk; omega, j15, jA, fr, F'⟩

/-- **The next region.** -/
theorem incS_exec (c : Config) (hw : WordsBounded W c) {r p : ℕ} (h14 : c.nreg 212014 = r)
    (h31 : c.nreg 216031 = p) (c0 : c.nreg 212000 = 1) (c6 : c.nreg 216006 = 5)
    (hr : r + 1 ≤ W) (hp : p + 5 ≤ W) :
    ∃ c' k, Exec P W incS c c' k ∧ k = 2 ∧ c'.nreg 212014 = r + 1 ∧ c'.nreg 216031 = p + 5 ∧
      FrameB (fun q => decide (q = 212014 ∨ q = 216031)) c c' := by
  obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W incS c c' k ∧ k = 2 ∧
      c'.nreg 212014 = r + 1 ∧ c'.nreg 216031 = p + 5 := by
    unfold incS
    exec_block
    all_goals try (config_simp; simp only [h14, h31, c0, c6]; omega)
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [h14, h31, c0, c6]
  exact ⟨c', k, ex, hk, v1, v2, exec_frameB ex (⌖)⟩

end exec

end

end DrvB

end Chazelle.Core
