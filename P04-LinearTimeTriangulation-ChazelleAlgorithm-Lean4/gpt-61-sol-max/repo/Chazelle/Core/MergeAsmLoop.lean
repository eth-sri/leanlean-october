module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.MergeAsmProg

/-!
# WP-F merge assembly, part 3: the descriptor copy and the maximum-degree loop

* `descS_exec`: a model descriptor at the allocator `A` (`0`, then the five words at `bw`), the
  allocator bumped by `6`, the memory below `A` unchanged;
* `mdInit_exec`, `mdLoop_exec`: the loop leaves in `100032` an upper bound of the values at
  `base + 5 r` (`r < R`) that is itself at most any common bound `Cap` of them.
-/

namespace Chazelle.Core

namespace MergeAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The descriptor copy -/

set_option maxHeartbeats 4000000 in
theorem descS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {A bw : ℕ}
    (hA : c.nreg ALLOC = A) (hbw : c.nreg 100002 = bw) (hbA : bw + 5 ≤ A) (hAW : A + 6 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 27 ∧ c'.nreg 100010 = A ∧ c'.nreg ALLOC = A + 6 ∧
      c'.nreg 100020 = 1 ∧ c'.nreg 100021 = 5 ∧
      c'.nmem A = 0 ∧ (∀ j, j < 5 → c'.nmem (A + 1 + j) = c.nmem (bw + j)) ∧
      (∀ a, (a < A ∨ A + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 100010 ∨ 100022 ≤ r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descS
  have hA' : c.nreg 9999 = A := hA
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', hbw, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl⟩
  · omega_nf
  · omega_nf
  · omega_nf
  · omega_nf
  · grind [Machine.upd_same, Machine.upd_other, ALLOC]
  · interval_cases j <;>
      grind [Machine.upd_same, Machine.upd_other, ALLOC, add_zero]
  · grind [Machine.upd_other, ALLOC]
  · have h2' : r ≠ 9999 := h2
    simp (disch := omega) only [Machine.upd_other]

/-! ## The maximum-degree loop -/

section
variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
include hw
theorem mdInit_exec {H : ℕ}
    (hH : rd c bFuse 7 = H) (hHW : H + 5 ≤ W) (hbW : c.nmem (H + 5) + 2 ≤ W) :
    ∃ c' k, Exec P W mdInit c c' k ∧ k = 10 ∧ c'.nreg 100034 = c.nmem (H + 2) ∧
      c'.nreg 100031 = c.nmem (H + 5) + 2 ∧ c'.nreg 100030 = 0 ∧ c'.nreg 100032 = 0 ∧
      c'.nmem = c.nmem ∧ (∀ r, r < 100030 → c'.nreg r = c.nreg r) ∧
      FrameB (inBand bMerge) c c' := by
  have hH' : c.nreg 70007 = H := hH
  obtain ⟨c', k, e, hk, q⟩ : ∃ c' k, Exec P W mdInit c c' k ∧ k = 10 ∧
      (c'.nreg 100034 = c.nmem (H + 2) ∧ c'.nreg 100031 = c.nmem (H + 5) + 2 ∧
      c'.nreg 100030 = 0 ∧ c'.nreg 100032 = 0 ∧ c'.nmem = c.nmem ∧
      (∀ r, r < 100030 → c'.nreg r = c.nreg r)) := by
    unfold mdInit
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hH']; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun r hr => ?_⟩
    · simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hH']
    · simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hH']
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
    · simp (disch := omega) only [Machine.upd_same]
    · simp (disch := omega) only [Machine.upd_other]
  exact ⟨c', k, e, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2,
    exec_frameB e wr_mdInit⟩

/-- One step of the maximum-degree loop. -/
theorem mdBody_exec
    (h20 : c.nreg 100020 = 1) (h21 : c.nreg 100021 = 5) (hp : c.nreg 100031 + 5 ≤ W)
    (hi : c.nreg 100030 + 1 ≤ W) :
    ∃ c' k, Exec P W mdBody c c' k ∧ k ≤ 5 ∧
      c'.nreg 100032 = max (c.nreg 100032) (c.nmem (c.nreg 100031)) ∧
      c'.nreg 100031 = c.nreg 100031 + 5 ∧ c'.nreg 100030 = c.nreg 100030 + 1 ∧
      c'.nmem = c.nmem ∧
      (∀ r, r ≠ 100030 → r ≠ 100031 → r ≠ 100032 → r ≠ 100033 → c'.nreg r = c.nreg r) := by
  have e₁ := Exec.loadN (P := P) hw 100033 100031
  set c₁ : Config := { c with nreg := upd c.nreg 100033 (c.nmem (c.nreg 100031)) } with hc₁
  have hw₁ : WordsBounded W c₁ := e₁.wb_right
  
  
  -- the maximum
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, q₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 100032 100033
      (block [.copyN 100032 100033]) .skip) c₁ c₂ k₂ ∧ k₂ ≤ 2 ∧
      c₂.nreg 100032 = max (c.nreg 100032) (c.nmem (c.nreg 100031)) ∧
      (∀ r, r ≠ 100032 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
    by_cases hlt : c₁.nreg 100032 < c₁.nreg 100033
    · have e := Exec.copyN (P := P) hw₁ 100032 100033
      refine ⟨_, _, .ifLtN_true hlt (.seq e (.skip e.wb_right)), by omega, ?_, fun r hr => ?_, rfl⟩
      all_goals (simp_all [upd_same] <;> omega_nf)
    · refine ⟨_, _, .ifLtN_false hlt (.skip hw₁), le_rfl, ?_, fun r _ => rfl, rfl⟩
      simp_all
  obtain ⟨q₂, m₂⟩ := q₂
  have hw₂ := e₂.wb_right
  have e₃ := Exec.addN (P := P) hw₂ 100031 100031 100021 (by
    simp_all)
  have e₄ := Exec.addN (P := P) e₃.wb_right 100030 100030 100020 (by
    simp_all)
  have ex : Exec P W mdBody c _ ((1 + 0) + (k₂ + (1 + (1 + 0)))) :=
    .seq (.seq e₁ (.skip hw₁)) (.seq e₂ (.seq e₃ (.seq e₄ (.skip e₄.wb_right))))
  refine ⟨_, _, ex, by omega, ?_, ?_, ?_, ?_, fun r a b d f => ?_⟩
  · simp only [upd_other _ _ _ (show (100032 : ℕ) ≠ 100030 by decide),
      upd_other _ _ _ (show (100032 : ℕ) ≠ 100031 by decide)]
    exact v₂
  all_goals (ram_simp )


end

/-- **The maximum-degree loop.** -/
theorem mdLoop_exec {P : Polygon} {W R base Cap : ℕ} {L : ℕ → ℕ}
    (hWb : base + 5 * R ≤ W) (hRW : R + 1 ≤ W) (hCap : ∀ r, r < R → L r ≤ Cap) :
    ∀ (n : ℕ) (c : Config), WordsBounded W c → c.nreg 100020 = 1 → c.nreg 100021 = 5 →
      c.nreg 100034 = R → (∀ r, r < R → c.nmem (base + 5 * r) = L r) →
      c.nreg 100030 + n = R → c.nreg 100031 = base + 5 * c.nreg 100030 →
      c.nreg 100032 ≤ Cap → (∀ r, r < c.nreg 100030 → L r ≤ c.nreg 100032) →
      ∃ c' k, Exec P W mdLoop c c' k ∧ k ≤ 7 * n + 2 ∧ (∀ r, r < R → L r ≤ c'.nreg 100032) ∧
        c'.nreg 100032 ≤ Cap ∧ c'.nmem = c.nmem ∧
        (∀ r, r ≠ 100030 → r ≠ 100031 → r ≠ 100032 → r ≠ 100033 → c'.nreg r = c.nreg r)
  | 0, c, hw, _, _, h34, _, hn, _, hc, hle => by
    refine ⟨c, 2, .whileLtN_false (by omega) hw, by omega,
      fun r hr => hle r (by omega), hc, rfl, fun _ _ _ _ _ => rfl⟩
  | n + 1, c, hw, h20, h21, h34, hL, hn, hp, hc, hle => by
    have hi : c.nreg 100030 < R := by omega
    obtain ⟨c₁, k₁, e₁, hk₁, v32, v31, v30, m₁, q₁⟩ := mdBody_exec (P := P) c hw h20 h21
      (by omega) (by omega)
    have hLi : c.nmem (c.nreg 100031) = L (c.nreg 100030) := by ram_grind
    obtain ⟨c', k₂, e₂, hk₂, hall, hcap, m₂, q₂⟩ := mdLoop_exec hWb hRW hCap n c₁ e₁.wb_right
      (by ram_grind)
      (by ram_grind)
      (by ram_grind)
      (fun r hr => by ram_grind) (by omega)
      (by omega)
      (by ram_grind)
      (fun r hr => by
        ram_grind)
    refine ⟨c', _, .whileLtN_true (by omega) e₁ e₂, by omega, hall, hcap,
      by rw [m₂, m₁], fun r a b d f => by ram_grind⟩

end

end MergeAsm

end Chazelle.Core
