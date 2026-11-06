module

public import Chazelle.Core.NFDecompGlue

/-!
# Tree decomposition (WP-C), part 22: writing the output on the RAM

* `fcS_exec`: the node table (`par, lo, hi` of chord `k` at `DB + 3 k`, `DB = A + 12 + 19 R`) is
  copied from the fields `16, 17, 18`;
* `hdrS_exec`: the header of the output normal form at `A`.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

/-- A store instruction followed by more code. -/
macro "seq_store" : tactic =>
  `(tactic| (refine spec_seq (spec_instr (Machine.Exec.storeN ‹WordsBounded _ _› _ _)
    fun _hw => ?_); config_flatten_at _hw; spec_flatten))

/-- An addition followed by more code (side condition moved last). -/
macro "seq_addN" : tactic =>
  `(tactic| (refine spec_seq (spec_instr (Machine.Exec.addN ‹WordsBounded _ _› _ _ _ ?_)
    fun _hw => ?_); rotate_left; config_flatten_at _hw; spec_flatten))

/-- Discharge the arithmetic side conditions left by the block steps. -/
macro "side_tac" : tactic =>
  `(tactic| all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [*]; omega)
    | skip)

section fc

variable {P : Polygon} {W : ℕ} {A R K CB RB LB : ℕ}

/-- One step of the node-table copy. -/
theorem fcBody_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R + 3 * K ≤ W) {j : ℕ} (h20 : c.nreg 60020 = j) (hj : j < K)
    (hKR : K < R) :
    ∃ c' k, Exec P W fcBody c c' k ∧ k = 15 ∧ DFr (A + 12) (A + 12 + 19 * R + 3 * K) c c' ∧
      c'.nreg 60020 = j + 1 ∧
      c'.nmem = upd (upd (upd c.nmem (A + 12 + 19 * R + 3 * j) (fv c.nmem A R 16 j))
        (A + 12 + 19 * R + 3 * j + 1) (fv c.nmem A R 17 j))
        (A + 12 + 19 * R + 3 * j + 2) (fv c.nmem A R 18 j) := by
  have b16 := hR.b 16 (by norm_num); have b17 := hR.b 17 (by norm_num)
  have b18 := hR.b 18 (by norm_num); have b19 := hR.b 19 (by norm_num)
  simp only [Nat.reduceAdd] at b16 b17 b18 b19
  have o := hR.one
  have h16 : 16 * R + j < 19 * R := by omega
  have hjR : 3 * j + 3 ≤ 3 * K := by omega
  unfold fcBody ldF fb
  simp only [Nat.reduceAdd]
  refine spec_seq ?_
  exec_block
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  seq_addN
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  seq_addN
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  refine spec_instr (Machine.Exec.addN ‹WordsBounded _ _› _ _ _ ?_) fun _hw => ?_
  rotate_left
  side_tac
  refine ⟨by norm_num, ⟨fun r hr hra => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_⟩
  · unfold Prot at hr
    config_simp
    simp (disch := omega) only [Machine.upd_other]
  · config_simp
    simp only [b16, b17, b18, b19, h20, o]
    simp (disch := omega) only [Machine.upd_other]
  · config_simp; rw [h20, o]
  · config_simp
    simp only [b16, b17, b18, b19, h20, o]
    simp (disch := omega) only [Machine.upd_other]
    unfold fv
    funext a
    simp only [Machine.upd_apply]
    split_ifs <;> first | rfl | omega

/-- The node table value at address `a` (relative to `DB = A + 12 + 19 R`). -/
def ntv (m : ℕ → ℕ) (A R a : ℕ) : ℕ :=
  fv m A R (16 + (a - (A + 12 + 19 * R)) % 3) ((a - (A + 12 + 19 * R)) / 3)

/-- **The node-table copy.** -/
theorem fcS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R + 3 * K ≤ W) (hKR : K < R) :
    ∃ c' k, Exec P W fcS c c' k ∧ k ≤ 17 * K + 3 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R + 3 * K) c c' ∧
      ∀ a, c'.nmem a = if A + 12 + 19 * R ≤ a ∧ a < A + 12 + 19 * R + 3 * K then
        ntv c.nmem A R a else c.nmem a := by
  unfold fcS
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  set c1 := { c with nreg := upd c.nreg 60020 0 } with hc1
  have hf1 : DFr (A + 12) (A + 12 + 19 * R + 3 * K) c c1 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr; rw [Machine.upd_other _ _ _ (by omega)]
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60014) (body := fcBody)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R + 3 * K) c d ∧ d.nreg 60020 ≤ K ∧
      ∀ a, d.nmem a = if A + 12 + 19 * R ≤ a ∧ a < A + 12 + 19 * R + 3 * d.nreg 60020 then
        ntv c.nmem A R a else c.nmem a)
    (fun d => 17 * (K - d.nreg 60020)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      have hRd := hR.frame hfd
      rw [hRd.rK] at htest
      obtain ⟨j, hjdef⟩ : ∃ j, d.nreg 60020 = j := ⟨_, rfl⟩
      rw [hjdef] at htest hjd hvd
      obtain ⟨d', k', e', rfl, hf'', h20', hm'⟩ := fcBody_exec (P := P) hwd hRd hAW hjdef htest hKR
      have hfv : ∀ f, f < 19 → fv d.nmem A R f j = fv c.nmem A R f j := fun f hf => by
        have : f * R ≤ 18 * R := Nat.mul_le_mul_right _ (by omega)
        unfold fv; rw [hvd, ite_eq_right (by omega)]
      refine ⟨d', 15, e', ⟨e'.wb_right, hfd.trans hf'', by omega, fun a => ?_⟩, by omega⟩
      rw [hm', h20', hfv 16 (by norm_num), hfv 17 (by norm_num), hfv 18 (by norm_num)]
      simp only [Machine.upd_apply]
      rw [hvd a]
      unfold ntv
      split_ifs <;> first
        | rfl
        | omega
        | (· simp only [show (a - (A + 12 + 19 * R)) % 3 = 0 by omega,
            show (a - (A + 12 + 19 * R)) / 3 = j by omega, Nat.add_zero])
        | (· simp only [show (a - (A + 12 + 19 * R)) % 3 = 1 by omega,
            show (a - (A + 12 + 19 * R)) / 3 = j by omega, Nat.reduceAdd])
        | (· simp only [show (a - (A + 12 + 19 * R)) % 3 = 2 by omega,
            show (a - (A + 12 + 19 * R)) / 3 = j by omega, Nat.reduceAdd]))
    ⟨hw1, hf1, by simp only [hc1]; config_simp; omega, fun a => by
      simp only [hc1]; config_simp; rw [ite_eq_right (by omega)]⟩
  have hR' := hR.frame hf'
  rw [hR'.rK] at htest
  have hjK : c'.nreg 60020 = K := by omega
  have h0 : c1.nreg 60020 = 0 := by simp only [hc1]; config_simp
  rw [h0] at hk
  refine ⟨c', k, e, by omega, hw', hf', fun a => ?_⟩
  rw [hv' a, hjK]

end fc

section hdr

variable {P : Polygon} {W : ℕ} {A R K CB RB LB : ℕ}

/-- **The header** of the output at `A`. -/
theorem hdrS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c) {B : ℕ}
    (hB : c.nreg 60001 = B) (hBA : B + 9 < A) (hAW : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W hdrS c c' k ∧ k ≤ 40 ∧ c'.nreg 60003 = A ∧
      (∀ r, r ≠ 60030 → r ≠ 60031 → r ≠ 60085 → r ≠ 60003 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nmem A = K ∧ c'.nmem (A + 1) = c.nmem (B + 1) ∧ c'.nmem (A + 2) = R ∧
      c'.nmem (A + 3) = c.nmem (B + 3) ∧ c'.nmem (A + 4) = c.nmem (B + 4) ∧
      c'.nmem (A + 5) = c.nmem (B + 5) ∧ c'.nmem (A + 6) = c.nmem (B + 6) ∧
      c'.nmem (A + 7) = c.nmem (B + 7) ∧ c'.nmem (A + 8) = A + 12 + 19 * R ∧
      c'.nmem (A + 9) = c.nreg 60024 ∧ c'.nmem (A + 10) = A + 12 ∧ c'.nmem (A + 11) = K ∧
      ∀ a, (a < A ∨ A + 12 ≤ a) → c'.nmem a = c.nmem a := by
  have b0 := hR.b 0 (by norm_num); have b19 := hR.b 19 (by norm_num)
  simp only [Nat.reduceAdd, Nat.zero_mul, Nat.add_zero] at b0 b19
  have o := hR.one; have t := hR.two; have rA := hR.rA; have rK := hR.rK; have rR := hR.rR
  unfold hdrS
  exec_block
  side_tac
  refine ⟨by omega, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, ?_⟩
  · config_simp; exact rA
  · config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp
    simp only [b0, b19, o, t, rA, rK, rR, hB]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩ <;>
      simp (disch := omega) only [Machine.upd_other, Machine.upd_same]

end hdr

end

end Chazelle.Core.DecR
