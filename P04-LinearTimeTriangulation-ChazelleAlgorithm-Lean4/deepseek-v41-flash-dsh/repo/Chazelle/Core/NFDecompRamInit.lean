module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompProg

/-!
# Tree decomposition (WP-C), part 13: setup and initialisation on the RAM

* `setupS_exec`: the constants and field bases (`DRegs`), the allocator raised by `12`;
* `initS_exec`: every field entry cleared (sizes `1`), then the root visited, active, with the
  root slot; the allocator raised by `19 R`.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs

@[expose] public section

set_option maxHeartbeats 1000000

section setup

variable {P : Polygon} {W : ℕ}

/-- **The setup.** -/
theorem setupS_exec {c : Config} (hw : WordsBounded W c) {B K R CB RB LB : ℕ}
    (hB : c.nreg 60001 = B) (hK : c.nmem B = K) (hR : c.nmem (B + 2) = R)
    (hCB : c.nmem (B + 3) = CB) (hRB : c.nmem (B + 5) = RB) (hLB : c.nmem (B + 7) = LB)
    (hBW : B + 7 ≤ W) (hroom : c.nreg ALLOC + 12 + 20 * R + 3 * K ≤ W) :
    ∃ c' k, Exec P W setupS c c' k ∧ k = 38 ∧ DRegs (c.nreg ALLOC) R K CB RB LB c' ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nreg 60086 = c.nreg ALLOC + 12 + 19 * R + 3 * K ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ r, (r < 60010 ∨ (60032 ≤ r ∧ r < 60086) ∨ (60087 ≤ r ∧ r < 60100) ∨ 60120 ≤ r) →
        r ≠ ALLOC →
        c'.nreg r = c.nreg r) := by
  have hA : c.nreg 9999 = c.nreg ALLOC := rfl
  unfold setupS
  exec_block
  all_goals first
    | omega
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hB, hR, hK, hA]; omega)
    | skip
  have e3 : B + 2 + 1 = B + 3 := rfl
  have e5 : B + 2 + 1 + 2 = B + 5 := rfl
  have e7 : B + 2 + 1 + 2 + 2 = B + 7 := rfl
  refine ⟨⋄, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · config_simp
  · config_simp
  · config_simp
  · config_simp; rw [hB, hR]
  · config_simp; rw [hB, hK]
  · config_simp; rw [hB, e3, hCB]
  · config_simp; rw [hB, e5, hRB]
  · config_simp; rw [hB, e7, hLB]
  · config_simp; rfl
  · config_simp; rw [hB, hR]
  · intro f hf
    ϴ fb
    interval_cases f <;> config_simp <;>
      simp (config := { failIfUnchanged := false }) only [hB, hR, hA] <;> omega
  · unfold ALLOC; config_simp
  · config_simp; rw [hB, hR, hK, hA]; omega
  · intro r hr hra
    unfold ALLOC at hra
    config_simp
    simp (disch := omega) only [Machine.upd_other]

end setup

end

end Chazelle.Core.DecR

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs

@[expose] public section

theorem DRegs.b {A R K CB RB LB : ℕ} {c : Config} (h : DRegs A R K CB RB LB c) (f : ℕ)
    (hf : f < 20) : c.nreg (60100 + f) = A + 12 + f * R := h.base f hf

section alloc

variable {P : Polygon} {W : ℕ}

end alloc

section init

variable {P : Polygon} {W : ℕ}

theorem initBody_exec {A R K CB RB LB : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hi : c.nreg 60020 < R) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W initBody c c' k ∧ k = 9 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60020 = c.nreg 60020 + 1 ∧
      ∀ f j, f < 19 → j < R → fv c'.nmem A R f j =
        if j = c.nreg 60020 ∧ (f = 2 ∨ f = 7 ∨ f = 11 ∨ f = 12) then (if f = 7 then 1 else 0)
        else fv c.nmem A R f j := by
  have b2 := hR.b 2 (⊛); have b7 := hR.b 7 (⊛)
  have b11 := hR.b 11 (⊛); have b12 := hR.b 12 (⊛)
  simp only [Nat.reduceAdd] at b2 b7 b11 b12
  have z := hR.zero
  have o := hR.one
  unfold initBody
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b2, b7, b11, b12, o]; omega)
    | skip
  refine ⟨rfl, ?_, by config_simp; rw [o], fun f j hf hj => ?_⟩
  · refine ⟨fun r hr hra => ?_, rfl, rfl, rfl, fun a ha => ?_⟩
    · unfold Prot at hr
      config_simp
      simp (disch := omega) only [Machine.upd_other]
    · config_simp
      ϴ b2, b7, b11, b12
      simp (disch := omega) only [Machine.upd_other]
  · config_simp
    ϴ b2, b7, b11, b12, z, o
    Ξ fv_store hi hj, fv_store hi hj, fv_store hi hj, fv_store hi hj
    by_cases hji : j = c.nreg 60020
    · subst hji
      interval_cases f <;> simp
    · Θ hji

/-- The initialisation loop. -/
theorem initLoop_exec {A R K CB RB LB : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (h0 : c.nreg 60020 = 0) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 60020 60013 initBody) c c' k ∧ k ≤ 11 * R + 2 ∧
      WordsBounded W c' ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      ∀ j, j < R → fv c'.nmem A R 2 j = 0 ∧ fv c'.nmem A R 7 j = 1 ∧ fv c'.nmem A R 11 j = 0 ∧
        fv c'.nmem A R 12 j = 0 := by
  obtain ⟨c', k, e, ⟨hw', hf', hle, hv⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := initBody)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60020 ≤ R ∧
      ∀ j, j < d.nreg 60020 → fv d.nmem A R 2 j = 0 ∧ fv d.nmem A R 7 j = 1 ∧
        fv d.nmem A R 11 j = 0 ∧ fv d.nmem A R 12 j = 0)
    (fun d => 11 * (R - d.nreg 60020)) (fun d h => h.1)
    (fun d ⟨hwd, hfd, hled, hvd⟩ ht => by
      have hRd := hR.frame hfd
      rw [hRd.rR] at ht
      obtain ⟨d', k', e', rfl, hf', hi', hv'⟩ := initBody_exec (P := P) hwd hRd ht hroom
      refine ⟨d', 9, e', ⟨e'.wb_right, hfd.trans hf', ⋄, fun j hj => ?_⟩, ⋄⟩
      rw [hi'] at hj
      have hjR : j < R := ⋄
      rw [hv' 2 j (⊛) hjR, hv' 7 j (⊛) hjR, hv' 11 j (⊛) hjR,
        hv' 12 j (⊛) hjR]
      by_cases e : j = d.nreg 60020
      · Θ e
      · ϴ e, false_and, ite_false
        exact hvd j (⋄))
    ⟨hw, DFr.refl _ _ c, ⋄, fun j hj => ⋄⟩
  have hR' := hR.frame hf'
  rw [hR'.rR] at htest
  refine ⟨c', k, e, by rw [h0] at hk; omega, hw', hf', fun j hj => hv j (⋄)⟩

/-- **The initialisation.** -/
theorem initS_exec {A R K CB RB LB : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hR1 : 1 ≤ R) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k ≤ 11 * R + 11 ∧
      WordsBounded W c' ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      (∀ j, j < R → fv c'.nmem A R 2 j = (if j = 0 then 1 else 0) ∧ fv c'.nmem A R 7 j = 1 ∧
        fv c'.nmem A R 11 j = 0 ∧ fv c'.nmem A R 12 j = 0) ∧
      fv c'.nmem A R 1 0 = 0 ∧ fv c'.nmem A R 13 0 = 1 ∧ fv c'.nmem A R 15 0 = 2 := by
  unfold initS
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c
      { c with nreg := upd c.nreg 60020 0 } :=
    DFr.nreg _ fun r hr _ => by unfold Prot at hr; rw [Machine.upd_other _ _ _ (⋄)]
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hv2⟩ := initLoop_exec (P := P) hw1 (hR.frame hf1)
    (by config_simp) hroom
  have hR2 := (hR.frame hf1).frame hf2
  refine spec_seq ⟨c2, k2, e2, ?_⟩
  have b1 := hR2.b 1 (⊛); have b2 := hR2.b 2 (⊛)
  have b13 := hR2.b 13 (⊛); have b15 := hR2.b 15 (⊛)
  simp only [Nat.reduceAdd] at b1 b2 b13 b15
  have z := hR2.zero; have o := hR2.one; have t := hR2.two
  unfold rootInit
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, b2, b13, b15, z]; omega)
    | skip
  have hR0 : 0 < R := ⋄
  refine ⟨⋄, ‹_›, hf1.trans (hf2.trans ⟨fun r hr hra => ?_, rfl, rfl, rfl, fun a ha => ?_⟩),
    fun j hj => ?_, ?_, ?_, ?_⟩
  · unfold Prot at hr; config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp; simp only [b1, b2, b13, b15, z]
    simp (disch := omega) only [Machine.upd_other]
  · config_simp; simp only [b1, b2, b13, b15, z, o, t]
    obtain ⟨v1, v2, v3, v4⟩ := hv2 j hj
    ϴ fv_store hR0 hj
    by_cases e : j = 0
    · subst e; simp [v2, v3, v4]
    · Θ e, v1, v2, v3, v4
  all_goals
    config_simp
    ϴ b1, b2, b13, b15, z, o, t
    unfold fv
    ϴ Machine.upd_apply
    split_ifs <;> omega

end init

end

end Chazelle.Core.DecR
