module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.RestoreReserve

/-!
# WP-E, part 7: the restoration driver — copying the chord list and reserving room

* `copy_exec`: the copy loop writes the `K` chord triples read at `CB + 5 i` to the allocator
  `LB, LB + 3, …` and raises the allocator to `LB + 3 K`;
* `res_exec`: the reservation loop raises the allocator by `3 R`.
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs

@[expose] public section

/-- The copy-loop invariant. -/
structure CopyI (W K CB LB : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 80030 ≤ K
  src : c.nreg 80031 = CB + 5 * c.nreg 80030
  alloc : c.nreg ALLOC = LB + 3 * c.nreg 80030
  regs : ∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : MemEqBelow LB c.nmem c₀.nmem
  copied : ∀ i, i < c.nreg 80030 → ∀ j, j < 3 → c.nmem (LB + 3 * i + j) = c₀.nmem (CB + 5 * i + j)
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 4000000 in
theorem copyBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {s a : ℕ}
    (h31 : c.nreg 80031 = s) (hA : c.nreg ALLOC = a) (h20 : c.nreg 80020 = 1)
    (h22 : c.nreg 80022 = 3) (hs : s + 5 ≤ W) (ha : a + 3 ≤ W) (hi : c.nreg 80030 + 1 ≤ W)
    (hsa : s + 2 < a) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 13 ∧ c'.nreg 80031 = s + 5 ∧ c'.nreg ALLOC = a + 3 ∧
      c'.nreg 80030 = c.nreg 80030 + 1 ∧
      c'.nmem = upd (upd (upd c.nmem a (c.nmem s)) (a + 1) (c.nmem (s + 1))) (a + 2)
        (c.nmem (s + 2)) ∧
      (∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold copyBody
  have hA' : c.nreg 9999 = a := hA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h31, hA', h20, h22, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h31, hA', h20, ALLOC]
  · have a4' := a4
    simp (disch := omega) only [Machine.upd_other]

set_option maxHeartbeats 2000000 in
theorem copyBody_step {P : Polygon} {W K CB LB : ℕ} {c₀ c : Config}
    (hI : CopyI W K CB LB c₀ c) (ht : c.nreg 80030 < K) (h20 : c₀.nreg 80020 = 1)
    (h22 : c₀.nreg 80022 = 3) (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB)
    (hW : LB + 3 * K ≤ W) (hWK : K + 1 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ CopyI W K CB LB c₀ c' ∧ k = 13 ∧
      c'.nreg 80030 = c.nreg 80030 + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, c.nreg 80030 = i := ⟨_, rfl⟩
  rw [hi] at ht
  have hCBi := hCB i ht
  have hsrc : c.nreg 80031 = CB + 5 * i := by rw [hI.src, hi]
  have hal : c.nreg ALLOC = LB + 3 * i := by rw [hI.alloc, hi]
  obtain ⟨c', k, e, hk, r31, rA, r30, hm, R, rr, rm, ro⟩ := copyBody_exec (P := P) c hI.wb hsrc
    hal (by frame_finish)
    (by frame_finish)
    (by omega) (by omega) (by omega) (by omega)
  rw [hi] at r30
  refine ⟨c', k, e, ⟨e.wb_right, by omega, by rw [r31, r30]; ring, by rw [rA, r30]; ring,
    fun r a1 a2 a3 a4 => ?_, fun a ha => ?_, fun i' hi' j hj => ?_, by rw [rr, hI.rr],
    by rw [rm, hI.rm], by rw [ro, hI.out]⟩, hk, by rw [r30, hi]⟩
  · frame_finish
  · ram_rw [hm, Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _, hI.low a ha]
  · rw [r30] at hi'
    have hs : ∀ j, j < 3 → c.nmem (CB + 5 * i + j) = c₀.nmem (CB + 5 * i + j) :=
      fun j hj => hI.low _ (by omega)
    rcases Nat.lt_or_ge i' i with hlt | hge
    · have hold := hI.copied i' (by omega) j hj
      ram_rw [hm, Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_other _ _, hold]
    · have hii : i' = i := by omega
      subst hii
      have e0 := hs 0 (by omega)
      have e1 := hs 1 (by omega)
      have e2 := hs 2 (by omega)
      simp only [add_zero] at e0
      rw [hm]
      interval_cases j
      · ram_simp [add_zero, e0] <;> reg_omega
      · simp_all <;> omega
      · rw [Machine.upd_same, e2]

/-- **The copy loop.** -/
theorem copy_exec {P : Polygon} {W K CB LB A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h13 : c₀.nreg 80013 = K) (h30 : c₀.nreg 80030 = 0) (h31 : c₀.nreg 80031 = CB)
    (hA : c₀.nreg ALLOC = LB) (h20 : c₀.nreg 80020 = 1) (h22 : c₀.nreg 80022 = 3)
    (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB) (hW : LB + 3 * K ≤ W) (hWK : K + 1 ≤ W)
    (hA₀ : A₀ ≤ LB) :
    ∃ c' k, Exec P W copyS c₀ c' k ∧ k ≤ 15 * K + 2 ∧ c'.nreg ALLOC = LB + 3 * K ∧
      c'.nreg 80030 = K ∧
      (∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧
      (MemEqBelow LB c'.nmem c₀.nmem) ∧
      (∀ i, i < K → ∀ j, j < 3 → c'.nmem (LB + 3 * i + j) = c₀.nmem (CB + 5 * i + j)) ∧
      RF dBands A₀ c₀ c' k := by
  have I0 : CopyI W K CB LB c₀ c₀ := ⟨hw, by omega, by rw [h31, h30]; ring,
    by rw [hA, h30]; ring, fun _ _ _ _ _ => rfl, fun _ _ => rfl,
    fun i hi => by rw [h30] at hi; omega, rfl, rfl, rfl⟩
  obtain ⟨c', k, e, I', hx, RFl, hk⟩ := whileLtN_frame (P := P) (W := W) (a := 80030)
    (b := 80013) (body := copyBody) (B := dBands) (A₀ := A₀)
    (CopyI W K CB LB c₀) (fun c => K - c.nreg 80030) 13
    (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 80030 < K := by
        rw [(ram_app% (I.regs 80013 ?_ ?_ ?_ ?_)), h13] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := copyBody_step (P := P) I t h20 h22 hCB hW hWK
      refine ⟨c', k, e, I', ?_, by omega, by omega⟩
      -- the frame of one step
      have hb : ∀ r, bandOf r ∉ dBands → r ≠ 80030 ∧ r ≠ 80031 ∧ r ≠ 80033 := fun r hr =>
        ⟨fun h => hr (by ram_rw [h, band8]; exact mem_dBands_8),
         fun h => hr (by ram_rw [h, band8]; exact mem_dBands_8),
         fun h => hr (by ram_rw [h, band8]; exact mem_dBands_8)⟩
      refine ⟨fun r hr hra => ?_, fun r _ => by rw [I'.rr, I.rr], fun a ha => ?_,
        fun a _ => by rw [I'.rm, I.rm], by rw [I'.out, I.out], ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hb r hr
        frame_finish
      · have h : A₀ ≤ LB := hA₀
        ram_rw [I'.low a, I.low a]
      · rw [I'.alloc, I.alloc]; omega
      · rw [I'.alloc, I.alloc, hi, hk]; omega) I0
  have hK' : c'.nreg 80030 = K := by
    rw [(ram_app% (I'.regs 80013 ?_ ?_ ?_ ?_)), h13] at hx
    have := I'.i_le; omega
  refine ⟨c', k, e, ?_, by rw [I'.alloc, hK'], hK', I'.regs, I'.low,
    fun i hi j hj => I'.copied i (by omega) j hj, RFl⟩
  rw [h30] at hk
  omega

/-- **The reservation loop.** -/
theorem res_exec {P : Polygon} {W R A A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h14 : c₀.nreg 80014 = R) (h34 : c₀.nreg 80034 = 0) (hA : c₀.nreg ALLOC = A)
    (h20 : c₀.nreg 80020 = 1) (hW : A + 3 * R ≤ W) (_hWR : R + 1 ≤ W) :
    ∃ c' k, Exec P W resS c₀ c' k ∧ k ≤ 6 * R + 2 ∧ c'.nreg ALLOC = A + 3 * R ∧
      (∀ r, r ≠ 80034 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      RF dBands A₀ c₀ c' k := by
  obtain ⟨d, k, e, hk, ha, _, hkeep, hf⟩ := (ram_app% (reserveLoop_exec (P := P) (m := 3)
    (B := dBands) (A₀ := A₀) ?_ ?_ ?_ ?_ ?_
    hw h14 h34 h20 (hA.symm ▸ hW)))
  refine ⟨d, k, e, hk, ha.trans (by rw [hA]), fun r hr hA => hkeep.nr r ?_, hkeep.nm rfl, hf⟩
  simp [reserveFoot, hr, hA]

end

end Restore

end Chazelle.Core
