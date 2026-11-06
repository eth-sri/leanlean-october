module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreDrvProg

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
  low : ∀ a, a < LB → c.nmem a = c₀.nmem a
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
  · grind [Machine.upd_same, Machine.upd_other, ALLOC]
  · grind [Machine.upd_same, Machine.upd_other, ALLOC]
  · omega_nf
  · grind [Machine.upd_same, Machine.upd_other, ALLOC]
  · ram_simp

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
    hal (by rw [hI.regs _ (by decide) (by decide) (by decide) (by decide), h20])
    (by rw [hI.regs _ (by decide) (by decide) (by decide) (by decide), h22])
    (by omega) (by omega) (by omega) (by omega)
  rw [hi] at r30
  refine ⟨c', k, e, ⟨e.wb_right, by omega, by omega, by omega,
    fun r a1 a2 a3 a4 => ?_, fun a ha => ?_, fun i' hi' j hj => ?_, by rw [rr, hI.rr],
    by rw [rm, hI.rm], by rw [ro, hI.out]⟩, hk, by rw [r30, hi]⟩
  · rw [R r a1 a2 a3 a4, hI.regs r a1 a2 a3 a4]
  · rw [hm, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), hI.low a ha]
  · rw [r30] at hi'
    have hs : ∀ j, j < 3 → c.nmem (CB + 5 * i + j) = c₀.nmem (CB + 5 * i + j) :=
      fun j hj => hI.low _ (by omega)
    rcases Nat.lt_or_ge i' i with hlt | hge
    · have hold := hI.copied i' (by omega) j hj
      rw [hm, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), hold]
    · have hii : i' = i := by omega
      subst hii
      have e0 := hs 0 (by omega)
      have e1 := hs 1 (by omega)
      
      simp only [add_zero] at e0
      rw [hm]
      interval_cases j
      · omega_nf
      · omega_nf
      · ram_simp

/-- **The copy loop.** -/
theorem copy_exec {P : Polygon} {W K CB LB A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h13 : c₀.nreg 80013 = K) (h30 : c₀.nreg 80030 = 0) (h31 : c₀.nreg 80031 = CB)
    (hA : c₀.nreg ALLOC = LB) (h20 : c₀.nreg 80020 = 1) (h22 : c₀.nreg 80022 = 3)
    (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB) (hW : LB + 3 * K ≤ W) (hWK : K + 1 ≤ W)
    (hA₀ : A₀ ≤ LB) :
    ∃ c' k, Exec P W copyS c₀ c' k ∧ k ≤ 15 * K + 2 ∧ c'.nreg ALLOC = LB + 3 * K ∧
      c'.nreg 80030 = K ∧
      (∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧
      (∀ a, a < LB → c'.nmem a = c₀.nmem a) ∧
      (∀ i, i < K → ∀ j, j < 3 → c'.nmem (LB + 3 * i + j) = c₀.nmem (CB + 5 * i + j)) ∧
      RF dBands A₀ c₀ c' k := by
  have I0 : CopyI W K CB LB c₀ c₀ := ⟨hw, by omega, by omega,
    by omega, fun _ _ _ _ _ => rfl, fun _ _ => rfl,
    fun i hi => by omega, rfl, rfl, rfl⟩
  obtain ⟨c', k, e, I', hx, RFl, hk⟩ := whileLtN_frame (P := P) (W := W) (a := 80030)
    (b := 80013) (body := copyBody) (B := dBands) (A₀ := A₀)
    (CopyI W K CB LB c₀) (fun c => K - c.nreg 80030) 13
    (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 80030 < K := by
        rw [I.regs 80013 (by decide) (by decide) (by decide) (by decide), h13] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := copyBody_step (P := P) I t h20 h22 hCB hW hWK
      refine ⟨c', k, e, I', ?_, by omega, by omega⟩
      -- the frame of one step
      have hb : ∀ r, bandOf r ∉ dBands → r ≠ 80030 ∧ r ≠ 80031 ∧ r ≠ 80033 := fun r hr =>
        ⟨fun h => hr (by rw [h, band8 (by norm_num) (by norm_num)]; exact mem_dBands_8),
         fun h => hr (by rw [h, band8 (by norm_num) (by norm_num)]; exact mem_dBands_8),
         fun h => hr (by rw [h, band8 (by norm_num) (by norm_num)]; exact mem_dBands_8)⟩
      refine ⟨fun r hr hra => ?_, fun r _ => by rw [I'.rr, I.rr], fun a ha => ?_,
        fun a _ => by rw [I'.rm, I.rm], by rw [I'.out, I.out], ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hb r hr
        rw [I'.regs r h1 h2 h3 hra, I.regs r h1 h2 h3 hra]
      · rw [I'.low a (by omega), I.low a (by omega)]
      · rw [I'.alloc, I.alloc]; omega
      · rw [I'.alloc, I.alloc, hi, hk]; omega) I0
  have hK' : c'.nreg 80030 = K := by
    rw [I'.regs 80013 (by decide) (by decide) (by decide) (by decide), h13] at hx
    have := I'.i_le; omega
  refine ⟨c', k, e, ?_, by rw [I'.alloc, hK'], hK', I'.regs, I'.low,
    fun i hi j hj => I'.copied i (by omega) j hj, RFl⟩
  omega

/-- The reservation-loop invariant. -/
structure ResI (W R A : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  j_le : c.nreg 80034 ≤ R
  alloc : c.nreg ALLOC = A + 3 * c.nreg 80034
  regs : ∀ r, r ≠ 80034 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 2000000 in
theorem resBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {a : ℕ}
    (hA : c.nreg ALLOC = a) (h20 : c.nreg 80020 = 1) (ha : a + 3 ≤ W)
    (hj : c.nreg 80034 + 1 ≤ W) :
    ∃ c' k, Exec P W resBody c c' k ∧ k = 4 ∧ c'.nreg ALLOC = a + 3 ∧
      c'.nreg 80034 = c.nreg 80034 + 1 ∧
      (∀ r, r ≠ 80034 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  
  unfold resBody
  exec_block
  all_goals (grind [Machine.upd_same, Machine.upd_other, ALLOC])

/-- **The reservation loop.** -/
theorem res_exec {P : Polygon} {W R A A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h14 : c₀.nreg 80014 = R) (h34 : c₀.nreg 80034 = 0) (hA : c₀.nreg ALLOC = A)
    (h20 : c₀.nreg 80020 = 1) (hW : A + 3 * R ≤ W) (hWR : R + 1 ≤ W) :
    ∃ c' k, Exec P W resS c₀ c' k ∧ k ≤ 6 * R + 2 ∧ c'.nreg ALLOC = A + 3 * R ∧
      (∀ r, r ≠ 80034 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      RF dBands A₀ c₀ c' k := by
  have I0 : ResI W R A c₀ c₀ := ⟨hw, by omega, by omega, fun _ _ _ => rfl, rfl,
    rfl, rfl, rfl⟩
  obtain ⟨c', k, e, I', hx, RFl, hk⟩ := whileLtN_frame (P := P) (W := W) (a := 80034)
    (b := 80014) (body := resBody) (B := dBands) (A₀ := A₀)
    (ResI W R A c₀) (fun c => R - c.nreg 80034) 4
    (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 80034 < R := by
        rw [I.regs 80014 (by decide) (by decide), h14] at ht; exact ht
      have c20 : c.nreg 80020 = 1 := by rw [I.regs _ (by decide) (by decide), h20]
      obtain ⟨c', k, e, hk, qa, qj, qr, qm, qrr, qrm, qo⟩ := resBody_exec (P := P) c I.wb
        I.alloc c20 (by omega) (by omega)
      have b34 : bandOf 80034 ∈ dBands := by
        rw [band8 (by norm_num) (by norm_num)]; exact mem_dBands_8
      refine ⟨c', k, e, ⟨e.wb_right, by omega, by omega,
        fun r a1 a2 => by rw [qr r a1 a2, I.regs r a1 a2], by rw [qm, I.mem],
        by rw [qrr, I.rr], by rw [qrm, I.rm], by rw [qo, I.out]⟩,
        ⟨fun r hr hra => qr r (fun h => hr (h ▸ b34)) hra, fun r _ => by rw [qrr],
          fun a _ => by rw [qm], fun a _ => by rw [qrm], qo, by rw [qa, I.alloc]; omega,
          by rw [qa, I.alloc, hk]; omega⟩,
        by omega, by omega⟩) I0
  have hR' : c'.nreg 80034 = R := by
    rw [I'.regs 80014 (by decide) (by decide), h14] at hx
    have := I'.j_le; omega
  refine ⟨c', k, e, ?_, by rw [I'.alloc, hR'], I'.regs, I'.mem, RFl⟩
  omega

end

end Restore

end Chazelle.Core
