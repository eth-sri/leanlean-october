module

public import Chazelle.Core.NFDecompRamP1

/-!
# Tree decomposition (WP-C), part 16: the top pass on the RAM

`p2S_exec`: the top pass leaves in fields `8`, `9`, `10` the fold of `p2` over all `R` search
positions (tops, best candidates and their values, `p2_full`).
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

/-- Close a `Same` goal for an explicit register update. -/
macro "same_tac" : tactic =>
  `(tactic| exact ⟨fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      config_simp
      simp (disch := omega) only [Machine.upd_other], rfl, rfl, rfl⟩)

section p2ram

variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}

theorem ite_lt_min (a b : ℕ) : (if a < b then a else b) = min a b := by
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (by omega)).symm

/-- The top branch: `top r := r`, `best r := r`, `bestv r := 0`. -/
theorem topBr_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) :
    ∃ c' k, Exec P W topBr c c' k ∧ k = 6 ∧ Same [60030] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 8 ∧ u = r then r else if f = 9 ∧ u = r then r else if f = 10 ∧ u = r then 0
        else fv c.nmem A R f u := by
  have b8 := hR.b 8 (by norm_num); have b9 := hR.b 9 (by norm_num); have b10 := hR.b 10 (by norm_num)
  simp only [Nat.reduceAdd] at b8 b9 b10
  have z := hR.zero
  unfold topBr
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b8, b9, b10, h40]; omega)
    | skip
  refine ⟨rfl, ?_, fun a ha => ?_, fun f u hf hu => ?_⟩
  · same_tac
  · config_simp; simp only [b8, b9, b10, h40]
    rw [fv_store_out (by norm_num) hr ha, fv_store_out (by norm_num) hr ha,
      fv_store_out (by norm_num) hr ha]
  · config_simp; simp only [b8, b9, b10, h40, z]
    rw [fv_store hr hu, fv_store hr hu, fv_store hr hu]
    by_cases hur : u = r
    · subst hur; interval_cases f <;> simp
    · simp [hur]

/-- The non-top branch: the top of `r` is its parent's; the candidate of that top may improve. -/
theorem ntBr_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r q t : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) (hq : q < R)
    (ht : t < R) (hprg : fv c.nmem A R 3 r = q) (htop : fv c.nmem A R 8 q = t) :
    ∃ c' k, Exec P W ntBr c c' k ∧ k ≤ 21 ∧
      Same [60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 8 ∧ u = r then t
        else if fv c.nmem A R 10 t < min (fv c.nmem A R 7 r) (fv c.nmem A R 7 t - fv c.nmem A R 7 r)
          ∧ f = 10 ∧ u = t then min (fv c.nmem A R 7 r) (fv c.nmem A R 7 t - fv c.nmem A R 7 r)
        else if fv c.nmem A R 10 t < min (fv c.nmem A R 7 r) (fv c.nmem A R 7 t - fv c.nmem A R 7 r)
          ∧ f = 9 ∧ u = t then r
        else fv c.nmem A R f u := by
  have b3 := hR.b 3 (by norm_num); have b7 := hR.b 7 (by norm_num); have b8 := hR.b 8 (by norm_num)
  have b9 := hR.b 9 (by norm_num); have b10 := hR.b 10 (by norm_num)
  simp only [Nat.reduceAdd] at b3 b7 b8 b9 b10
  have hq' : c.nmem (A + 12 + 3 * R + r) = q := hprg
  have ht' : c.nmem (A + 12 + 8 * R + q) = t := htop
  set a := fv c.nmem A R 7 r with hadef
  set sT := fv c.nmem A R 7 t with hsdef
  set bv := fv c.nmem A R 10 t with hbvdef
  set v := min a (sT - a) with hvdef
  -- the first block
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [
      .addN 60030 60103 60040, .loadN 60043 60030,
      .addN 60030 60108 60043, .loadN 60046 60030,
      .addN 60030 60108 60040, .storeN 60030 60046,
      .addN 60030 60107 60040, .loadN 60044 60030,
      .addN 60030 60107 60046, .loadN 60047 60030,
      .subN 60048 60047 60044]) c c1 k1 ∧ k1 = 11 ∧
      c1 = { c with
        nreg := upd (upd (upd (upd (upd (upd c.nreg 60030 (A + 12 + 7 * R + t)) 60043 q) 60046 t)
          60044 a) 60047 sT) 60048 (sT - a)
        nmem := upd c.nmem (A + 12 + 8 * R + r) t } := by
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [b3, b7, b8, h40, hq', ht']
         omega)
      | skip
    refine ⟨rfl, ?_⟩
    simp only [b3, b7, b8, h40, hq', ht']
    have e1 : A + 12 + 7 * R + r ≠ A + 12 + 8 * R + r := by omega
    have e2 : A + 12 + 7 * R + t ≠ A + 12 + 8 * R + r := by omega
    rw [Machine.upd_other _ _ _ e1, Machine.upd_other _ _ _ e2]
    congr 1
    funext x
    simp only [Machine.upd_apply]
    split_ifs <;> first | rfl | omega
  have hw1 := e1.wb_right
  have s1 : Same [60030, 60043, 60046, 60044, 60047, 60048] c c1 := by rw [hc1]; same_tac
  have hR1 : DRegs A R K CB RB LB c1 := hR.of_same s1 (by simp [Prot])
  have m1 : c1.nmem = upd c.nmem (A + 12 + 8 * R + r) t := by rw [hc1]
  have r44 : c1.nreg 60044 = a := by rw [hc1]; config_simp
  have r48 : c1.nreg 60048 = sT - a := by rw [hc1]; config_simp
  have r46 : c1.nreg 60046 = t := by rw [hc1]; config_simp
  unfold ntBr
  refine spec_seq ⟨c1, 11, e1, ?_⟩
  -- the value
  obtain ⟨c2, k2, e2, hk2, hc2⟩ : ∃ c2 k2, Exec P W (.ifLtN 60044 60048 (.instr (.copyN 60049 60044))
      (.instr (.copyN 60049 60048))) c1 c2 k2 ∧ k2 ≤ 3 ∧
      c2 = { c1 with nreg := upd c1.nreg 60049 v } := by
    by_cases hlt : a < sT - a
    · refine spec_ifLtN_true (by rw [r44, r48]; exact hlt)
        (spec_instr (Exec.copyN hw1 _ _) fun _ => ⟨by omega, ?_⟩)
      rw [r44, hvdef, ← ite_lt_min, ite_eq_left hlt]
    · refine spec_ifLtN_false (by rw [r44, r48]; exact hlt)
        (spec_instr (Exec.copyN hw1 _ _) fun _ => ⟨by omega, ?_⟩)
      rw [r48, hvdef, ← ite_lt_min, ite_eq_right hlt]
  subst hc2
  have hw2 := e2.wb_right
  have b10c := hR1.b 10 (by norm_num)
  simp only [Nat.reduceAdd] at b10c
  obtain ⟨c3, k3, e3, rfl, m3, s3, r50⟩ := ldF_rel (P := P) hw2 60050 10 60046
    (by simp only [show fb 10 = 60110 from rfl]; config_simp; rw [b10c, r46]; omega)
  have hbv : c3.nreg 60050 = bv := by
    rw [r50]; simp only [show fb 10 = 60110 from rfl]; config_simp
    rw [b10c, r46, m1, Machine.upd_other _ _ _ (by omega)]
    rfl
  have r49 : c3.nreg 60049 = v := by rw [s3.1 _ (by simp)]; config_simp
  refine spec_seq ⟨_, k2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩
  have hw3 := e3.wb_right
  have hR3 : DRegs A R K CB RB LB c3 := by
    refine (hR1.of_same (l := [60049]) (Same.upd1 (by simp)) (by simp [Prot])).of_same s3
      (by simp [Prot])
  have m3' : c3.nmem = upd c.nmem (A + 12 + 8 * R + r) t := by rw [m3]; exact m1
  have s13 : Same [60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c c3 :=
    ((s1.mono (by simp)).trans ((Same.upd1 (l := [60030, 60043, 60046, 60044, 60047, 60048, 60049,
      60050]) (by simp)))).trans (s3.mono (by simp))
  by_cases hup : bv < v
  · refine spec_ifLtN_true (by rw [hbv, r49]; exact hup) ?_
    have b9' := hR3.b 9 (by norm_num); have b10' := hR3.b 10 (by norm_num)
    simp only [Nat.reduceAdd] at b9' b10'
    have r46' : c3.nreg 60046 = t := by rw [s3.1 _ (by simp)]; config_simp; exact r46
    have r40' : c3.nreg 60040 = r := by rw [s13.1 _ (by simp), h40]
    obtain ⟨c4, k4, e4, rfl, hc4⟩ : ∃ c4 k4, Exec P W (block [.addN 60030 60110 60046,
        .storeN 60030 60049, .addN 60030 60109 60046, .storeN 60030 60040]) c3 c4 k4 ∧ k4 = 4 ∧
        c4 = { c3 with
          nreg := upd c3.nreg 60030 (A + 12 + 9 * R + t)
          nmem := upd (upd c3.nmem (A + 12 + 10 * R + t) v) (A + 12 + 9 * R + t) r } := by
      exec_block
      all_goals first
        | (config_simp; simp (config := { failIfUnchanged := false }) only [b9', b10', r46']; omega)
        | skip
      refine ⟨rfl, ?_⟩
      simp only [b9', b10', r46', r49, r40']
    refine ⟨_, 4, e4, ⟨by omega, s13.trans (by rw [hc4]; exact Same.upd1 (by simp)), fun x hx => ?_,
      fun f u hf hu => ?_⟩⟩
    · rw [hc4]; config_simp; rw [m3', fv_store_out (by norm_num) ht hx, fv_store_out (by norm_num) ht hx,
        fv_store_out (by norm_num) hr hx]
    · rw [hc4]; config_simp; rw [m3', fv_store ht hu, fv_store ht hu, fv_store hr hu]
      by_cases h8 : f = 8 ∧ u = r
      · rw [ite_eq_left h8]
        have : ¬ (f = 9 ∧ u = t) := fun hh => by omega
        have : ¬ (f = 10 ∧ u = t) := fun hh => by omega
        simp [*]
      · simp only [ite_eq_right h8, hup, true_and]
        split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by rw [hbv, r49]; exact hup) (spec_skip hw3 ?_)
    refine ⟨by omega, s13, fun x hx => ?_, fun f u hf hu => ?_⟩
    · rw [m3', fv_store_out (by norm_num) hr hx]
    · rw [m3', fv_store hr hu]
      simp only [hup, false_and, ite_false]

/-- The field view of the top-pass state. -/
def t3Of (m : ℕ → ℕ) (A R : ℕ) : T3 := ⟨fv m A R 8, fv m A R 9, fv m A R 10⟩

/-- **One step of the top pass** realises `p2` on fields `8`, `9`, `10`. -/
theorem p2Body_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {i : ℕ} (h20 : c.nreg 60020 = i) (hi : i < R)
    (hr : fv c.nmem A R 1 i < R)
    (hpch : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 4 (fv c.nmem A R 1 i) < R)
    (hprg : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 3 (fv c.nmem A R 1 i) < R)
    (htop : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 8 (fv c.nmem A R 3 (fv c.nmem A R 1 i)) < R) :
    ∃ c' k, Exec P W p2Body c c' k ∧ k ≤ 40 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60020 = i + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        (let st' := p2 (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
          (fv c.nmem A R 7) (t3Of c.nmem A R) i
         if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
         else fv c.nmem A R f u) := by
  have b1 := hR.b 1 (by norm_num)
  simp only [Nat.reduceAdd] at b1
  set r := fv c.nmem A R 1 i with hrdef
  have hr' : c.nmem (A + 12 + 1 * R + i) = r := rfl
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.addN 60030 60101 60020,
      .loadN 60040 60030]) c c1 k1 ∧ k1 = 2 ∧
      c1 = { c with nreg := upd (upd c.nreg 60030 (A + 12 + 1 * R + i)) 60040 r } := by
    exec_block
    · rw [b1, h20]; omega
    · refine ⟨rfl, ?_⟩
      rw [b1, h20, hr']
  have s1 : Same [60030, 60040] c c1 := by rw [hc1]; same_tac
  have m1 : c1.nmem = c.nmem := by rw [hc1]
  have hw1 := e1.wb_right
  have hR1 : DRegs A R K CB RB LB c1 := hR.of_same s1 (by simp [Prot])
  have r40 : c1.nreg 60040 = r := by rw [hc1]; config_simp
  unfold p2Body
  -- the middle
  have hmid : ∃ c2 k2, Exec P W (.ifLtN 60010 60040
        (.seq (ldF 60041 4 60040) (.seq (ldF 60042 11 60041) (ifEqN 60042 60011 topBr ntBr)))
        topBr) c1 c2 k2 ∧ k2 ≤ 34 ∧
      Same [60041, 60042, 60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c1 c2 ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c2.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        (let st' := p2 (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
          (fv c.nmem A R 7) (t3Of c.nmem A R) i
         if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
         else fv c.nmem A R f u) := by
    -- the top branch, from any configuration with memory that of `c`
    have htopB : ∀ d : Config, WordsBounded W d → DRegs A R K CB RB LB d → d.nreg 60040 = r →
        d.nmem = c.nmem → (r = 0 ∨ fv c.nmem A R 11 (fv c.nmem A R 4 r) = 1) →
        ∃ d' k, Exec P W topBr d d' k ∧ k = 6 ∧ Same [60030] d d' ∧
          (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → d'.nmem a = c.nmem a) ∧
          ∀ f u, f < 19 → u < R → fv d'.nmem A R f u =
            (let st' := p2 (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
              (fv c.nmem A R 7) (t3Of c.nmem A R) i
             if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
             else fv c.nmem A R f u) := by
      intro d hwd hRd h40 hmd hcond
      obtain ⟨d', k, e, hk, s, hm, hv⟩ := topBr_exec (P := P) hwd hRd hAW h40 hr
      refine ⟨d', k, e, hk, s, fun a ha => by rw [hm a ha, hmd], fun f u hf hu => ?_⟩
      rw [hv f u hf hu, hmd]
      simp only [p2, ← hrdef, ite_eq_left hcond, t3Of, Function.update_apply]
      by_cases hur : u = r
      · subst hur; interval_cases f <;> simp
      · simp only [hur, and_false, ite_false]
        split_ifs with h8 h9 h10 <;> subst_vars <;> rfl
    by_cases h0 : r = 0
    · refine spec_ifLtN_false (by rw [hR1.zero, r40, h0]; omega) ?_
      obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := htopB c1 hw1 hR1 r40 m1 (Or.inl h0)
      exact ⟨c2, k2, e2, by omega, s2.mono (by simp), hm2, hv2⟩
    · refine spec_ifLtN_true (by rw [hR1.zero, r40]; omega) ?_
      have hpr := hpch h0; have hpg := hprg h0; have htp := htop h0
      obtain ⟨c2, k2, e2, rfl, m2, s2, r41⟩ := ldF_rel (P := P) hw1 60041 4 60040
        (by rw [show fb 4 = 60104 from rfl, hR1.b 4 (by norm_num), r40]; omega)
      rw [show fb 4 = 60104 from rfl, hR1.b 4 (by norm_num), r40, m1] at r41
      have hR2 : DRegs A R K CB RB LB c2 := hR1.of_same s2 (by simp [Prot])
      obtain ⟨c3, k3, e3, rfl, m3, s3, r42⟩ := ldF_rel (P := P) e2.wb_right 60042 11 60041
        (by
          rw [show fb 11 = 60111 from rfl, hR2.b 11 (by norm_num), r41]
          have : fv c.nmem A R 4 r < R := hpr
          unfold fv at this
          omega)
      rw [show fb 11 = 60111 from rfl, hR2.b 11 (by norm_num), r41, m2, m1] at r42
      have hR3 : DRegs A R K CB RB LB c3 := hR2.of_same s3 (by simp [Prot])
      have s23 : Same [60041, 60042, 60030] c1 c3 := (s2.mono (by simp)).trans (s3.mono (by simp))
      have m13 : c3.nmem = c.nmem := by rw [m3, m2, m1]
      have r40' : c3.nreg 60040 = r := by rw [s23.1 _ (by simp), r40]
      refine spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩
      by_cases hrem : fv c.nmem A R 11 (fv c.nmem A R 4 r) = 1
      · refine ifEqN_eq (by rw [r42, hR3.one]; exact hrem) ?_
        obtain ⟨c4, k4, e4, hk4, s4, hm4, hv4⟩ :=
          htopB c3 e3.wb_right hR3 r40' m13 (Or.inr hrem)
        exact ⟨c4, k4, e4, by omega, s23.trans (s4.mono (by simp)) |>.mono (by simp), hm4, hv4⟩
      · refine ifEqN_ne (by rw [r42, hR3.one]; exact hrem) ?_
        obtain ⟨c4, k4, e4, hk4, s4, hm4, hv4⟩ := ntBr_exec (P := P) e3.wb_right hR3 hAW r40' hr hpg htp
          (by rw [m13]) (by rw [m13])
        refine ⟨c4, k4, e4, fun k' hk' => ⟨by omega, (s23.mono (by simp)).trans (s4.mono (by simp)),
          fun a ha => by rw [hm4 a ha, m13], fun f u hf hu => ?_⟩⟩
        rw [hv4 f u hf hu, m13]
        have hnc : ¬ (r = 0 ∨ fv c.nmem A R 11 (fv c.nmem A R 4 r) = 1) := by tauto
        simp only [p2, ← hrdef, ite_eq_right hnc, t3Of]
        set T := fv c.nmem A R 8 (fv c.nmem A R 3 r) with hT
        set v := min (fv c.nmem A R 7 r) (fv c.nmem A R 7 T - fv c.nmem A R 7 r) with hv
        rcases (show f = 8 ∨ f = 9 ∨ f = 10 ∨ (f ≠ 8 ∧ f ≠ 9 ∧ f ≠ 10) by omega) with
          h8 | h9 | h10 | ⟨h8, h9, h10⟩
        · subst h8
          by_cases hup : fv c.nmem A R 10 T < v
          · rw [ite_eq_left hup]; simp [Function.update_apply]
          · rw [ite_eq_right hup]; simp [Function.update_apply]
        · subst h9
          by_cases hup : fv c.nmem A R 10 T < v
          · rw [ite_eq_left hup]; simp [Function.update_apply, hup]
          · rw [ite_eq_right hup]; simp [hup]
        · subst h10
          by_cases hup : fv c.nmem A R 10 T < v
          · rw [ite_eq_left hup]; simp [Function.update_apply, hup]
          · rw [ite_eq_right hup]; simp [hup]
        · simp [h8, h9, h10]
  obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := hmid
  have hR2 : DRegs A R K CB RB LB c2 := hR1.of_same s2 (by simp [Prot])
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20⟩ := incr_exec (P := P) e2.wb_right hR2.one
    (by rw [s2.1 _ (by simp), s1.1 _ (by simp), h20]; omega)
  have s13 : Same [60030, 60040, 60041, 60042, 60043, 60046, 60044, 60047, 60048, 60049, 60050,
      60020] c c3 := ((s1.mono (by simp)).trans (s2.mono (by simp))).trans (s3.mono (by simp))
  refine ⟨c3, 2 + (k2 + 1), .seq e1 (.seq e2 e3), by omega, ?_, by
    rw [r20, s2.1 _ (by simp), s1.1 _ (by simp), h20], fun f u hf hu => by rw [m3, hv2 f u hf hu]⟩
  exact DFr.of_same s13 (by simp [Prot]) (fun a ha => by rw [m3, hm2 a ha])

/-- Two top-pass states agree below `R`. -/
def T3Agree (R : ℕ) (st st' : T3) : Prop :=
  ∀ u, u < R → st.top u = st'.top u ∧ st.best u = st'.best u ∧ st.bestv u = st'.bestv u

/-- `p2` depends only on the entries it reads. -/
theorem p2_congr {R i : ℕ} {o o' p p' q q' rm rm' S S' : ℕ → ℕ} {st st' : T3}
    (hag : T3Agree R st st') (ho : o i = o' i) (hr : o' i < R)
    (hq : o' i ≠ 0 → q (o' i) = q' (o' i)) (hrm : o' i ≠ 0 → rm (q' (o' i)) = rm' (q' (o' i)))
    (hp : o' i ≠ 0 → p (o' i) = p' (o' i)) (hpR : o' i ≠ 0 → p' (o' i) < R)
    (htR : o' i ≠ 0 → st'.top (p' (o' i)) < R)
    (hS : ∀ u, u < R → S u = S' u) :
    T3Agree R (p2 o p q rm S st i) (p2 o' p' q' rm' S' st' i) := by
  intro u hu
  unfold p2
  rw [ho]
  by_cases h0 : o' i = 0
  · rw [ite_eq_left (Or.inl h0), ite_eq_left (Or.inl h0)]
    obtain ⟨a1, a2, a3⟩ := hag u hu
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [hq h0, hrm h0]
    by_cases htop : rm' (q' (o' i)) = 1
    · rw [ite_eq_left (Or.inr htop), ite_eq_left (Or.inr htop)]
      obtain ⟨a1, a2, a3⟩ := hag u hu
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · have hnt : ¬ (o' i = 0 ∨ rm' (q' (o' i)) = 1) := by tauto
      rw [ite_eq_right hnt, ite_eq_right hnt, hp h0]
      have ht : st.top (p' (o' i)) = st'.top (p' (o' i)) := (hag _ (hpR h0)).1
      rw [ht]
      set t := st'.top (p' (o' i)) with htdef
      have htR' := htR h0
      rw [hS _ hr, hS _ htR', (hag t htR').2.2]
      obtain ⟨a1, a2, a3⟩ := hag u hu
      split_ifs <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all

/-- **The top pass**: fields `8`, `9`, `10` end with the fold of `p2` over all search positions. -/
theorem p2S_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn ord pos prg pch rem : ℕ → ℕ}
    (h : Rooted R K up dn ord pos prg pch)
    (hord : ∀ j, j < R → fv c.nmem A R 1 j = ord j) (hprg : ∀ j, j < R → fv c.nmem A R 3 j = prg j)
    (hpch : ∀ j, j < R → fv c.nmem A R 4 j = pch j) (hrem : ∀ j, j < R → fv c.nmem A R 11 j = rem j)
    (hsize : ∀ j, j < R → fv c.nmem A R 7 j = sz R prg pch rem j) :
    ∃ c' k, Exec P W p2S c c' k ∧ k ≤ 42 * R + 3 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      T3Agree R (t3Of c'.nmem A R)
        ((List.range R).foldl (p2 ord prg pch rem (sz R prg pch rem)) (t3Of c.nmem A R)) ∧
      ∀ f u, f < 19 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R → fv c'.nmem A R f u = fv c.nmem A R f u := by
  have hKR : K < R := by have := h.hR; omega
  let S : ℕ → T3 := fun i =>
    (List.range i).foldl (p2 ord prg pch rem (sz R prg pch rem)) (t3Of c.nmem A R)
  have hS : ∀ i, S (i + 1) = p2 ord prg pch rem (sz R prg pch rem) (S i) i := fun i => by
    simp only [S, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold p2S
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  set c1 := { c with nreg := upd c.nreg 60020 0 } with hc1
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c c1 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr; rw [Machine.upd_other _ _ _ (by omega)]
  obtain ⟨c', k, e, ⟨hw', hf', hj', hag', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := p2Body)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60020 ≤ R ∧
      T3Agree R (t3Of d.nmem A R) (S (d.nreg 60020)) ∧
      ∀ f u, f < 19 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R → fv d.nmem A R f u = fv c.nmem A R f u)
    (fun d => 42 * (R - d.nreg 60020)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hjd, hagd, hvd⟩ htest => by
      have hRd := hR.frame hfd
      rw [hRd.rR] at htest
      obtain ⟨i, hidef⟩ : ∃ i, d.nreg 60020 = i := ⟨_, rfl⟩
      rw [hidef] at htest hjd hagd
      have hv1 : ∀ v, v < R → fv d.nmem A R 1 v = ord v := fun v hv => by
        rw [hvd 1 v (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv, hord v hv]
      have hv3 : ∀ v, v < R → fv d.nmem A R 3 v = prg v := fun v hv => by
        rw [hvd 3 v (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv, hprg v hv]
      have hv4 : ∀ v, v < R → fv d.nmem A R 4 v = pch v := fun v hv => by
        rw [hvd 4 v (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv, hpch v hv]
      have hv11 : ∀ v, v < R → fv d.nmem A R 11 v = rem v := fun v hv => by
        rw [hvd 11 v (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv, hrem v hv]
      have hv7 : ∀ v, v < R → fv d.nmem A R 7 v = sz R prg pch rem v := fun v hv => by
        rw [hvd 7 v (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv, hsize v hv]
      have hr := h.ord_lt i htest
      have hP2 := p2_fold h (rem := rem) (S := sz R prg pch rem) (le_of_lt htest) (fun _ _ => rfl)
        (t3Of c.nmem A R)
      -- the top of the parent is already computed
      have htopR : ord i ≠ 0 → (S i).top (prg (ord i)) < R := fun h0 => by
        have hpR := h.prg_lt _ hr h0
        have := h.pos_prg _ hr h0
        rw [h.pos_ord i htest] at this
        exact (hP2.1 _ hpR this).1
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := p2Body_exec (P := P) hwd hRd hAW hidef htest
        (by rw [hv1 i htest]; exact hr)
        (fun h0 => by rw [hv1 i htest] at h0 ⊢; rw [hv4 _ hr]; have := h.pch_lt _ hr h0; omega)
        (fun h0 => by rw [hv1 i htest] at h0 ⊢; rw [hv3 _ hr]; exact h.prg_lt _ hr h0)
        (fun h0 => by
          rw [hv1 i htest] at h0 ⊢
          rw [hv3 _ hr]
          have := (hagd _ (h.prg_lt _ hr h0)).1
          simp only [t3Of] at this
          rw [this]
          exact htopR h0)
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by omega, ?_, fun f u hf h8 h9 h10 hu => ?_⟩,
        by rw [h20', hidef]; omega⟩
      · rw [h20', hS i]
        have hc := p2_congr (R := R) (i := i) (st := t3Of d.nmem A R) (st' := S i) hagd
          (hv1 i htest) hr (fun h0 => hv4 _ hr) (fun h0 => hv11 _ (by have := h.pch_lt _ hr h0; omega))
          (fun h0 => hv3 _ hr) (fun h0 => h.prg_lt _ hr h0) htopR hv7
        intro u hu
        obtain ⟨a1, a2, a3⟩ := hc u hu
        refine ⟨?_, ?_, ?_⟩
        · show fv d'.nmem A R 8 u = _; rw [hv'' 8 u (by norm_num) hu]; exact a1
        · show fv d'.nmem A R 9 u = _; rw [hv'' 9 u (by norm_num) hu]; exact a2
        · show fv d'.nmem A R 10 u = _; rw [hv'' 10 u (by norm_num) hu]; exact a3
      · rw [hv'' f u hf hu]
        simp only [h8, h9, h10, ite_false]
        exact hvd f u hf h8 h9 h10 hu)
    ⟨hw1, hf1, by simp only [hc1]; config_simp; omega, by
      simp only [hc1]; config_simp; intro u _; exact ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ _ _ => rfl⟩
  have hR' := hR.frame hf'
  rw [hR'.rR] at htest
  have hjR : c'.nreg 60020 = R := by omega
  have h0 : c1.nreg 60020 = 0 := by simp only [hc1]; config_simp
  rw [h0] at hk
  rw [hjR] at hag'
  exact ⟨c', k, e, by omega, hw', hf', hag', hv'⟩

end p2ram

end

end Chazelle.Core.DecR
