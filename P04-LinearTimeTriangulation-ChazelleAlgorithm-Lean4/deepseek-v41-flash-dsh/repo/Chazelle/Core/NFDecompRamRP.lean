module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.NFDecompRamCP

/-!
# Tree decomposition (WP-C), part 18: the root step and the region pass on the RAM

* `rootS_exec`: in the first round (root active with the root slot) the root code is set;
* `rpS_exec`: the region pass writes, at every region, the fields `size` (`1`), `act`, `cpar`,
  `side`, `lpar` given by `rpv`, and counts the finished singletons.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

/-- The new value of field `f` of region `r` in the region pass, read from the memory after the
chord pass. -/
def rpv (m : ℕ → ℕ) (A R f r : ℕ) : ℕ :=
  if f = 7 then 1
  else if fv m A R 8 r = r then
    (if fv m A R 13 r = 1 then
      (if fv m A R 9 r = r then
        (if f = 13 then 0
         else if f = 0 then (if fv m A R 15 r = 2 then 2 * r + 1 else 2 * fv m A R 14 r)
         else fv m A R f r)
       else
        (if f = 14 then fv m A R 4 (fv m A R 9 r)
         else if f = 15 then (if fv m A R 5 (fv m A R 9 r) = 1 then 1 else 0)
         else fv m A R f r))
     else fv m A R f r)
  else if fv m A R 12 (fv m A R 4 r) = 1 then
    (if f = 13 then 1 else if f = 14 then fv m A R 4 r
     else if f = 15 then (if fv m A R 5 r = 1 then 0 else 1) else fv m A R f r)
  else fv m A R f r

/-- The fields of the region pass. -/
def RPF (f : ℕ) : Prop := f = 0 ∨ f = 7 ∨ f = 13 ∨ f = 14 ∨ f = 15

instance (f : ℕ) : Decidable (RPF f) := inferInstanceAs (Decidable (_ ∨ _))

/-- Region `r` finishes as a singleton in this round. -/
def SingAt (m : ℕ → ℕ) (A R r : ℕ) : Prop :=
  fv m A R 8 r = r ∧ fv m A R 13 r = 1 ∧ fv m A R 9 r = r

instance (m : ℕ → ℕ) (A R r : ℕ) : Decidable (SingAt m A R r) :=
  inferInstanceAs (Decidable (_ ∧ _))

section rpram

variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}

/-- A store helper: `field f [e] := v` through `stF` with the index in `60020`. -/
theorem stF_at {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {f r v vr : ℕ} (hf : f < 19) (h20 : c.nreg 60020 = r) (hr : r < R)
    (hvr : c.nreg vr = v) (hv : vr ≠ 60030) :
    ∃ c' k, Exec P W (stF f 60020 vr) c c' k ∧ k = 2 ∧
      c'.nmem = upd c.nmem (A + 12 + f * R + r) v ∧ Same [60030] c c' := by
  obtain ⟨c', k, e, hk, m, s⟩ := stF_rel (P := P) hw f 60020 vr hv
    (by rw [show fb f = 60100 + f from rfl, hR.b f (⋄), h20]
        have : f * R ≤ 18 * R := Nat.mul_le_mul_right _ (⋄)
        omega)
  refine ⟨c', k, e, hk, ?_, s⟩
  rw [m, show fb f = 60100 + f from rfl, hR.b f (⋄), h20, hvr]

/-- A load helper: `d := field f [x]`. -/
theorem ldF_at {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {d f x xr : ℕ} (hf : f < 19) (hxr : c.nreg xr = x) (hx : x < R) :
    ∃ c' k, Exec P W (ldF d f xr) c c' k ∧ k = 2 ∧ c'.nmem = c.nmem ∧ Same [60030, d] c c' ∧
      c'.nreg d = fv c.nmem A R f x := by
  obtain ⟨c', k, e, hk, m, s, r⟩ := ldF_rel (P := P) hw d f xr
    (by rw [show fb f = 60100 + f from rfl, hR.b f (⋄), hxr]
        have : f * R ≤ 18 * R := Nat.mul_le_mul_right _ (⋄)
        omega)
  refine ⟨c', k, e, hk, m, s, ?_⟩
  rw [r, show fb f = 60100 + f from rfl, hR.b f (⋄), hxr]; rfl

/-- **The root step.** -/
theorem rootS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) (h0 : fv c.nmem A R 8 0 = 0) :
    ∃ c' k, Exec P W rootS c c' k ∧ k ≤ 30 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60068, 60069, 60070, 60051, 60052, 60024] c c' ∧
      c'.nreg 60024 = (if fv c.nmem A R 13 0 = 1 then (if fv c.nmem A R 15 0 = 2 then
        code (tv c.nmem A R 9) (tv c.nmem A R 4) 0 else c.nreg 60024) else c.nreg 60024) := by
  have hR0 : 0 < R := by have := hF.hKR; omega
  unfold rootS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r68⟩ := ldF_rel (P := P) hw 60068 13 60010
    (by rw [show fb 13 = 60113 from rfl, hR.b 13 (⊛), hR.zero]; omega)
  rw [show fb 13 = 60113 from rfl, hR.b 13 (⊛), hR.zero] at r68
  change c1.nreg 60068 = fv c.nmem A R 13 0 at r68
  have hR1 := hR.of_same s1 (⊚ Prot)
  refine spec_seq ⟨c1, 2, e1, ?_⟩
  by_cases ha : fv c.nmem A R 13 0 = 1
  · refine ifEqN_eq (by rw [r68, hR1.one]; exact ha) ?_
    obtain ⟨c2, k2, e2, rfl, m2, s2, r69⟩ := ldF_rel (P := P) e1.wb_right 60069 15 60010
      (by rw [show fb 15 = 60115 from rfl, hR1.b 15 (⊛), hR1.zero]; omega)
    rw [show fb 15 = 60115 from rfl, hR1.b 15 (⊛), hR1.zero, m1] at r69
    change c2.nreg 60069 = fv c.nmem A R 15 0 at r69
    have hR2 := hR1.of_same s2 (⊚ Prot)
    refine spec_seq ⟨c2, 2, e2, ?_⟩
    by_cases hs : fv c.nmem A R 15 0 = 2
    · refine ifEqN_eq (by rw [r69, hR2.two]; exact hs) ?_
      obtain ⟨b1, b2⟩ := hF.best 0 hR0 h0
      obtain ⟨c3, k3, e3, hk3, m3, s3, r70⟩ := codeS_exec (P := P) e2.wb_right hR2 hAW
        (d := 60070) (xr := 60010) (x := 0) (⌖) (by decide) hR2.zero hR0
        (by rw [m2, m1]; exact b1) (by rw [m2, m1]; exact b2)
      rw [m2, m1] at r70
      refine spec_seq ⟨c3, k3, e3, ?_⟩
      refine spec_instr (Exec.copyN e3.wb_right _ _) fun _ => ?_
      refine ⟨⋄, by rw [m3, m2, m1], ?_, ?_⟩
      · exact ((((s1.mono (✓)).trans (s2.mono (by simp))).trans (s3.mono (by simp))).trans
          (Same.upd1 (✓)))
      · config_simp; rw [r70, ite_eq_left ha, ite_eq_left hs]
    · refine ifEqN_ne (by rw [r69, hR2.two]; exact hs) (spec_skip e2.wb_right ?_)
      intro k' hk'
      refine ⟨⋄, by rw [m2, m1], (s1.mono (by simp)).trans (s2.mono (by simp)), ?_⟩
      rw [ite_eq_left ha, ite_eq_right hs, s2.1 _ (✓), s1.1 _ (by simp)]
  · refine ifEqN_ne (by rw [r68, hR1.one]; exact ha) (spec_skip e1.wb_right ?_)
    intro k' hk'
    refine ⟨⋄, m1, s1.mono (by simp), ?_⟩
    rw [ite_eq_right ha, s1.1 _ (✓)]

/-- A finishing singleton. -/
theorem singS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hcp : fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R) (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W singS c c' k ∧ k ≤ 16 ∧
      c'.nmem = upd (upd c.nmem (A + 12 + 13 * R + r) 0) (A + 12 + 0 * R + r)
        (if fv c.nmem A R 15 r = 2 then 2 * r + 1 else 2 * fv c.nmem A R 14 r) ∧
      Same [60030, 60071, 60072, 60073, 60023] c c' ∧ c'.nreg 60023 = c.nreg 60023 + 1 := by
  unfold singS
  obtain ⟨c1, k1, e1, rfl, m1, s1⟩ := stF_at (P := P) hw hR hAW (f := 13) (⊛) h20 hr
    hR.zero (⌖)
  have hR1 := hR.of_same s1 (⊚ Prot)
  have r20 : c1.nreg 60020 = r := Ρ s1.1 _ (✓), h20
  obtain ⟨c2, k2, e2, rfl, m2, s2, r71⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60071)
    (f := 15) (⊛) r20 hr
  Ξ' m1, fv_store hr hr, ite_eq_right (show ¬ (15 = 13 ∧ r = r) by omega) at r71
  have hR2 := hR1.of_same s2 (⊚ Prot)
  have r20' : c2.nreg 60020 = r := Ρ s2.1 _ (✓), r20
  set y := if fv c.nmem A R 15 r = 2 then 2 * r + 1 else 2 * fv c.nmem A R 14 r with hy
  obtain ⟨c3, k3, e3, hk3, m3, s3, r72⟩ : ∃ c3 k3, Exec P W (ifEqN 60071 60012
      (block [.addN 60072 60020 60020, .addN 60072 60072 60011])
      (.seq (ldF 60073 14 60020) (.instr (.addN 60072 60073 60073)))) c2 c3 k3 ∧ k3 ≤ 7 ∧
      c3.nmem = c2.nmem ∧ Same [60030, 60072, 60073] c2 c3 ∧ c3.nreg 60072 = y := by
    have hw2 := e2.wb_right
    by_cases hs : fv c.nmem A R 15 r = 2
    · refine ifEqN_eq (by rw [r71, hR2.two]; exact hs) ?_
      clear hw
      exec_block
      · rw [r20']; omega
      · config_simp; rw [r20', hR2.one]; omega
      · refine ⟨⋄, rfl, by same_tac, ?_⟩
        config_simp; rw [r20', hR2.one, hy, ite_eq_left hs]; ring
    · refine ifEqN_ne (by rw [r71, hR2.two]; exact hs) ?_
      obtain ⟨c3, k3, e3, rfl, m3, s3, r73⟩ := ldF_at (P := P) hw2 hR2 hAW (d := 60073)
        (f := 14) (⊛) r20' hr
      Ξ' m2, m1, fv_store hr hr, ite_eq_right (show ¬ (14 = 13 ∧ r = r) by omega) at r73
      have hc := hcp hs
      refine spec_seq ⟨c3, 2, e3, spec_instr (Exec.addN e3.wb_right _ _ _ (by
        rw [r73]; unfold fv at hc ⊢; omega)) fun _ => ?_⟩
      intro k' hk'
      refine ⟨⋄, m3, (s3.mono (✓)).trans (Same.upd1 (✓)), ?_⟩
      config_simp; rw [r73, hy, ite_eq_right hs]; ring
  have hR3 := hR2.of_same s3 (⊚ Prot)
  have r20'' : c3.nreg 60020 = r := Ρ s3.1 _ (✓), r20'
  obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at (P := P) e3.wb_right hR3 hAW (f := 0) (⊛)
    r20'' hr r72 (⌖)
  have s14 : Same [60030, 60071, 60072, 60073, 60023] c c4 :=
    (((s1.mono (✓)).trans (s2.mono (✓))).trans (s3.mono (✓))).trans (s4.mono (✓))
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, k3, e3, spec_seq ⟨c4, 2, e4,
    spec_instr (Exec.addN e4.wb_right _ _ _ (by
      Ξ s14.1 60011 (✓), hR.one
      have : c4.nreg 60023 = c.nreg 60023 := by
        Ξ s4.1 _ (✓), s3.1 _ (✓), s2.1 _ (✓), s1.1 _ (✓)
      omega)) fun _ => ?_⟩⟩⟩⟩
  refine ⟨⋄, by config_simp; rw [m4, m3, m2, m1], s14.trans (Same.upd1 (✓)), ?_⟩
  config_simp
  rw [s14.1 60011 (✓), hR.one, s4.1 _ (✓), s3.1 _ (✓), s2.1 _ (✓),
    s1.1 _ (✓)]

/-- A cut component records its new slot. -/
theorem cutS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r b : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (h75 : c.nreg 60075 = b) (hb : b < R) :
    ∃ c' k, Exec P W cutS c c' k ∧ k ≤ 13 ∧
      c'.nmem = upd (upd c.nmem (A + 12 + 14 * R + r) (fv c.nmem A R 4 b)) (A + 12 + 15 * R + r)
        (if fv c.nmem A R 5 b = 1 then 1 else 0) ∧
      Same [60030, 60074, 60076] c c' := by
  unfold cutS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r74⟩ := ldF_at (P := P) hw hR hAW (d := 60074) (f := 4)
    (by norm_num) h75 hb
  have hR1 := hR.of_same s1 (by simp [Prot])
  obtain ⟨c2, k2, e2, rfl, m2, s2⟩ := stF_at (P := P) e1.wb_right hR1 hAW (f := 14) (by norm_num)
    (by rw [s1.1 60020 (by simp), h20]) hr r74 (by decide)
  have hR2 := hR1.of_same s2 (by simp [Prot])
  obtain ⟨c3, k3, e3, rfl, m3, s3, r76⟩ := ldF_at (P := P) e2.wb_right hR2 hAW (d := 60076) (f := 5)
    (by norm_num) (by rw [s2.1 60075 (by simp), s1.1 60075 (by simp), h75]) hb
  rw [m2, m1, fv_store hr hb, ite_eq_right (show ¬ (5 = 14 ∧ b = r) by omega)] at r76
  have hR3 := hR2.of_same s3 (by simp [Prot])
  have r20 : c3.nreg 60020 = r := by rw [s3.1 60020 (by simp), s2.1 60020 (by simp), s1.1 60020 (by simp), h20]
  have s13 : Same [60030, 60074, 60076] c c3 :=
    ((s1.mono (by simp)).trans (s2.mono (by simp))).trans (s3.mono (by simp))
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩⟩
  by_cases hd : fv c.nmem A R 5 b = 1
  · refine ifEqN_eq (by rw [r76, hR3.one]; exact hd) ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at (P := P) e3.wb_right hR3 hAW (f := 15) (by norm_num)
      r20 hr hR3.one (by decide)
    exact ⟨_, 2, e4, by omega, by rw [m4, m3, m2, m1, ite_eq_left hd], s13.trans (s4.mono (by simp))⟩
  · refine ifEqN_ne (by rw [r76, hR3.one]; exact hd) ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at (P := P) e3.wb_right hR3 hAW (f := 15) (by norm_num)
      r20 hr hR3.zero (by decide)
    exact ⟨_, 2, e4, fun k' hk' => ⟨by omega, by rw [m4, m3, m2, m1, ite_eq_right hd],
      s13.trans (s4.mono (by simp))⟩⟩

/-- A region that becomes a top when its parent chord was just cut. -/
theorem ntR_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hp : fv c.nmem A R 4 r < R) :
    ∃ c' k, Exec P W ntR c c' k ∧ k ≤ 22 ∧
      c'.nmem = (if fv c.nmem A R 12 (fv c.nmem A R 4 r) = 1 then
        upd (upd (upd c.nmem (A + 12 + 13 * R + r) 1) (A + 12 + 14 * R + r) (fv c.nmem A R 4 r))
          (A + 12 + 15 * R + r) (if fv c.nmem A R 5 r = 1 then 0 else 1)
        else c.nmem) ∧
      Same [60030, 60078, 60079, 60080] c c' := by
  unfold ntR
  obtain ⟨c1, k1, e1, rfl, m1, s1, r78⟩ := ldF_at (P := P) hw hR hAW (d := 60078) (f := 4)
    (by norm_num) h20 hr
  have hR1 := hR.of_same s1 (by simp [Prot])
  obtain ⟨c2, k2, e2, rfl, m2, s2, r79⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60079) (f := 12)
    (by norm_num) r78 hp
  rw [m1] at r79
  have hR2 := hR1.of_same s2 (by simp [Prot])
  have r20 : c2.nreg 60020 = r := by rw [s2.1 60020 (by simp), s1.1 60020 (by simp), h20]
  have s12 : Same [60030, 60078, 60079, 60080] c c2 := (s1.mono (by simp)).trans (s2.mono (by simp))
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, ?_⟩⟩
  by_cases hpd : fv c.nmem A R 12 (fv c.nmem A R 4 r) = 1
  · refine ifEqN_eq (by rw [r79, hR2.one]; exact hpd) ?_
    obtain ⟨c3, k3, e3, rfl, m3, s3⟩ := stF_at (P := P) e2.wb_right hR2 hAW (f := 13) (by norm_num)
      r20 hr hR2.one (by decide)
    have hR3 := hR2.of_same s3 (by simp [Prot])
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at (P := P) e3.wb_right hR3 hAW (f := 14) (by norm_num)
      (by rw [s3.1 60020 (by simp), r20]) hr (by rw [s3.1 60078 (by simp), s2.1 60078 (by simp), r78]) (by decide)
    have hR4 := hR3.of_same s4 (by simp [Prot])
    obtain ⟨c5, k5, e5, rfl, m5, s5, r80⟩ := ldF_at (P := P) e4.wb_right hR4 hAW (d := 60080) (f := 5)
      (by norm_num) (by rw [s4.1 60020 (by simp), s3.1 60020 (by simp), r20]) hr
    rw [m4, m3, m2, m1, fv_store hr hr, fv_store hr hr, ite_eq_right (show ¬ (5 = 14 ∧ r = r) by omega),
      ite_eq_right (show ¬ (5 = 13 ∧ r = r) by omega)] at r80
    have hR5 := hR4.of_same s5 (by simp [Prot])
    have r20' : c5.nreg 60020 = r := by
      rw [s5.1 60020 (by simp), s4.1 60020 (by simp), s3.1 60020 (by simp), r20]
    have s15 : Same [60030, 60078, 60079, 60080] c c5 :=
      ((s12.trans (s3.mono (by simp))).trans (s4.mono (by simp))).trans (s5.mono (by simp))
    refine spec_seq ⟨_, 2, e3, spec_seq ⟨_, 2, e4, spec_seq ⟨c5, 2, e5, ?_⟩⟩⟩
    by_cases hd : fv c.nmem A R 5 r = 1
    · refine ifEqN_eq (by rw [r80, hR5.one]; exact hd) ?_
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_at (P := P) e5.wb_right hR5 hAW (f := 15) (by norm_num)
        r20' hr hR5.zero (by decide)
      exact ⟨_, 2, e6, by omega, by rw [m6, m5, m4, m3, m2, m1, ite_eq_left hpd, ite_eq_left hd],
        s15.trans (s6.mono (by simp))⟩
    · refine ifEqN_ne (by rw [r80, hR5.one]; exact hd) ?_
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_at (P := P) e5.wb_right hR5 hAW (f := 15) (by norm_num)
        r20' hr hR5.one (by decide)
      exact ⟨_, 2, e6, fun k' hk' => ⟨by omega, by
        rw [m6, m5, m4, m3, m2, m1, ite_eq_left hpd, ite_eq_right hd], s15.trans (s6.mono (by simp))⟩⟩
  · refine ifEqN_ne (by rw [r79, hR2.one]; exact hpd) (spec_skip e2.wb_right ?_)
    intro k' hk'
    exact ⟨by omega, by rw [m2, m1, ite_eq_right hpd], s12⟩

/-- The top branch of the region pass. -/
theorem topR_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (ht : fv c.nmem A R 8 r = r)
    (hb : fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r = r → fv c.nmem A R 15 r ≠ 2 →
      fv c.nmem A R 14 r < R)
    (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W topR c c' k ∧ k ≤ 28 ∧
      Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c.nmem A R f r else fv c.nmem A R f u) ∧
      c'.nreg 60023 = c.nreg 60023 + (if SingAt c.nmem A R r then 1 else 0) := by
  unfold topR
  obtain ⟨c1, k1, e1, rfl, m1, s1, r77⟩ := ldF_at (P := P) hw hR hAW (d := 60077) (f := 13)
    (⊛) h20 hr
  have hR1 := hR.of_same s1 (⊚ Prot)
  have r20 : c1.nreg 60020 = r := Ρ s1.1 60020 (✓), h20
  refine spec_seq ⟨c1, 2, e1, ?_⟩
  by_cases ha : fv c.nmem A R 13 r = 1
  · refine ifEqN_eq (by rw [r77, hR1.one]; exact ha) ?_
    obtain ⟨c2, k2, e2, rfl, m2, s2, r75⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60075)
      (f := 9) (⊛) r20 hr
    Ξ' m1 at r75
    have hR2 := hR1.of_same s2 (⊚ Prot)
    have r20' : c2.nreg 60020 = r := Ρ s2.1 60020 (✓), r20
    have m12 : c2.nmem = c.nmem := Ρ m2, m1
    have s12 : Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076] c c2 :=
      (s1.mono (✓)).trans (s2.mono (✓))
    refine spec_seq ⟨c2, 2, e2, ?_⟩
    by_cases hs : fv c.nmem A R 9 r = r
    · refine ifEqN_eq (by rw [r75, r20']; exact hs) ?_
      obtain ⟨c3, k3, e3, hk3, m3, s3, r23⟩ := singS_exec (P := P) e2.wb_right hR2 hAW r20' hr
        (by rw [m12]; exact hcp ha hs)
        (by rw [s2.1 60023 (✓), s1.1 60023 (✓)]; exact hfin)
      have hsing : SingAt c.nmem A R r := ⟨ht, ha, hs⟩
      refine ⟨c3, k3, e3, ⋄, s12.trans (s3.mono (✓)), fun a hA => ?_,
        fun f u hf hu => ?_, ?_⟩
      · rw [m3, m12, fv_store_out (⊛) hr hA, fv_store_out (⊛) hr hA]
      · Ξ m3, m12, fv_store hr hu, fv_store hr hu
        by_cases hur : u = r
        · subst hur
          by_cases h0 : f = 0
          · subst h0; Θ rpv, RPF, ht, ha, hs
          by_cases h13 : f = 13
          · subst h13; Θ rpv, RPF, ht, ha, hs
          · ϴ h0, h13, false_and, ite_false, true_and
            unfold rpv; simp only [ht, ha, hs, h0, h13, ite_true]; split_ifs <;> simp_all
        · Θ hur
      · rw [r23, ite_eq_left hsing, s2.1 60023 (✓), s1.1 60023 (✓)]
    · refine ifEqN_ne (by rw [r75, r20']; exact hs) ?_
      obtain ⟨c3, k3, e3, hk3, m3, s3⟩ := cutS_exec (P := P) e2.wb_right hR2 hAW r20' hr
        (Ρ r75) (hb ha)
      have hsing : ¬ SingAt c.nmem A R r := fun h => hs h.2.2
      refine ⟨c3, k3, e3, fun k' hk' => ⟨⋄, s12.trans (s3.mono (✓)), fun a hA => ?_,
        fun f u hf hu => ?_, ?_⟩⟩
      · rw [m3, m12, fv_store_out (⊛) hr hA, fv_store_out (⊛) hr hA]
      · Ξ m3, m12, fv_store hr hu, fv_store hr hu
        by_cases hur : u = r
        · subst hur
          by_cases h14 : f = 14
          · subst h14; Θ rpv, RPF, ht, ha, hs
          by_cases h15 : f = 15
          · subst h15; Θ rpv, RPF, ht, ha, hs
          · ϴ h14, h15, false_and, ite_false, true_and
            unfold rpv; simp only [ht, ha, hs, h14, h15, ite_true, ite_false]; split_ifs <;> simp_all
        · Θ hur
      · rw [ite_eq_right hsing, Nat.add_zero, s3.1 60023 (✓), s2.1 60023 (✓),
          s1.1 60023 (✓)]
  · refine ifEqN_ne (by rw [r77, hR1.one]; exact ha) (spec_skip e1.wb_right ?_)
    have hsing : ¬ SingAt c.nmem A R r := fun h => ha h.2.1
    intro k' hk'
    refine ⟨⋄, s1.mono (✓), fun a _ => by rw [m1], fun f u hf hu => ?_, ?_⟩
    · Ξ m1
      by_cases hur : u = r
      · subst hur
        unfold rpv; simp only [ht, ha, ite_true, ite_false]; split_ifs <;> simp_all
      · Θ hur
    · Ξ ite_eq_right hsing, Nat.add_zero, s1.1 60023 (✓)

/-- The non-top branch of the region pass. -/
theorem ntR_exec' {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (ht : fv c.nmem A R 8 r ≠ r) (hp : fv c.nmem A R 4 r < R) :
    ∃ c' k, Exec P W ntR c c' k ∧ k ≤ 28 ∧
      Same [60030, 60078, 60079, 60080] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c.nmem A R f r else fv c.nmem A R f u) := by
  obtain ⟨c', k, e, hk, hm, s⟩ := ntR_exec (P := P) hw hR hAW h20 hr hp
  refine ⟨c', k, e, ⋄, s, fun a hA => ?_, fun f u hf hu => ?_⟩
  · Ξ hm
    by_cases hpd : fv c.nmem A R 12 (fv c.nmem A R 4 r) = 1
    · rw [ite_eq_left hpd, fv_store_out (⊛) hr hA, fv_store_out (⊛) hr hA,
        fv_store_out (⊛) hr hA]
    · Ξ ite_eq_right hpd
  · Ξ hm
    by_cases hpd : fv c.nmem A R 12 (fv c.nmem A R 4 r) = 1
    · Ξ ite_eq_left hpd, fv_store hr hu, fv_store hr hu, fv_store hr hu
      by_cases hur : u = r
      · subst hur
        unfold rpv; simp only [ht, hpd, ite_true, ite_false, RPF]; split_ifs <;> simp_all
      · Θ hur
    · Ξ ite_eq_right hpd
      by_cases hur : u = r
      · subst hur
        unfold rpv; simp only [ht, hpd, ite_false]; split_ifs <;> simp_all
      · Θ hur

/-- The field-`7` store does not change the other region-pass values. -/
theorem rpv_store7 {m : ℕ → ℕ} {r v f : ℕ} (hr : r < R) (hf : f ≠ 7) (_hf' : f < 19)
    (hb : fv m A R 8 r = r → fv m A R 13 r = 1 → fv m A R 9 r < R)
    (hp : fv m A R 8 r ≠ r → fv m A R 4 r < R) :
    rpv (upd m (A + 12 + 7 * R + r) v) A R f r = rpv m A R f r := by
  have e : ∀ g j, g ≠ 7 → j < R → fv (upd m (A + 12 + 7 * R + r) v) A R g j = fv m A R g j :=
    fun g j hg hj => Ρ fv_store hr hj, ite_eq_right (fun h => hg h.1)
  unfold rpv
  simp only [e 8 r (⊛) hr, e 13 r (⊛) hr, e 9 r (⊛) hr,
    e 15 r (⊛) hr, e 14 r (⊛) hr, e 4 r (⊛) hr,
    e 5 r (⊛) hr, e f r hf hr]
  by_cases h8 : fv m A R 8 r = r
  · by_cases h13 : fv m A R 13 r = 1
    · have := hb h8 h13
      ϴ e 4 _ (⊛) this, e 5 _ (⊛) this, h8, h13, ite_true
    · ϴ h8, h13, ite_true, ite_false
  · have := hp h8
    ϴ e 12 _ (⊛) this, h8, ite_false

/-- **One step of the region pass.** -/
theorem rpBody_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hb : fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r = r →
      fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R)
    (hp : fv c.nmem A R 8 r ≠ r → fv c.nmem A R 4 r < R)
    (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W rpBody c c' k ∧ k ≤ 40 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60020 = r + 1 ∧
      c'.nreg 60023 = c.nreg 60023 + (if SingAt c.nmem A R r then 1 else 0) ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f then rpv c.nmem A R f r else fv c.nmem A R f u := by
  unfold rpBody
  obtain ⟨c1, k1, e1, rfl, m1, s1⟩ := stF_at (P := P) hw hR hAW (f := 7) (⊛) h20 hr
    hR.one (⌖)
  have hR1 := hR.of_same s1 (⊚ Prot)
  have r20 : c1.nreg 60020 = r := Ρ s1.1 60020 (✓), h20
  have e1v : ∀ g j, j < R → fv c1.nmem A R g j = if g = 7 ∧ j = r then 1 else fv c.nmem A R g j :=
    fun g j hj => Ρ m1, fv_store hr hj
  have e1' : ∀ g j, g ≠ 7 → j < R → fv c1.nmem A R g j = fv c.nmem A R g j :=
    fun g j hg hj => Ρ e1v g j hj, ite_eq_right (fun h => hg h.1)
  obtain ⟨c2, k2, e2, rfl, m2, s2, r81⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60081) (f := 8)
    (⊛) r20 hr
  Ξ' e1' 8 r (⊛) hr at r81
  have hR2 := hR1.of_same s2 (⊚ Prot)
  have r20' : c2.nreg 60020 = r := Ρ s2.1 60020 (✓), r20
  have m12 := m2
  have s12 : Same [60030, 60081] c c2 := (s1.mono (✓)).trans (s2.mono (✓))
  -- the middle
  have hmid : ∃ c3 k3, Exec P W (ifEqN 60081 60020 topR ntR) c2 c3 k3 ∧ k3 ≤ 32 ∧
      Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076, 60078, 60079, 60080]
        c2 c3 ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c3.nmem a = c2.nmem a) ∧
      (∀ f u, f < 19 → u < R → fv c3.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c2.nmem A R f r else fv c2.nmem A R f u) ∧
      c3.nreg 60023 = c2.nreg 60023 + (if SingAt c.nmem A R r then 1 else 0) := by
    by_cases ht : fv c.nmem A R 8 r = r
    · refine ifEqN_eq (by rw [r81, r20']; exact ht) ?_
      have hs : SingAt c2.nmem A R r ↔ SingAt c.nmem A R r := by
        unfold SingAt
        Ξ m12, e1' 8 r (⊛) hr, e1' 13 r (⊛) hr, e1' 9 r (⊛) hr
      obtain ⟨c3, k3, e3, hk3, s3, ho, hv, h23⟩ := topR_exec (P := P) e2.wb_right hR2 hAW r20' hr
        (by rw [m12, e1' 8 r (⊛) hr]; exact ht)
        (by rw [m12, e1' 13 r (⊛) hr, e1' 9 r (⊛) hr]; exact hb ht)
        (by rw [m12, e1' 13 r (⊛) hr, e1' 9 r (⊛) hr,
              e1' 15 r (⊛) hr, e1' 14 r (⊛) hr]; exact hcp ht)
        (by rw [s2.1 60023 (✓), s1.1 60023 (✓)]; exact hfin)
      refine ⟨c3, k3, e3, ⋄, s3.mono (✓), ho, hv, ?_⟩
      rw [h23]; ϴ hs
    · refine ifEqN_ne (by rw [r81, r20']; exact ht) ?_
      have hs : ¬ SingAt c.nmem A R r := fun h => ht h.1
      obtain ⟨c3, k3, e3, hk3, s3, ho, hv⟩ := ntR_exec' (P := P) e2.wb_right hR2 hAW r20' hr
        (by rw [m12, e1' 8 r (⊛) hr]; exact ht)
        (by rw [m12, e1' 4 r (⊛) hr]; exact hp ht)
      exact ⟨c3, k3, e3, fun k' hk' => ⟨⋄, s3.mono (✓), ho, hv, by
        rw [ite_eq_right hs, Nat.add_zero, s3.1 60023 (✓)]⟩⟩
  obtain ⟨c3, k3, e3, hk3, s3, ho3, hv3, h23⟩ := hmid
  have hR3 := hR2.of_same s3 (⊚ Prot)
  obtain ⟨c4, k4, e4, rfl, m4, s4, r20''⟩ := incr_exec (P := P) e3.wb_right hR3.one
    (by rw [s3.1 60020 (✓), r20']; omega)
  refine ⟨c4, 2 + (2 + (k3 + 1)), .seq e1 (.seq e2 (.seq e3 e4)), ⋄, ?_, by
    rw [r20'', s3.1 60020 (✓), r20'], by
    rw [s4.1 60023 (✓), h23, s2.1 60023 (✓), s1.1 60023 (✓)], ?_⟩
  · refine DFr.of_same ((s12.mono (l' := [60030, 60081, 60077, 60075, 60071, 60072, 60073, 60023,
      60074, 60076, 60078, 60079, 60080, 60020]) (✓)).trans ((s3.mono (✓)).trans
      (s4.mono (✓)))) (⊚ Prot) (fun a hA => ?_)
    Ξ m4, ho3 a hA, m12, m1, fv_store_out (⊛) hr hA
  · intro f u hf hu
    Ξ m4, hv3 f u hf hu, m12
    by_cases h7 : f = 7
    · subst h7
      Ξ ite_eq_right (fun h => h.2.2 rfl), e1v 7 u hu
      by_cases hur : u = r
      · subst hur; Θ rpv, RPF
      · Θ hur
    · by_cases hur : u = r ∧ RPF f
      · rw [ite_eq_left ⟨hur.1, hur.2, h7⟩, ite_eq_left hur, m1,
          rpv_store7 hr h7 hf hb hp]
      · Ξ ite_eq_right (fun h => hur ⟨h.1, h.2.1⟩), ite_eq_right hur, e1' f u h7 hu

/-- The region-pass values at `r` depend only on the static fields and the entries at `r`. -/
theorem rpv_congr {m m' : ℕ → ℕ} {r : ℕ} (hr : r < R)
    (hs : ∀ f, f < 19 → ¬ RPF f → ∀ u, u < R → fv m A R f u = fv m' A R f u)
    (he : ∀ f, RPF f → fv m A R f r = fv m' A R f r)
    (hb : fv m A R 8 r = r → fv m A R 13 r = 1 → fv m A R 9 r < R)
    (hp : fv m A R 8 r ≠ r → fv m A R 4 r < R) (f : ℕ) (hf : f < 19) :
    rpv m A R f r = rpv m' A R f r := by
  have n : ∀ g, g < 19 → ¬ RPF g → ∀ u, u < R → fv m' A R g u = fv m A R g u :=
    fun g hg hc u hu => (hs g hg hc u hu).symm
  have hff : fv m' A R f r = fv m A R f r := by
    by_cases hc : RPF f
    · exact (he f hc).symm
    · exact n f hf hc r hr
  unfold rpv
  simp only [n 8 (⊛) (by unfold RPF; omega) r hr,
    n 9 (⊛) (by unfold RPF; omega) r hr, n 4 (⊛) (by unfold RPF; omega) r hr,
    n 5 (⊛) (by unfold RPF; omega) r hr, ← he 13 (by unfold RPF; omega),
    ← he 14 (by unfold RPF; omega), ← he 15 (by unfold RPF; omega), hff]
  by_cases h8 : fv m A R 8 r = r
  · by_cases h13 : fv m A R 13 r = 1
    · have := hb h8 h13
      simp only [n 4 (⊛) (by unfold RPF; omega) _ this,
        n 5 (⊛) (by unfold RPF; omega) _ this, h8, h13, ite_true]
    · ϴ h8, h13, ite_true, ite_false
  · have := hp h8
    ϴ n 12 (⊛) (by unfold RPF; omega) _ this, h8, ite_false

/-- Counting a filter over `range (j + 1)`. -/
theorem card_filter_succ (p : ℕ → Prop) [DecidablePred p] (j : ℕ) :
    ((Finset.range (j + 1)).filter p).card =
      ((Finset.range j).filter p).card + if p j then 1 else 0 := by
  Ξ Finset.range_add_one, Finset.filter_insert
  split_ifs with h
  · Ξ Finset.card_insert_of_notMem (✓)
  · rfl

/-- **The region pass.** -/
theorem rpS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W)
    (hb : ∀ r, r < R → fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : ∀ r, r < R → fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 →
      fv c.nmem A R 9 r = r → fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R)
    (hp : ∀ r, r < R → fv c.nmem A R 8 r ≠ r → fv c.nmem A R 4 r < R)
    (hfin : c.nreg 60023 + R ≤ W) :
    ∃ c' k, Exec P W rpS c c' k ∧ k ≤ 42 * R + 3 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60023 = c.nreg 60023 + ((Finset.range R).filter (fun r => SingAt c.nmem A R r)).card ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if RPF f then rpv c.nmem A R f u else fv c.nmem A R f u := by
  unfold rpS
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  set c1 := { c with nreg := upd c.nreg 60020 0 } with hc1
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c c1 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr; rw [Machine.upd_other _ _ _ (⋄)]
  have hstat : ∀ d : Config, (∀ f u, f < 19 → u < R → fv d.nmem A R f u =
      if u < d.nreg 60020 ∧ RPF f then rpv c.nmem A R f u else fv c.nmem A R f u) →
      ∀ f, f < 19 → ¬ RPF f → ∀ u, u < R → fv d.nmem A R f u = fv c.nmem A R f u :=
    fun d hv f hf hc u hu => Ρ hv f u hf hu, ite_eq_right (fun hh => hc hh.2)
  obtain ⟨c', k, e, ⟨hw', hf', hj', h23', hv'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := rpBody)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60020 ≤ R ∧
      d.nreg 60023 = c.nreg 60023 +
        ((Finset.range (d.nreg 60020)).filter (fun r => SingAt c.nmem A R r)).card ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u =
        if u < d.nreg 60020 ∧ RPF f then rpv c.nmem A R f u else fv c.nmem A R f u)
    (fun d => 42 * (R - d.nreg 60020)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hjd, h23d, hvd⟩ htest => by
      have hRd := hR.frame hfd
      rw [hRd.rR] at htest
      obtain ⟨j, hjdef⟩ : ∃ j, d.nreg 60020 = j := ⟨_, rfl⟩
      rw [hjdef] at htest hjd hvd h23d
      have hs := hstat d (by rw [hjdef]; exact hvd)
      have heC : ∀ f, RPF f → fv d.nmem A R f j = fv c.nmem A R f j := fun f hc => by
        have hf : f < 19 := by unfold RPF at hc; omega
        rw [hvd f j hf htest, ite_eq_right (fun hh => ⋄)]
      have e8 := hs 8 (⊛) (by unfold RPF; omega) j htest
      have e9 := hs 9 (⊛) (by unfold RPF; omega) j htest
      have e4 := hs 4 (⊛) (by unfold RPF; omega) j htest
      have e13 := heC 13 (by unfold RPF; omega)
      have e14 := heC 14 (by unfold RPF; omega)
      have e15 := heC 15 (by unfold RPF; omega)
      have hcard := card_filter_succ (fun r => SingAt c.nmem A R r) j
      have hcnt : ((Finset.range j).filter (fun r => SingAt c.nmem A R r)).card ≤ j := by
        have := Finset.card_filter_le (Finset.range j) (fun r => SingAt c.nmem A R r)
        rw [Finset.card_range] at this; exact this
      obtain ⟨d', k', e', hk', hf'', h20', h23'', hv''⟩ := rpBody_exec (P := P) hwd hRd hAW hjdef
        htest (by rw [e8, e13, e9]; exact hb j htest) (by rw [e8, e13, e9, e15, e14]; exact hcp j htest)
        (by rw [e8, e4]; exact hp j htest) (by rw [h23d]; omega)
      have hsing : SingAt d.nmem A R j ↔ SingAt c.nmem A R j := by
        unfold SingAt; rw [e8, e13, e9]
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', ⋄, ?_, fun f u hf hu => ?_⟩,
        by rw [h20', hjdef]; omega⟩
      · rw [h23'', h20', h23d, hcard]; simp only [hsing]; omega
      · rw [hv'' f u hf hu, h20', rpv_congr htest hs heC (by rw [e8, e13, e9]; exact hb j htest)
          (by rw [e8, e4]; exact hp j htest) f hf]
        by_cases hue : u = j
        · subst hue
          by_cases hc : RPF f
          · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left ⟨⋄, hc⟩]
          · rw [ite_eq_right (fun hh => hc hh.2), ite_eq_right (fun hh => hc hh.2), hvd f u hf hu,
              ite_eq_right (fun hh => hc hh.2)]
        · Ξ ite_eq_right (fun hh => hue hh.1), hvd f u hf hu
          have hiff : (u < j ↔ u < j + 1) := ⋄
          simp only [hiff])
    ⟨hw1, hf1, by simp only [hc1]; config_simp; omega, by
      simp only [hc1]; config_simp; simp, fun f u hf hu => by
      simp only [hc1]; config_simp; rw [ite_eq_right (fun hh => ⋄)]⟩
  have hR' := hR.frame hf'
  rw [hR'.rR] at htest
  have hjR : c'.nreg 60020 = R := ⋄
  have h0 : c1.nreg 60020 = 0 := by simp only [hc1]; config_simp
  rw [h0] at hk
  refine ⟨c', k, e, ⋄, hw', hf', by rw [h23', hjR], fun f u hf hu => ?_⟩
  Ξ hv' f u hf hu, hjR
  by_cases hc : RPF f
  · Ξ ite_eq_left ⟨hu, hc⟩, ite_eq_left hc
  · Ξ ite_eq_right (fun hh => hc hh.2), ite_eq_right hc

end rpram

end

end Chazelle.Core.DecR
