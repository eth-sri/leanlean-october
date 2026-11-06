module

public import Chazelle.Core.NFDecompRamP2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
public import Chazelle.ConfigTactics

/-!
# Tree decomposition (WP-C), part 17: the chord pass on the RAM

* `tv`: the truncated field view (`0` from `R` on), so that memories agreeing on the fields give
  equal states; `rsOf`: the round state held in memory;
* `codeS_exec`: the code of a component;
* `cpS_exec`: the chord pass writes the fields `rem`, `pend`, `dpar`, `dlo`, `dhi` of `next`.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

/-- The truncated field view. -/
def tv (m : ℕ → ℕ) (A R f : ℕ) : ℕ → ℕ := fun j => if j < R then fv m A R f j else 0

theorem tv_lt {m : ℕ → ℕ} {A R f j : ℕ} (hj : j < R) : tv m A R f j = fv m A R f j := by
  unfold tv; rw [ite_eq_left hj]

/-- The round state held in memory (root and finished count from registers). -/
def rsOf (m : ℕ → ℕ) (A R root fin : ℕ) : RS :=
  ⟨tv m A R 11, tv m A R 12, tv m A R 13, tv m A R 14, tv m A R 15, tv m A R 16, tv m A R 17,
    tv m A R 18, tv m A R 0, root, fin⟩

section cpram

variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}

/-- **The code of a component** with top `x` (in register `xr`). -/
theorem codeS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {d xr x : ℕ} (hd : d ≠ 60030 ∧ d ≠ 60051 ∧ d ≠ 60052 ∧ d ≠ 60011)
    (hxr : xr ≠ 60030 ∧ xr ≠ 60051 ∧ xr ≠ 60052 ∧ xr ≠ d)
    (h : c.nreg xr = x) (hx : x < R) (hb : fv c.nmem A R 9 x < R)
    (hp : fv c.nmem A R 9 x ≠ x → fv c.nmem A R 4 (fv c.nmem A R 9 x) < R) :
    ∃ c' k, Exec P W (codeS d xr) c c' k ∧ k ≤ 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60051, 60052, d] c c' ∧ c'.nreg d = code (tv c.nmem A R 9) (tv c.nmem A R 4) x := by
  have b9 := hR.b 9 (by norm_num); have b4 := hR.b 4 (by norm_num)
  simp only [Nat.reduceAdd] at b9 b4
  unfold codeS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r51⟩ := ldF_rel (P := P) hw 60051 9 xr
    (by rwo [show fb 9 = 60109 from rfl, b9, h])
  rw [show fb 9 = 60109 from rfl, b9, h] at r51
  have r51' : c1.nreg 60051 = fv c.nmem A R 9 x := r51
  have hxr1 : c1.nreg xr = x := by rw [s1.1 _ (by sio), h]
  have hR1 : DRegs A R K CB RB LB c1 := hR.of_same s1 (by simp [Prot])
  refine spec_seq ⟨c1, 2, e1, ?_⟩
  unfold code
  rw [tv_lt hx]
  by_cases hbx : fv c.nmem A R 9 x = x
  · refine ifEqN_eq (by rw [r51', hxr1, hbx]) ?_
    rw [ite_eq_left hbx]
    have hw1 := e1.wb_right
    clear hw
    exec_block
    · rwo [hxr1]
    · config_simp; rwo [Machine.upd_other _ _ _ (Ne.symm hd.2.2.2), hxr1, hR1.one]
    · refine ⟨by omega, by rw [m1], ?_, ?_⟩
      · refine (s1.mono (by simp)).trans ?_
        exact ⟨fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          config_simp; rw [Machine.upd_other _ _ _ hy.2.2.2], rfl, rfl, rfl⟩
      · config_simp; rwring [Machine.upd_other _ _ _ (Ne.symm hd.2.2.2), hxr1, hR1.one]
  · refine ifEqN_ne (by rwx [r51', hxr1]) ?_
    rw [ite_eq_right hbx]
    have hpx := hp hbx
    obtain ⟨c2, k2, e2, rfl, m2, s2, r52⟩ := ldF_rel (P := P) e1.wb_right 60052 4 60051
      (by rwo [show fb 4 = 60104 from rfl, hR1.b 4 (by norm_num), r51'])
    rw [show fb 4 = 60104 from rfl, hR1.b 4 (by norm_num), r51', m1] at r52
    refine spec_seq ⟨c2, 2, e2, ?_⟩
    have hw2 := e2.wb_right
    refine spec_instr (Exec.addN hw2 _ _ _ (by ruo [r52] fv at hpx ⊢)) fun _ => ?_
    intro k' hk'
    refine ⟨by omega, by rw [m2, m1], ?_, ?_⟩
    · refine ((s1.mono (by simp)).trans (s2.mono (by simp))).trans ?_
      exact Same.upd1 (by simp)
    · config_simp; rw [r52, tv_lt hb]; ufring fv

/-- The facts on the fields the chord pass relies on. -/
structure CPFacts (m : ℕ → ℕ) (A R K : ℕ) : Prop where
  hKR : K < R
  chOf : ∀ e, e < K → fv m A R 6 e < R ∧ fv m A R 6 e ≠ 0 ∧ fv m A R 3 (fv m A R 6 e) < R
  topR : ∀ u, u < R → fv m A R 8 u < R
  topTop : ∀ u, u < R → fv m A R 8 (fv m A R 8 u) = fv m A R 8 u
  best : ∀ x, x < R → fv m A R 8 x = x →
    fv m A R 9 x < R ∧ (fv m A R 9 x ≠ x → fv m A R 4 (fv m A R 9 x) < R)
  cpar : ∀ t, t < R → fv m A R 8 t = t → fv m A R 13 t = 1 → fv m A R 15 t ≠ 2 →
    fv m A R 14 t < R

/-- **Filling the slots** of chord `e` (in `60020`) cut in the previous round. -/
theorem fillS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K) (hpend : fv c.nmem A R 12 e = 1)
    (hpt : fv c.nmem A R 8 (fv c.nmem A R 6 e) = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W fillS c c' k ∧ k ≤ 50 ∧
      Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = e ∧ f = 12 then 0
        else if u = e ∧ f = 18 then code (tv c.nmem A R 9) (tv c.nmem A R 4)
          (hiTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e)
        else if u = e ∧ f = 17 then code (tv c.nmem A R 9) (tv c.nmem A R 4)
          (loTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e)
        else fv c.nmem A R f u := by
  have hKR := hF.hKR
  have heR : e < R := by omega
  obtain ⟨hc1, hc2, hc3⟩ := hF.chOf e he
  set ch := fv c.nmem A R 6 e with hchdef
  set pc := fv c.nmem A R 3 ch with hpcdef
  set tp := fv c.nmem A R 8 pc with htpdef
  have htpR  := hF.topR pc hc3
  have hchTop  := hpt
  have htpTop  := hF.topTop pc hc3
  unfold fillS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r53⟩ := ldF_rel (P := P) hw 60053 6 60020
    (by rwo [show fb 6 = 60106 from rfl, hR.b 6 (by norm_num), h20])
  rw [show fb 6 = 60106 from rfl, hR.b 6 (by norm_num), h20] at r53
  change c1.nreg 60053 = ch at r53
  have hR1 := hR.of_same s1 (by simp [Prot])
  obtain ⟨c2, k2, e2, rfl, m2, s2, r54⟩ := ldF_rel (P := P) e1.wb_right 60054 3 60053
    (by rwo [show fb 3 = 60103 from rfl, hR1.b 3 (by norm_num), r53])
  rw [show fb 3 = 60103 from rfl, hR1.b 3 (by norm_num), r53, m1] at r54
  change c2.nreg 60054 = pc at r54
  have hR2 := hR1.of_same s2 (by simp [Prot])
  obtain ⟨c3, k3, e3, rfl, m3, s3, r55⟩ := ldF_rel (P := P) e2.wb_right 60055 8 60054
    (by rwo [show fb 8 = 60108 from rfl, hR2.b 8 (by norm_num), r54])
  rw [show fb 8 = 60108 from rfl, hR2.b 8 (by norm_num), r54, m2, m1] at r55
  change c3.nreg 60055 = tp at r55
  have hR3 := hR2.of_same s3 (by simp [Prot])
  obtain ⟨c4, k4, e4, rfl, m4, s4, r56⟩ := ldF_rel (P := P) e3.wb_right 60056 5 60053
    (by rw [show fb 5 = 60105 from rfl, hR3.b 5 (by norm_num), s3.1 _ (by simp), s2.1 _ (by simp), r53]
        omega)
  rw [show fb 5 = 60105 from rfl, hR3.b 5 (by norm_num), s3.1 _ (by simp), s2.1 _ (by simp), r53,
    m3, m2, m1] at r56
  have hR4 := hR3.of_same s4 (by simp [Prot])
  have m14 : c4.nmem = c.nmem := by rw [m4, m3, m2, m1]
  have s14 : Same [60030, 60053, 60054, 60055, 60056] c c4 :=
    (((s1.mono (by simp)).trans (s2.mono (by simp))).trans (s3.mono (by simp))).trans (s4.mono (by simp))
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, spec_seq ⟨c4, 2, e4, ?_⟩⟩⟩⟩
  -- the low and high tops
  set lo := loTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e with hlodef
  set hi := hiTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e with hhidef
  have hlo : lo = if fv c.nmem A R 5 ch = 1 then ch else tp := by
    rw [hlodef]; unfold loTop; rw [tv_lt heR, tv_lt hc1, tv_lt hc1, tv_lt hc3]
  have hhi : hi = if fv c.nmem A R 5 ch = 1 then tp else ch := by
    rw [hhidef]; unfold hiTop; rw [tv_lt heR, tv_lt hc1, tv_lt hc1, tv_lt hc3]
  obtain ⟨c5, k5, e5, hk5, hc5⟩ : ∃ c5 k5, Exec P W (ifEqN 60056 60011
      (block [.copyN 60057 60053, .copyN 60058 60055])
      (block [.copyN 60057 60055, .copyN 60058 60053])) c4 c5 k5 ∧ k5 ≤ 6 ∧
      c5 = { c4 with nreg := upd (upd c4.nreg 60057 lo) 60058 hi } := by
    have r53' : c4.nreg 60053 = ch := by rw [s4.1 _ (by simp), s3.1 _ (by simp), s2.1 _ (by simp), r53]
    have r55' : c4.nreg 60055 = tp := by rw [s4.1 _ (by simp), r55]
    have hw4 := e4.wb_right
    clear hw
    by_cases hd : fv c.nmem A R 5 ch = 1
    · refine ifEqN_eq (by rwx [r56, hR4.one]) ?_
      exec_block
      refine ⟨by omega, ?_⟩
      rw [hlo, hhi, ite_eq_left hd, ite_eq_left hd, r53', r55']
    · refine ifEqN_ne (by rwx [r56, hR4.one]) ?_
      exec_block
      intro k' hk'
      refine ⟨by omega, ?_⟩
      rw [hlo, hhi, ite_eq_right hd, ite_eq_right hd, r53', r55']
  subst hc5
  have hw5 := e5.wb_right
  set c5 := { c4 with nreg := upd (upd c4.nreg 60057 lo) 60058 hi } with hc5def
  have s45 : Same [60057, 60058] c4 c5 := by rw [hc5def]; same_tac
  have hR5 := hR4.of_same s45 (by simp [Prot])
  have hloR : lo < R ∧ fv c.nmem A R 8 lo = lo := by
    rw [hlo]; split_ifs
    · exact ⟨hc1, hchTop⟩
    · exact ⟨htpR, htpTop⟩
  have hhiR : hi < R ∧ fv c.nmem A R 8 hi = hi := by
    rw [hhi]; split_ifs
    · exact ⟨htpR, htpTop⟩
    · exact ⟨hc1, hchTop⟩
  obtain ⟨blo1, blo2⟩ := hF.best lo hloR.1 hloR.2
  obtain ⟨bhi1, bhi2⟩ := hF.best hi hhiR.1 hhiR.2
  obtain ⟨c6, k6, e6, hk6, m6, s6, r59⟩ := codeS_exec (P := P) hw5 hR5 hAW (d := 60059) (xr := 60057)
    (x := lo) (by decide) (by decide) (by rw [hc5def]; config_simp)
    hloR.1 (by rw [hc5def]; config_simp; rw [m14]; exact blo1)
    (by rw [hc5def]; config_simp; rw [m14]; exact blo2)
  rw [hc5def] at r59; simp only [m14] at r59
  have hR6 := hR5.of_same s6 (by simp [Prot])
  obtain ⟨c7, k7, e7, hk7, m7, s7, r60⟩ := codeS_exec (P := P) e6.wb_right hR6 hAW (d := 60060)
    (xr := 60058) (x := hi) (by decide) (by decide)
    (by rw [s6.1 _ (by simp), hc5def]; config_simp)
    hhiR.1 (by rw [m6, hc5def]; config_simp; rw [m14]; exact bhi1)
    (by rw [m6, hc5def]; config_simp; rw [m14]; exact bhi2)
  rw [m6, hc5def] at r60; simp only [m14] at r60
  have hR7 := hR6.of_same s7 (by simp [Prot])
  have m17 : c7.nmem = c.nmem := by rwx [m7, m6, hc5def]
  have s17 : Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052] c c7 :=
    (((s14.mono (by simp)).trans (s45.mono (by simp))).trans (s6.mono (by simp))).trans (s7.mono (by simp))
  have r20 : c7.nreg 60020 = e := by rw [s17.1 _ (by simp), h20]
  have r59' : c7.nreg 60059 = code (tv c.nmem A R 9) (tv c.nmem A R 4) lo := by
    rw [s7.1 _ (by simp), r59]
  have hcodeR : ∀ x, x < R → fv c.nmem A R 8 x = x →
      code (tv c.nmem A R 9) (tv c.nmem A R 4) x ≤ 2 * R + 1 := by
    intro x hx htx
    obtain ⟨b1, b2⟩ := hF.best x hx htx
    unfold code; rw [tv_lt hx]
    split_ifs with hb
    · omega
    · rw [tv_lt b1]; have := b2 hb; omega
  refine spec_seq ⟨c5, k5, e5, spec_seq ⟨c6, k6, e6, spec_seq ⟨c7, k7, e7, ?_⟩⟩⟩
  obtain ⟨c8, k8, e8, rfl, m8, s8⟩ := stF_rel (P := P) e7.wb_right 17 60020 60059 (by decide)
    (by rwo [show fb 17 = 60117 from rfl, hR7.b 17 (by norm_num), r20])
  have hR8 := hR7.of_same s8 (by simp [Prot])
  obtain ⟨c9, k9, e9, rfl, m9, s9⟩ := stF_rel (P := P) e8.wb_right 18 60020 60060 (by decide)
    (by rwo [show fb 18 = 60118 from rfl, hR8.b 18 (by norm_num), s8.1 _ (by simp), r20])
  have hR9 := hR8.of_same s9 (by simp [Prot])
  obtain ⟨c10, k10, e10, rfl, m10, s10⟩ := stF_rel (P := P) e9.wb_right 12 60020 60010 (by decide)
    (by rw [show fb 12 = 60112 from rfl, hR9.b 12 (by norm_num), s9.1 _ (by simp), s8.1 _ (by simp), r20]
        omega)
  refine spec_seq ⟨_, 2, e8, spec_seq ⟨_, 2, e9, ⟨_, 2, e10, ?_⟩⟩⟩
  have r20' : ∀ d : Config, Same [60030] c7 d → d.nreg 60020 = e := fun d hs => by
    rw [hs.1 _ (by simp), r20]
  refine ⟨by omega, s17.trans (((s8.trans s9).trans s10).mono (by simp)), fun a ha => ?_,
    fun f u hf hu => ?_⟩
  · rw [m10, m9, m8]
    simp only [show fb 17 = 60117 from rfl, show fb 18 = 60118 from rfl,
      show fb 12 = 60112 from rfl, hR7.b 17 (by norm_num), hR8.b 18 (by norm_num),
      hR9.b 12 (by norm_num), s9.1 60020 (by simp), s8.1 60020 (by simp), r20]
    rw [fv_store_out (by norm_num) heR ha, fv_store_out (by norm_num) heR ha,
      fv_store_out (by norm_num) heR ha, m17]
  · rw [m10, m9, m8]
    simp only [show fb 17 = 60117 from rfl, show fb 18 = 60118 from rfl,
      show fb 12 = 60112 from rfl, hR7.b 17 (by norm_num), hR8.b 18 (by norm_num),
      hR9.b 12 (by norm_num), s9.1 60020 (by simp), s8.1 60020 (by simp), r20]
    rw [fv_store heR hu, fv_store heR hu, fv_store heR hu, m17]
    rw [s8.1 60060 (by simp),
      s9.1 60010 (by simp), s8.1 60010 (by simp), s17.1 60010 (by simp), hR.zero, r59']
    have r60'  := r60
    rw [r60']
    by_cases hue : u = e
    · subst hue
      rcases (show f = 12 ∨ f = 17 ∨ f = 18 ∨ (f ≠ 12 ∧ f ≠ 17 ∧ f ≠ 18) by omega) with
        h | h | h | ⟨h1, h2, h3⟩
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · simp [h1, h2, h3]
    · simp [hue]

/-- **Cutting the chord** `e` if it is the chosen chord of its component. -/
theorem chkS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K) :
    ∃ c' k, Exec P W chkS c c' k ∧ k ≤ 40 ∧
      Same [60030, 60053, 60055, 60064, 60065, 60061, 60062, 60063] c c' ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c'.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if fv c.nmem A R 13 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = 1 ∧
          fv c.nmem A R 9 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = fv c.nmem A R 6 e ∧ u = e ∧
          (f = 11 ∨ f = 12 ∨ f = 16) then
          (if f = 16 then
            (if fv c.nmem A R 15 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = 2 then 2 * e
              else 2 * fv c.nmem A R 14 (fv c.nmem A R 8 (fv c.nmem A R 6 e)))
           else 1)
        else fv c.nmem A R f u := by
  have hKR := hF.hKR
  have heR : e < R := by omega
  obtain ⟨hc1, hc2, hc3⟩ := hF.chOf e he
  set ch := fv c.nmem A R 6 e with hchdef
  set t := fv c.nmem A R 8 ch with htdef
  have htR : t < R := hF.topR ch hc1
  have htt : fv c.nmem A R 8 t = t := hF.topTop ch hc1
  unfold chkS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r53⟩ := ldF_rel (P := P) hw 60053 6 60020
    (by rwo [show fb 6 = 60106 from rfl, hR.b 6 (by norm_num), h20])
  rw [show fb 6 = 60106 from rfl, hR.b 6 (by norm_num), h20] at r53
  change c1.nreg 60053 = ch at r53
  have hR1 := hR.of_same s1 (by simp [Prot])
  obtain ⟨c2, k2, e2, rfl, m2, s2, r55⟩ := ldF_rel (P := P) e1.wb_right 60055 8 60053
    (by rwo [show fb 8 = 60108 from rfl, hR1.b 8 (by norm_num), r53])
  rw [show fb 8 = 60108 from rfl, hR1.b 8 (by norm_num), r53, m1] at r55
  change c2.nreg 60055 = t at r55
  have hR2 := hR1.of_same s2 (by simp [Prot])
  obtain ⟨c3, k3, e3, rfl, m3, s3, r64⟩ := ldF_rel (P := P) e2.wb_right 60064 13 60055
    (by rwo [show fb 13 = 60113 from rfl, hR2.b 13 (by norm_num), r55])
  rw [show fb 13 = 60113 from rfl, hR2.b 13 (by norm_num), r55, m2, m1] at r64
  have hR3 := hR2.of_same s3 (by simp [Prot])
  have m13 : c3.nmem = c.nmem := by rw [m3, m2, m1]
  have s13 : Same [60030, 60053, 60055, 60064] c c3 :=
    ((s1.mono (by simp)).trans (s2.mono (by simp))).trans (s3.mono (by simp))
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩⟩
  by_cases hact : fv c.nmem A R 13 t = 1
  · refine ifEqN_eq (by rwx [r64, hR3.one]) ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4, r65⟩ := ldF_rel (P := P) e3.wb_right 60065 9 60055
      (by rwo [show fb 9 = 60109 from rfl, hR3.b 9 (by norm_num), s3.1 _ (by simp), r55])
    rw [show fb 9 = 60109 from rfl, hR3.b 9 (by norm_num), s3.1 _ (by simp), r55, m13] at r65
    have hR4 := hR3.of_same s4 (by simp [Prot])
    have m14 : c4.nmem = c.nmem := by rw [m4, m13]
    have s14 : Same [60030, 60053, 60055, 60064, 60065] c c4 :=
      (s13.mono (by simp)).trans (s4.mono (by simp))
    refine spec_seq ⟨c4, 2, e4, ?_⟩
    have r53' : c4.nreg 60053 = ch := by
      rw [s4.1 _ (by simp), s3.1 _ (by simp), s2.1 _ (by simp), r53]
    by_cases hbest : fv c.nmem A R 9 t = ch
    · refine ifEqN_eq (by rwx [r65, r53']) ?_
      -- cut the chord
      have r20 : c4.nreg 60020 = e := by rw [s14.1 _ (by simp), h20]
      have r55' : c4.nreg 60055 = t := by rw [s4.1 _ (by simp), s3.1 _ (by simp), r55]
      unfold doS
      obtain ⟨c5, k5, e5, rfl, m5, s5⟩ := stF_rel (P := P) e4.wb_right 11 60020 60011 (by decide)
        (by rwo [show fb 11 = 60111 from rfl, hR4.b 11 (by norm_num), r20])
      have hR5 := hR4.of_same s5 (by simp [Prot])
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_rel (P := P) e5.wb_right 12 60020 60011 (by decide)
        (by rwo [show fb 12 = 60112 from rfl, hR5.b 12 (by norm_num), s5.1 _ (by simp), r20])
      have hR6 := hR5.of_same s6 (by simp [Prot])
      have r55'' : c6.nreg 60055 = t := by rw [s6.1 _ (by simp), s5.1 _ (by simp), r55']
      have r20'' : c6.nreg 60020 = e := by rw [s6.1 _ (by simp), s5.1 _ (by simp), r20]
      -- the memory after the two stores
      set m2' := upd (upd c.nmem (A + 12 + 11 * R + e) 1) (A + 12 + 12 * R + e) 1 with hm2'
      have m6' : c6.nmem = m2' := by
        rw [m6, m5, show fb 12 = 60112 from rfl, hR5.b 12 (by norm_num), show fb 11 = 60111 from rfl,
          hR4.b 11 (by norm_num), s5.1 _ (by simp), r20, s5.1 60011 (by simp), hR4.one, m14]
      have hside : fv m2' A R 15 t = fv c.nmem A R 15 t := by
        rws [hm2', fv_store heR htR, fv_store heR htR]
      have hcpar : fv m2' A R 14 t = fv c.nmem A R 14 t := by
        rws [hm2', fv_store heR htR, fv_store heR htR]
      obtain ⟨c7, k7, e7, rfl, m7, s7, r61⟩ := ldF_rel (P := P) e6.wb_right 60061 15 60055
        (by rwo [show fb 15 = 60115 from rfl, hR6.b 15 (by norm_num), r55''])
      rw [show fb 15 = 60115 from rfl, hR6.b 15 (by norm_num), r55'', m6'] at r61
      change c7.nreg 60061 = fv m2' A R 15 t at r61
      rw [hside] at r61
      have hR7 := hR6.of_same s7 (by simp [Prot])
      set y := if fv c.nmem A R 15 t = 2 then 2 * e else 2 * fv c.nmem A R 14 t with hydef
      obtain ⟨c8, k8, e8, hk8, m8, s8, r62⟩ : ∃ c8 k8, Exec P W (ifEqN 60061 60012
          (.instr (.addN 60062 60020 60020))
          (.seq (ldF 60063 14 60055) (.instr (.addN 60062 60063 60063)))) c7 c8 k8 ∧ k8 ≤ 7 ∧
          c8.nmem = c7.nmem ∧ Same [60030, 60062, 60063] c7 c8 ∧ c8.nreg 60062 = y := by
        have r20' : c7.nreg 60020 = e := by rw [s7.1 _ (by simp), r20'']
        by_cases hs2 : fv c.nmem A R 15 t = 2
        · refine ifEqN_eq (by rwx [r61, hR7.two]) ?_
          refine spec_instr (Exec.addN e7.wb_right _ _ _ (by rwo [r20'])) fun _ => ?_
          refine ⟨by omega, rfl, Same.upd1 (by simp), ?_⟩
          config_simp; rwring [r20', hydef, ite_eq_left hs2]
        · refine ifEqN_ne (by rwx [r61, hR7.two]) ?_
          have hcR := hF.cpar t htR htt hact hs2
          obtain ⟨c8, k8, e8, rfl, m8, s8, r63⟩ := ldF_rel (P := P) e7.wb_right 60063 14 60055
            (by rwo [show fb 14 = 60114 from rfl, hR7.b 14 (by norm_num), s7.1 _ (by simp), r55''])
          rw [show fb 14 = 60114 from rfl, hR7.b 14 (by norm_num), s7.1 _ (by simp), r55'', m7, m6'] at r63
          change c8.nreg 60063 = fv m2' A R 14 t at r63
          rw [hcpar] at r63
          refine spec_seq ⟨c8, 2, e8, ?_⟩
          refine spec_instr (Exec.addN e8.wb_right _ _ _ (by ruo [r63] fv at hcR ⊢)) fun _ => ?_
          intro k' hk'
          refine ⟨by omega, m8, (s8.mono (by simp)).trans (Same.upd1 (by simp)), ?_⟩
          config_simp; rwring [r63, hydef, ite_eq_right hs2]
      obtain ⟨c9, k9, e9, rfl, m9, s9⟩ := stF_rel (P := P) e8.wb_right 16 60020 60062 (by decide)
        (by rw [show fb 16 = 60116 from rfl, s8.1 60116 (by simp), s8.1 60020 (by simp),
          hR7.b 16 (by norm_num), s7.1 _ (by simp), r20'']; omega)
      refine spec_seq ⟨_, 2, e5, spec_seq ⟨_, 2, e6, spec_seq ⟨c7, 2, e7, spec_seq ⟨c8, k8, e8,
        ⟨_, 2, e9, ?_⟩⟩⟩⟩⟩
      have s19 : Same [60030, 60053, 60055, 60064, 60065, 60061, 60062, 60063] c c9 :=
        (((((s14.mono (by simp)).trans (s5.mono (by simp))).trans (s6.mono (by simp))).trans
          (s7.mono (by simp))).trans (s8.mono (by simp))).trans (s9.mono (by simp))
      have m9' : c9.nmem = upd m2' (A + 12 + 16 * R + e) y := by
        rw [m9, m8, m7, m6', show fb 16 = 60116 from rfl, s8.1 60116 (by simp), s8.1 60020 (by simp),
          hR7.b 16 (by norm_num), s7.1 60020 (by simp), r20'', r62]
      refine ⟨by omega, s19, fun a ha => ?_, fun f u hf hu => ?_⟩
      · rw [m9', hm2', fv_store_out (by norm_num) heR ha, fv_store_out (by norm_num) heR ha,
          fv_store_out (by norm_num) heR ha]
      · rw [m9', hm2', fv_store heR hu, fv_store heR hu, fv_store heR hu]
        by_cases hue : u = e
        · subst hue
          rcases (show f = 11 ∨ f = 12 ∨ f = 16 ∨ (f ≠ 11 ∧ f ≠ 12 ∧ f ≠ 16) by omega) with
            h | h | h | ⟨h1, h2, h3⟩
          · subst h; simp [hact, hbest]
          · subst h; simp [hact, hbest]
          · subst h; simp [hact, hbest, hydef]
          · simp [h1, h2, h3]
        · simp [hue]
    · refine ifEqN_ne (by rwx [r65, r53']) (spec_skip e4.wb_right ?_)
      intro k' hk'
      refine ⟨by omega, s14.mono (by simp), fun a _ => by rw [m14], fun f u _ _ => ?_⟩
      rw [m14, ite_eq_right (fun hh => hbest hh.2.1)]
  · refine ifEqN_ne (by rwx [r64, hR3.one]) (spec_skip e3.wb_right ?_)
    intro k' hk'
    refine ⟨by omega, s13.mono (by simp), fun a _ => by rw [m13], fun f u _ _ => ?_⟩
    rw [m13, ite_eq_right (fun hh => hact hh.1)]

/-- The round `next` computed from the state held in memory. -/
def nxt (m : ℕ → ℕ) (A R K : ℕ) : RS :=
  next R K (tv m A R 3) (tv m A R 4) (tv m A R 5) (tv m A R 6) (tv m A R 8) (tv m A R 9)
    (rsOf m A R 0 0)

/-- The fields written by the chord pass, with their new values at `e`. -/
def cpv (m : ℕ → ℕ) (A R K f e : ℕ) : ℕ :=
  if f = 11 then (nxt m A R K).rem e else if f = 12 then (nxt m A R K).pend e
  else if f = 16 then (nxt m A R K).dpar e else if f = 17 then (nxt m A R K).dlo e
  else (nxt m A R K).dhi e

/-- The fields of the chord pass. -/
def CPF (f : ℕ) : Prop := f = 11 ∨ f = 12 ∨ f = 16 ∨ f = 17 ∨ f = 18

instance (f : ℕ) : Decidable (CPF f) := inferInstanceAs (Decidable (_ ∨ _))

/-- **One step of the chord pass.** -/
theorem cpBody_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K)
    (hpt : fv c.nmem A R 12 e = 1 → fv c.nmem A R 8 (fv c.nmem A R 6 e) = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W cpBody c c' k ∧ k ≤ 62 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60020 = e + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = e ∧ CPF f then cpv c.nmem A R K f e else fv c.nmem A R f u := by
  have hKR := hF.hKR
  have heR : e < R := by omega
  obtain ⟨hc1, hc2, hc3⟩ := hF.chOf e he
  have htR := hF.topR _ hc1
  -- the next values at `e`
  have hN : ∀ f, CPF f → cpv c.nmem A R K f e =
      (if fv c.nmem A R 12 e = 1 then
        (if f = 12 then 0
         else if f = 17 then code (tv c.nmem A R 9) (tv c.nmem A R 4)
           (loTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e)
         else if f = 18 then code (tv c.nmem A R 9) (tv c.nmem A R 4)
           (hiTop (tv c.nmem A R 3) (tv c.nmem A R 5) (tv c.nmem A R 6) (tv c.nmem A R 8) e)
         else fv c.nmem A R f e)
      else if fv c.nmem A R 11 e ≠ 1 ∧
          fv c.nmem A R 13 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = 1 ∧
          fv c.nmem A R 9 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = fv c.nmem A R 6 e ∧
          (f = 11 ∨ f = 12 ∨ f = 16) then
        (if f = 16 then
          (if fv c.nmem A R 15 (fv c.nmem A R 8 (fv c.nmem A R 6 e)) = 2 then 2 * e
            else 2 * fv c.nmem A R 14 (fv c.nmem A R 8 (fv c.nmem A R 6 e)))
         else 1)
      else fv c.nmem A R f e) := by
    intro f hf
    have ht := tv_lt (m := c.nmem) (A := A) (f := 8) hc1
    have hc := tv_lt (m := c.nmem) (A := A) (f := 6) heR
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp only [cpv, nxt, next, nPend, rsOf, Chosen, ite_eq_left he, hc, ht, tv_lt heR, tv_lt htR] <;> norm_num
  unfold cpBody
  obtain ⟨c1, k1, e1, rfl, m1, s1, r66⟩ := ldF_rel (P := P) hw 60066 12 60020
    (by rwo [show fb 12 = 60112 from rfl, hR.b 12 (by norm_num), h20])
  rw [show fb 12 = 60112 from rfl, hR.b 12 (by norm_num), h20] at r66
  change c1.nreg 60066 = fv c.nmem A R 12 e at r66
  have hR1 := hR.of_same s1 (by simp [Prot])
  have hF1 : CPFacts c1.nmem A R K := by rwx [m1]
  have r20 : c1.nreg 60020 = e := by rw [s1.1 _ (by simp), h20]
  -- the middle, with its effect
  have hmid : ∃ c2 k2, Exec P W (ifEqN 60066 60011 fillS
        (.seq (ldF 60067 11 60020) (ifEqN 60067 60011 .skip chkS))) c1 c2 k2 ∧ k2 ≤ 56 ∧
      Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052, 60067,
        60064, 60065, 60061, 60062, 60063] c1 c2 ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c2.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        if u = e ∧ CPF f then cpv c.nmem A R K f e else fv c.nmem A R f u := by
    by_cases hp : fv c.nmem A R 12 e = 1
    · refine ifEqN_eq (by rwx [r66, hR1.one]) ?_
      obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := fillS_exec (P := P) e1.wb_right hR1 hAW hF1 r20 he
        (by rwx [m1]) (by rw [m1]; exact hpt hp)
      refine ⟨c2, k2, e2, by omega, s2.mono (by simp), fun a ha => by rw [hm2 a ha, m1],
        fun f u hf hu => ?_⟩
      rw [hv2 f u hf hu, m1]
      by_cases hue : u = e
      · subst hue
        by_cases hcf : CPF f
        · rw [show (if u = u ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u) =
              cpv c.nmem A R K f u from ite_eq_left ⟨rfl, hcf⟩, hN f hcf, ite_eq_left hp]
          rcases hcf with rfl | rfl | rfl | rfl | rfl <;> simp
        · have : f ≠ 11 ∧ f ≠ 12 ∧ f ≠ 16 ∧ f ≠ 17 ∧ f ≠ 18 := by ufo CPF at hcf
          simp [this, hcf]
      · simp [hue]
    · refine ifEqN_ne (by rwx [r66, hR1.one]) ?_
      obtain ⟨c2, k2, e2, rfl, m2, s2, r67⟩ := ldF_rel (P := P) e1.wb_right 60067 11 60020
        (by rwo [show fb 11 = 60111 from rfl, hR1.b 11 (by norm_num), r20])
      rw [show fb 11 = 60111 from rfl, hR1.b 11 (by norm_num), r20, m1] at r67
      change c2.nreg 60067 = fv c.nmem A R 11 e at r67
      have hR2 := hR1.of_same s2 (by simp [Prot])
      have m12 : c2.nmem = c.nmem := by rw [m2, m1]
      refine spec_seq ⟨c2, 2, e2, ?_⟩
      by_cases hr : fv c.nmem A R 11 e = 1
      · refine ifEqN_eq (by rwx [r67, hR2.one]) (spec_skip e2.wb_right ?_)
        intro k' hk'
        refine ⟨by omega, s2.mono (by simp), fun a _ => by rw [m12], fun f u hf hu => ?_⟩
        rw [m12]
        by_cases hue : u = e
        · subst hue
          by_cases hcf : CPF f
          · rw [ite_eq_left ⟨rfl, hcf⟩, hN f hcf, ite_eq_right hp,
              ite_eq_right (fun hh => hh.1 hr)]
          · rw [ite_eq_right (fun hh => hcf hh.2)]
        · rw [ite_eq_right (fun hh => hue hh.1)]
      · refine ifEqN_ne (by rwx [r67, hR2.one]) ?_
        have hF2 : CPFacts c2.nmem A R K := by rwx [m12]
        obtain ⟨c3, k3, e3, hk3, s3, hm3, hv3⟩ := chkS_exec (P := P) e2.wb_right hR2 hAW hF2
          (by rw [s2.1 _ (by simp), r20]) he
        refine ⟨c3, k3, e3, fun k' hk' => fun k'' hk'' => ⟨by omega,
          (s2.mono (by simp)).trans (s3.mono (by simp)), fun a ha => by rw [hm3 a ha, m12],
          fun f u hf hu => ?_⟩⟩
        rw [hv3 f u hf hu, m12]
        by_cases hue : u = e
        · subst hue
          by_cases hcf : CPF f
          · rw [show (if u = u ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u) =
              cpv c.nmem A R K f u from ite_eq_left ⟨rfl, hcf⟩, hN f hcf, ite_eq_right hp]
            by_cases hch : fv c.nmem A R 13 (fv c.nmem A R 8 (fv c.nmem A R 6 u)) = 1 ∧
                fv c.nmem A R 9 (fv c.nmem A R 8 (fv c.nmem A R 6 u)) = fv c.nmem A R 6 u
            · rcases hcf with rfl | rfl | rfl | rfl | rfl <;> simp [hch, hr]
            · rcases hcf with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp_all
          · have : ¬ (f = 11 ∨ f = 12 ∨ f = 16) := fun hh => hcf (by ufo CPF)
            rw [ite_eq_right (fun hh => this hh.2.2.2), ite_eq_right (fun hh => hcf hh.2)]
        · rw [ite_eq_right (fun hh => hue hh.2.2.1), ite_eq_right (fun hh => hue hh.1)]
  obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := hmid
  have hR2 := hR1.of_same s2 (by simp [Prot])
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20'⟩ := incr_exec (P := P) e2.wb_right hR2.one
    (by rwo [s2.1 _ (by simp), r20])
  refine ⟨c3, 2 + (k2 + 1), .seq e1 (.seq e2 e3), by omega, ?_, by
    rw [r20', s2.1 _ (by simp), r20], fun f u hf hu => by rw [m3, hv2 f u hf hu]⟩
  exact DFr.of_same (((s1.mono (l' := [60066, 60030, 60053, 60054, 60055, 60056, 60057, 60058,
    60059, 60060, 60051, 60052, 60067, 60064, 60065, 60061, 60062, 60063, 60020]) (by simp)).trans
    (s2.mono (by simp))).trans (s3.mono (by simp))) (by simp [Prot])
    (fun a ha => by rw [m3, hm2 a ha])

theorem tv_congr {m m' : ℕ → ℕ} {A R f : ℕ} (h : ∀ u, u < R → fv m A R f u = fv m' A R f u) :
    tv m A R f = tv m' A R f := by
  funext j; unfold tv; split_ifs with hj
  · exact h j hj
  · rfl

/-- The new values at `e` depend only on the static fields and the entries at `e`. -/
theorem cpv_congr {m m' : ℕ → ℕ} {e : ℕ} (heR : e < R)
    (hs : ∀ f, f < 19 → ¬ CPF f → ∀ u, u < R → fv m A R f u = fv m' A R f u)
    (he : ∀ f, CPF f → fv m A R f e = fv m' A R f e) (f : ℕ) :
    cpv m A R K f e = cpv m' A R K f e := by
  have t : ∀ f, f < 19 → ¬ CPF f → tv m A R f = tv m' A R f := fun f hf hc => tv_congr (hs f hf hc)
  have t3 := t 3 (by norm_num) (by ufo CPF)
  have t4 := t 4 (by norm_num) (by ufo CPF)
  have t5 := t 5 (by norm_num) (by ufo CPF)
  have t6 := t 6 (by norm_num) (by ufo CPF)
  have t8 := t 8 (by norm_num) (by ufo CPF)
  have t9 := t 9 (by norm_num) (by ufo CPF)
  have t13 := t 13 (by norm_num) (by ufo CPF)
  have t14 := t 14 (by norm_num) (by ufo CPF)
  have t15 := t 15 (by norm_num) (by ufo CPF)
  have t0 := t 0 (by norm_num) (by ufo CPF)
  have e11 := he 11 (by ufo CPF); have e12 := he 12 (by ufo CPF)
  have e16 := he 16 (by ufo CPF); have e17 := he 17 (by ufo CPF)
  have e18 := he 18 (by ufo CPF)
  simp only [cpv, nxt, next, nPend, rsOf, Chosen, t3, t4, t5, t6, t8, t9, t13, t14, t15, t0,
    tv_lt heR, e11, e12, e16, e17, e18]

/-- **The chord pass.** -/
theorem cpS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K)
    (hpt : ∀ e, e < K → fv c.nmem A R 12 e = 1 →
      fv c.nmem A R 8 (fv c.nmem A R 6 e) = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W cpS c c' k ∧ k ≤ 64 * K + 3 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u < K ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u := by
  have hKR := hF.hKR
  unfold cpS
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  set c1 := { c with nreg := upd c.nreg 60020 0 } with hc1
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c c1 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr; rw [Machine.upd_other _ _ _ (by omega)]
  have hstat : ∀ d : Config, (∀ f u, f < 19 → u < R → fv d.nmem A R f u =
      if u < d.nreg 60020 ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u) →
      ∀ f, f < 19 → ¬ CPF f → ∀ u, u < R → fv d.nmem A R f u = fv c.nmem A R f u :=
    fun d hv f hf hc u hu => by rw [hv f u hf hu, ite_eq_right (fun hh => hc hh.2)]
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60014) (body := cpBody)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60020 ≤ K ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u =
        if u < d.nreg 60020 ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u)
    (fun d => 64 * (K - d.nreg 60020)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      have hRd := hR.frame hfd
      rw [hRd.rK] at htest
      obtain ⟨e, hedef⟩ : ∃ e, d.nreg 60020 = e := ⟨_, rfl⟩
      rw [hedef] at htest hjd hvd
      have heR : e < R := by omega
      have hs := hstat d (by rwx [hedef])
      have h6 := hs 6 (by norm_num) (by ufo CPF)
      have h3 := hs 3 (by norm_num) (by ufo CPF)
      have h8 := hs 8 (by norm_num) (by ufo CPF)
      have h9 := hs 9 (by norm_num) (by ufo CPF)
      have h4 := hs 4 (by norm_num) (by ufo CPF)
      have h13 := hs 13 (by norm_num) (by ufo CPF)
      have h14 := hs 14 (by norm_num) (by ufo CPF)
      have h15 := hs 15 (by norm_num) (by ufo CPF)
      have hFd : CPFacts d.nmem A R K := by
        refine ⟨hKR, fun e' he' => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
          fun t ht htt ha hs2 => ?_⟩
        · obtain ⟨a1, a2, a3⟩ := hF.chOf e' he'
          rw [h6 _ (by omega), h3 _ a1]; exact ⟨a1, a2, a3⟩
        · rw [h8 _ hu]; exact hF.topR u hu
        · rw [h8 _ hu, h8 _ (hF.topR u hu)]; exact hF.topTop u hu
        · rw [h8 _ hx] at htx
          obtain ⟨b1, b2⟩ := hF.best x hx htx
          rw [h9 _ hx]; refine ⟨b1, fun hb => ?_⟩; rw [h4 _ b1]; exact b2 hb
        · rw [h8 _ ht] at htt; rw [h13 _ ht] at ha; rw [h15 _ ht] at hs2
          rw [h14 _ ht]; exact hF.cpar t ht htt ha hs2
      have heC : ∀ f, CPF f → fv d.nmem A R f e = fv c.nmem A R f e := fun f hc => by
        have hf : f < 19 := by ufo CPF at hc
        rw [hvd f e hf heR, ite_eq_right (fun hh => by omega)]
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := cpBody_exec (P := P) hwd hRd hAW hFd hedef htest
        (fun hp => by
          rw [heC 12 (by ufo CPF)] at hp
          obtain ⟨a1, -, -⟩ := hF.chOf e htest
          rw [h6 _ heR, h8 _ a1]; exact hpt e htest hp)
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by omega, fun f u hf hu => ?_⟩,
        by rwo [h20', hedef]⟩
      rw [hv'' f u hf hu, h20', cpv_congr heR hs heC]
      by_cases hue : u = e
      · subst hue
        by_cases hc : CPF f
        · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left ⟨by omega, hc⟩]
        · rw [ite_eq_right (fun hh => hc hh.2), ite_eq_right (fun hh => hc hh.2), hvd f u hf hu,
            ite_eq_right (fun hh => hc hh.2)]
      · rw [ite_eq_right (fun hh => hue hh.1), hvd f u hf hu]
        have hiff : (u < e ↔ u < e + 1) := by omega
        simp only [hiff])
    ⟨hw1, hf1, by simp only [hc1]; cso, fun f u hf hu => by
      simp only [hc1]; config_simp; rw [ite_eq_right (fun hh => by omega)]⟩
  have hR' := hR.frame hf'
  rw [hR'.rK] at htest
  have hjK : c'.nreg 60020 = K := by omega
  have h0 : c1.nreg 60020 = 0 := by simp only [hc1]; config_simp
  rw [h0] at hk
  refine ⟨c', k, e, by omega, hw', hf', fun f u hf hu => ?_⟩
  rw [hv' f u hf hu, hjK]

end cpram

end

end Chazelle.Core.DecR
