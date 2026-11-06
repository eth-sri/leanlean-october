module

public import Chazelle.Core.Lemma41Cover
public import Chazelle.Programs.Tactics

/-!
# WP-J, part 6: the greedy grade on the RAM

`ascS`: from `g = 0`, `q = x`, raise `g` while `g + 1 < λ`, `q` is even (read `q / 2` from the
halving table) and `x + 2^(g+1) ≤ b` (read `2^(g+1)` from the power table). It ends with
`g = nextG λ b x` and `q = x / 2^g` (`ascS_exec`).

Registers (band `bL41 = 16`): `160010` x, `160011` b, `160012` g, `160013` q, `160016`–`160019`
scratch, `160020` halving table base, `160021` power table base, `160024` the constant `1`,
`160025` the loop flag, `160026` λ.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Arithmetic of the ascending search -/

theorem dvd_succ_iff {x g : ℕ} (h : 2 ^ g ∣ x) : 2 ^ (g + 1) ∣ x ↔ (x / 2 ^ g) % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ (by positivity), pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)]
  exact Nat.dvd_iff_mod_eq_zero

theorem div_succ (x g : ℕ) : x / 2 ^ (g + 1) = x / 2 ^ g / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- If `g` satisfies the grade condition but `g + 1` does not (or is out of range), `g` is the
greedy grade. -/
theorem nextG_eq_of {lam b x g : ℕ} (hg : g ≤ lam - 1) (hok : GradeOK b x g)
    (hno : g + 1 ≤ lam - 1 → ¬ GradeOK b x (g + 1)) : nextG lam b x = g := by
  apply le_antisymm
  · by_contra hc
    push Not at hc
    have hx : x < b := by have := hok.2; have := Nat.one_le_two_pow (n := g); omega
    exact hno (by have := nextG_le lam b x; omega)
      (gradeOK_mono (nextG_spec (lam := lam) hx) hc)
  · exact le_nextG hg hok

/-! ## The program -/

/-- One step of the ascending search. -/
def ascBody : Stmt := .seq (.instr (.addN 160016 160012 160024))
  (.ifLtN 160016 160026
    (.seq (block [.addN 160017 160020 160013, .loadN 160017 160017, .addN 160018 160017 160017])
      (.ifLtN 160018 160013 (.instr (.constN 160025 1))
        (.seq (block [.addN 160019 160021 160016, .loadN 160019 160019,
            .addN 160019 160010 160019])
          (.ifLtN 160011 160019 (.instr (.constN 160025 1))
            (block [.copyN 160013 160017, .copyN 160012 160016])))))
    (.instr (.constN 160025 1)))

/-- **The greedy grade.** -/
def ascS : Stmt := .seq (block [.constN 160025 0, .constN 160012 0, .copyN 160013 160010])
  (.whileLtN 160025 160024 ascBody)

/-- The registers written by `ascS`. -/
def AscRG (r : ℕ) : Prop := r = 160012 ∨ r = 160013 ∨ (160016 ≤ r ∧ r ≤ 160019) ∨ r = 160025

section proofs

variable {P : Polygon} {W : ℕ}

/-- The state of the ascending search. -/
def AscInv (lam b x : ℕ) (c0 c : Config) : Prop :=
  (∀ r, ¬ AscRG r → c.nreg r = c0.nreg r) ∧ c.nmem = c0.nmem ∧ c.rreg = c0.rreg ∧
    c.rmem = c0.rmem ∧ c.output = c0.output ∧ c.nreg 160012 ≤ lam - 1 ∧
    GradeOK b x (c.nreg 160012) ∧ c.nreg 160013 = x / 2 ^ c.nreg 160012 ∧
    (c.nreg 160025 = 0 ∨ (c.nreg 160025 = 1 ∧ c.nreg 160012 = nextG lam b x))

set_option maxHeartbeats 4000000 in
/-- One step of the ascending search. -/
theorem ascBody_exec {c0 c : Config} (hw : WordsBounded W c) {lam b x D PW : ℕ}
    (h10 : c0.nreg 160010 = x) (h11 : c0.nreg 160011 = b) (h26 : c0.nreg 160026 = lam)
    (h24 : c0.nreg 160024 = 1) (h20 : c0.nreg 160020 = D) (h21 : c0.nreg 160021 = PW)
    (hD : ∀ y, y ≤ b → c0.nmem (D + y) = y / 2)
    (hPW : ∀ i, i ≤ lam → c0.nmem (PW + i) = 2 ^ i)
    (hWD : D + b ≤ W) (hWP : PW + lam ≤ W) (hWx : b + 2 ^ lam ≤ W)
    (hI : AscInv lam b x c0 c) (hf : c.nreg 160025 = 0) :
    ∃ c' k, Exec P W ascBody c c' k ∧ AscInv lam b x c0 c' ∧
      20 * ((lam - c'.nreg 160012) + (1 - c'.nreg 160025)) + k + 2 ≤
        20 * ((lam - c.nreg 160012) + (1 - c.nreg 160025)) := by
  obtain ⟨hr, hm, hrr, hrm, ho, hgl, hok, hq, -⟩ := hI
  have r10 : c.nreg 160010 = x := by rwa [hr _ (by unfold AscRG; omega)]
  have r11 : c.nreg 160011 = b := by rwa [hr _ (by unfold AscRG; omega)]
  have r26 : c.nreg 160026 = lam := by rwa [hr _ (by unfold AscRG; omega)]
  have r24 : c.nreg 160024 = 1 := by rwa [hr _ (by unfold AscRG; omega)]
  have r20 : c.nreg 160020 = D := by rwa [hr _ (by unfold AscRG; omega)]
  have r21 : c.nreg 160021 = PW := by rwa [hr _ (by unfold AscRG; omega)]
  set g := c.nreg 160012
  have hxb : x + 2 ^ g ≤ b := hok.2
  have hqx : x / 2 ^ g ≤ x := Nat.div_le_self _ _
  have hpg := Nat.one_le_two_pow (n := g)
  have hpl : 2 ^ g ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the counter step
  have e1 := Exec.addN (P := P) hw 160016 160012 160024 (by rw [r24]; omega)
  set c1 := { c with nreg := upd c.nreg 160016 (c.nreg 160012 + c.nreg 160024) }
  have k1 : ∀ r, r ≠ 160016 → c1.nreg r = c.nreg r := fun r h => by
    simp only [c1, Machine.upd_other _ _ _ h]
  have h16 : c1.nreg 160016 = g + 1 := by
    show upd c.nreg 160016 (c.nreg 160012 + c.nreg 160024) 160016 = g + 1
    rw [Machine.upd_same, r24]
  -- a stopping step: the flag is set, the grade is the greedy one
  have stop : ∀ c2 : Config, WordsBounded W c2 → (∀ r, ¬ AscRG r → c2.nreg r = c.nreg r) →
      c2.nmem = c.nmem → c2.rreg = c.rreg → c2.rmem = c.rmem → c2.output = c.output →
      c2.nreg 160012 = g → c2.nreg 160013 = x / 2 ^ g → nextG lam b x = g →
      Exec P W (.instr (.constN 160025 1)) c2 { c2 with nreg := upd c2.nreg 160025 1 } 1 ∧
        AscInv lam b x c0 { c2 with nreg := upd c2.nreg 160025 1 } := by
    intro c2 hw2 hr2 hm2 hrr2 hrm2 ho2 hg2 hq2 hn
    refine ⟨Exec.constN (P := P) hw2 160025 1 (by have := hw2.1 160024; omega), ?_⟩
    refine ⟨fun r hr' => ?_, by simp only; rw [hm2, hm], by simp only; rw [hrr2, hrr],
      by simp only; rw [hrm2, hrm], by simp only; rw [ho2, ho], ?_, ?_, ?_, ?_⟩
    · simp only
      rw [Machine.upd_other _ _ _ (by unfold AscRG at hr'; omega), hr2 r hr', hr r hr']
    · simp only; rwa [Machine.upd_other _ _ _ (by omega), hg2]
    · simp only; rwa [Machine.upd_other _ _ _ (by omega), hg2]
    · simp only; rw [Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), hg2, hq2]
    · right; simp only
      rw [Machine.upd_same, Machine.upd_other _ _ _ (by omega), hg2, hn]; exact ⟨rfl, rfl⟩
  unfold ascBody
  by_cases hA : c1.nreg 160016 < c1.nreg 160026
  · rw [h16, k1 _ (by omega), r26] at hA
    -- read `q / 2`
    obtain ⟨c2, k2, e2, hk2, hw2, h17, h18, k2r, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.addN 160017 160020 160013, .loadN 160017 160017, .addN 160018 160017 160017])
        c1 c2 k2 ∧ k2 = 3 ∧ WordsBounded W c2 ∧ c2.nreg 160017 = x / 2 ^ g / 2 ∧
        c2.nreg 160018 = x / 2 ^ g / 2 + x / 2 ^ g / 2 ∧
        (∀ r, r ≠ 160017 → r ≠ 160018 → c2.nreg r = c1.nreg r) ∧ c2.nmem = c.nmem ∧
        c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output := by
      have q1 : c1.nreg 160020 = D := by rwa [k1 _ (by omega)]
      have q2 : c1.nreg 160013 = x / 2 ^ g := by rwa [k1 _ (by omega)]
      have md : c1.nmem (D + x / 2 ^ g) = x / 2 ^ g / 2 := by
        show c.nmem _ = _; rw [hm]; exact hD _ (by omega)
      have e1w := e1.wb_right
      exec_block
      · rw [q1, q2]; omega
      · config_simp; rw [q1, q2, md]; omega
      · refine ⟨rfl, ‹_›, by config_simp; rw [q1, q2, md], by config_simp; rw [q1, q2, md],
          fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
        simp only [Machine.upd_apply]
        split_ifs <;> first | omega
    have fr2 : ∀ r, ¬ AscRG r → c2.nreg r = c.nreg r := fun r hr' => by
      unfold AscRG at hr'; rw [k2r r (by omega) (by omega), k1 r (by omega)]
    have g2 : c2.nreg 160012 = g := by rw [k2r _ (by omega) (by omega), k1 _ (by omega)]
    have q2 : c2.nreg 160013 = x / 2 ^ g := by
      rwa [k2r _ (by omega) (by omega), k1 _ (by omega)]
    have t13 : c2.nreg 160013 = x / 2 ^ g := q2
    by_cases hodd : c2.nreg 160018 < c2.nreg 160013
    · rw [h18, t13] at hodd
      obtain ⟨e3, hI3⟩ := stop c2 hw2 fr2 hm2 hrr2 hrm2 ho2 g2 q2
        (nextG_eq_of hgl hok (fun _ hg1 => by
          have := (dvd_succ_iff hok.1).mp hg1.1; omega))
      refine ⟨_, _, .seq e1 (.ifLtN_true (by rwa [h16, k1 _ (by omega), r26])
        (.seq e2 (.ifLtN_true (by rwa [h18, t13]) e3))), hI3, ?_⟩
      simp only [Machine.upd_same, Machine.upd_other _ _ _ (show (160012 : ℕ) ≠ 160025 by omega)]
      rw [g2, hf]; omega
    · have heven : (x / 2 ^ g) % 2 = 0 := by rw [h18, t13] at hodd; omega
      have hdv : 2 ^ (g + 1) ∣ x := (dvd_succ_iff hok.1).mpr heven
      obtain ⟨c4, k4, e4, hk4, hw4, h19, k4r, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (block [.addN 160019 160021 160016, .loadN 160019 160019, .addN 160019 160010 160019])
          c2 c4 k4 ∧ k4 = 3 ∧ WordsBounded W c4 ∧ c4.nreg 160019 = x + 2 ^ (g + 1) ∧
          (∀ r, r ≠ 160019 → c4.nreg r = c2.nreg r) ∧ c4.nmem = c.nmem ∧
          c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output := by
        have q21 : c2.nreg 160021 = PW := by rwa [fr2 _ (by unfold AscRG; omega)]
        have q16 : c2.nreg 160016 = g + 1 := by rwa [k2r _ (by omega) (by omega)]
        have q10 : c2.nreg 160010 = x := by rwa [fr2 _ (by unfold AscRG; omega)]
        have mp : c2.nmem (PW + (g + 1)) = 2 ^ (g + 1) := by rw [hm2, hm]; exact hPW _ (by omega)
        exec_block
        · rw [q21, q16]; omega
        · config_simp; rw [q10, q21, q16, mp]; omega
        · refine ⟨rfl, ‹_›, by config_simp; rw [q10, q21, q16, mp], fun r a1 => ?_, hm2, hrr2,
            hrm2, ho2⟩
          simp only [Machine.upd_apply]
          split_ifs <;> first | omega
      have fr4 : ∀ r, ¬ AscRG r → c4.nreg r = c.nreg r := fun r hr' => by
        unfold AscRG at hr'; rw [k4r r (by omega), fr2 r (by unfold AscRG; omega)]
      have r11' : c4.nreg 160011 = b := by rwa [fr4 _ (by unfold AscRG; omega)]
      by_cases hB : c4.nreg 160011 < c4.nreg 160019
      · rw [r11', h19] at hB
        obtain ⟨e5, hI5⟩ := stop c4 hw4 fr4 hm4 hrr4 hrm4 ho4
          (by rwa [k4r _ (by omega)]) (by rwa [k4r _ (by omega)])
          (nextG_eq_of hgl hok (fun _ hg1 => by have := hg1.2; omega))
        refine ⟨_, _, .seq e1 (.ifLtN_true
          (by rwa [h16, k1 _ (by omega), r26]) (.seq e2 (.ifLtN_false
          (by rw [h18, t13]; omega) (.seq e4 (.ifLtN_true (by rwa [r11', h19]) e5))))),
          hI5, ?_⟩
        simp only [Machine.upd_same,
          Machine.upd_other _ _ _ (show (160012 : ℕ) ≠ 160025 by omega)]
        rw [k4r _ (by omega), g2, hf]; omega
      · rw [r11', h19] at hB
        obtain ⟨c6, k6, e6, hk6, hw6, h12', h13', k6r, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
            (block [.copyN 160013 160017, .copyN 160012 160016]) c4 c6 k6 ∧ k6 = 2 ∧
            WordsBounded W c6 ∧ c6.nreg 160012 = g + 1 ∧ c6.nreg 160013 = x / 2 ^ g / 2 ∧
            (∀ r, r ≠ 160012 → r ≠ 160013 → c6.nreg r = c4.nreg r) ∧ c6.nmem = c.nmem ∧
            c6.rreg = c.rreg ∧ c6.rmem = c.rmem ∧ c6.output = c.output := by
          have q17 : c4.nreg 160017 = x / 2 ^ g / 2 := by rwa [k4r _ (by omega)]
          have q16 : c4.nreg 160016 = g + 1 := by
            rwa [k4r _ (by omega), k2r _ (by omega) (by omega)]
          exec_block
          refine ⟨rfl, ‹_›, by config_simp; exact q16, by config_simp; exact q17,
            fun r a1 a2 => ?_, hm4, hrr4, hrm4, ho4⟩
          simp only [Machine.upd_apply]
          split_ifs <;> first | omega
        refine ⟨c6, _, .seq e1 (.ifLtN_true
          (by rwa [h16, k1 _ (by omega), r26]) (.seq e2 (.ifLtN_false
          (by rw [h18, t13]; omega) (.seq e4 (.ifLtN_false (by rwa [r11', h19]) e6))))),
          ⟨fun r hr' => ?_, by rw [hm6, hm], by rw [hrr6, hrr], by rw [hrm6, hrm], by rw [ho6, ho],
            ?_, ?_, ?_, Or.inl ?_⟩, ?_⟩
        · unfold AscRG at hr'; rw [k6r r (by omega) (by omega), fr4 r (by unfold AscRG; omega)]
          exact hr r (by unfold AscRG; omega)
        · rw [h12']; omega
        · rw [h12']; exact ⟨hdv, by omega⟩
        · rw [h13', h12', div_succ]
        · rwa [k6r _ (by omega) (by omega), k4r _ (by omega), k2r _ (by omega) (by omega),
            k1 _ (by omega)]
        · rw [h12', k6r _ (by omega) (by omega), k4r _ (by omega), k2r _ (by omega) (by omega),
            k1 _ (by omega), hf]
          omega
  · rw [h16, k1 _ (by omega), r26] at hA
    have fr1 : ∀ r, ¬ AscRG r → c1.nreg r = c.nreg r := fun r hr' => by
      unfold AscRG at hr'; rw [k1 r (by omega)]
    obtain ⟨e3, hI3⟩ := stop c1 e1.wb_right fr1 rfl rfl rfl rfl
      (by rw [k1 _ (by omega)]) (by rwa [k1 _ (by omega)])
      (nextG_eq_of hgl hok (fun h => by omega))
    refine ⟨_, _, .seq e1 (.ifLtN_false
      (by rwa [h16, k1 _ (by omega), r26]) e3), hI3, ?_⟩
    simp only [Machine.upd_same,
      Machine.upd_other _ _ _ (show (160012 : ℕ) ≠ 160025 by omega)]
    rw [k1 _ (by omega), hf]; omega

set_option maxHeartbeats 4000000 in
/-- **The greedy grade on the RAM.** -/
theorem ascS_exec {c : Config} (hw : WordsBounded W c) {lam b x D PW : ℕ}
    (h10 : c.nreg 160010 = x) (h11 : c.nreg 160011 = b) (h26 : c.nreg 160026 = lam)
    (h24 : c.nreg 160024 = 1) (h20 : c.nreg 160020 = D) (h21 : c.nreg 160021 = PW)
    (hl : 1 ≤ lam) (hx : x < b)
    (hD : ∀ y, y ≤ b → c.nmem (D + y) = y / 2)
    (hPW : ∀ i, i ≤ lam → c.nmem (PW + i) = 2 ^ i)
    (hWD : D + b ≤ W) (hWP : PW + lam ≤ W) (hWx : b + 2 ^ lam ≤ W) :
    ∃ c' k, Exec P W ascS c c' k ∧ k ≤ 20 * lam + 30 ∧ WordsBounded W c' ∧
      c'.nreg 160012 = nextG lam b x ∧ c'.nreg 160013 = x / 2 ^ nextG lam b x ∧
      (∀ r, ¬ AscRG r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ascS
  obtain ⟨c1, k1, e1, hk1, hw1, hI1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 160025 0, .constN 160012 0, .copyN 160013 160010]) c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ AscInv lam b x c c1 ∧ c1.nreg 160025 = 0 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, ⟨fun r hr' => ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, Or.inl ?_⟩, ?_⟩
    · simp only [Machine.upd_apply]
      unfold AscRG at hr'
      split_ifs <;> first | omega
    · config_simp; omega
    · config_simp; exact gradeOK_zero hx
    · config_simp; rw [h10]; simp
    · config_simp
    · config_simp
  obtain ⟨c', k, e, ⟨hw', hI'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 160025) (b := 160024) (body := ascBody)
    (fun c' => WordsBounded W c' ∧ AscInv lam b x c c')
    (fun c' => 20 * ((lam - c'.nreg 160012) + (1 - c'.nreg 160025))) (fun c' h => h.1)
    (fun c2 ⟨hw2, hI2⟩ htest => by
      have r24 : c2.nreg 160024 = 1 := by rwa [hI2.1 _ (by unfold AscRG; omega)]
      have hf : c2.nreg 160025 = 0 := by rw [r24] at htest; omega
      obtain ⟨c3, k3, e3, hI3, hp⟩ := ascBody_exec (P := P) hw2 h10 h11 h26 h24 h20 h21 hD hPW
        hWD hWP hWx hI2 hf
      exact ⟨c3, k3, e3, ⟨e3.wb_right, hI3⟩, hp⟩) ⟨hw1, hI1⟩
  obtain ⟨hr', hm', hrr', hrm', ho', hgl', hok', hq', hfl'⟩ := hI'
  have r24 : c'.nreg 160024 = 1 := by rwa [hr' _ (by unfold AscRG; omega)]
  rw [r24] at htest
  rcases hfl' with h0 | ⟨h1, hn⟩
  · omega
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hn, by rw [hq', hn], hr', hm', hrr', hrm', ho'⟩
  rw [hf1] at hk
  have := hI1.2.2.2.2.2.1
  omega

/-- **A counted loop** (as `Cluster.forN`): `while i < n do body`, the body advancing the counter
register `ri` by one and keeping the bound register `rn`; cost `≤ (B + 2) (n - j₀) + 2`. -/
theorem forN {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (n B : ℕ)
    (hI : ∀ j c, I j c → WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n)
    (hbody : ∀ j c, j < n → I j c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ I (j + 1) c')
    {j₀ : ℕ} {c : Config} (hc : I j₀ c) (hj₀ : j₀ ≤ n) :
    ∃ c' k, Exec P W (.whileLtN ri rn body) c c' k ∧ k ≤ (B + 2) * (n - j₀) + 2 ∧ I n c' := by
  obtain ⟨c', k, e, ⟨j', hIj, hj'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := ri) (b := rn) (body := body) (fun c => ∃ j, I j c ∧ j ≤ n)
    (fun c => (B + 2) * (n - c.nreg ri)) (fun c ⟨j, h, _⟩ => (hI j c h).1)
    (fun c ⟨j, h, hjn⟩ htest => by
      obtain ⟨-, hri, hrn⟩ := hI j c h
      rw [hri, hrn] at htest
      obtain ⟨c', k, e, hk, h'⟩ := hbody j c htest h
      obtain ⟨-, hri', -⟩ := hI (j + 1) c' h'
      refine ⟨c', k, e, ⟨j + 1, h', by omega⟩, ?_⟩
      rw [hri, hri']
      have : (B + 2) * (n - j) = (B + 2) * (n - (j + 1)) + (B + 2) := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega) ⟨j₀, hc, hj₀⟩
  obtain ⟨-, hri, hrn⟩ := hI j' c' hIj
  have hj'n : j' = n := by rw [hri, hrn] at htest; omega
  subst hj'n
  refine ⟨c', k, e, ?_, hIj⟩
  obtain ⟨-, hri0, -⟩ := hI j₀ c hc
  rwa [hri0] at hk

end proofs

end

end Chazelle.Core.L41
