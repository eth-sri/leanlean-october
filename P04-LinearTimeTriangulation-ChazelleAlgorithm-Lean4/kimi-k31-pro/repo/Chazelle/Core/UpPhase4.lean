module

public import Chazelle.Core.UpPhase3

/-!
# WP-J up phase, part 4: calling the packages

Wrappers that load the input registers of a package, run it, and copy its output to band
`bUp`: brute force (`bruteCall`), Lemma 4.1 (`l41Call`), and the oracle preprocessing
(`prepCall`).  Each exec lemma is the package's `Meets` read back in the up phase's registers.

Registers: `170016` start `s`, `170017` length, `170011` the granularity `γ'_g`, `170005` the
grade record, `170007` the grade `g`, `170030` the descriptor, `170031` the NF, `170032` the
oracle structure.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- Brute force: `(s, len, γ) ↦ NF` in `170031`. -/
def bruteCall (sB : Stmt) : Stmt :=
  .seq (block [.copyN 180000 170016, .copyN 180001 170017, .copyN 180002 170011])
    (.seq sB (block [.copyN 170031 180003]))

/-- Lemma 4.1: `(h, s, len, g) ↦ NF` in `170031`. -/
def l41Call (sL : Stmt) : Stmt :=
  .seq (block [.copyN 160000 170005, .copyN 160001 170016, .copyN 160002 170017,
    .copyN 160003 170007]) (.seq sL (block [.copyN 170031 160004]))

/-- The oracle preprocessing: `(desc, NF, γ) ↦` structure in `170032`. -/
def prepCall (sP : Stmt) : Stmt :=
  .seq (block [.copyN 110000 170030, .copyN 110001 170031, .copyN 110002 170011])
    (.seq sP (block [.copyN 170032 110003]))

section proofs

variable {P : Polygon} {W : ℕ}

theorem band_brute {r : ℕ} (h1 : 180000 ≤ r) (h2 : r < 190000) : bandOf r = bBrute := by
  unfold bandOf bBrute; omega

theorem band_l41' {r : ℕ} (h1 : 160000 ≤ r) (h2 : r < 170000) : bandOf r = bL41 := by
  unfold bandOf bL41; omega

theorem band_prep {r : ℕ} (h1 : 110000 ≤ r) (h2 : r < 120000) : bandOf r = bOPrep := by
  unfold bandOf bOPrep; omega

set_option maxHeartbeats 16000000 in
/-- **Brute force, called from the up phase.** -/
theorem bruteCall_exec {sB : Stmt} {κB : ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
      (fun _ c => κB * (rd c bBrute 1 + 1) ^ 3))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {s len γ : ℕ} (h16 : c.nreg 170016 = s) (h17 : c.nreg 170017 = len)
    (h11 : c.nreg 170011 = γ) (hl : 1 ≤ len) (hsl : s + len + 1 ≤ P.n) (hγ : 1 ≤ γ)
    (hlγ : len = 1 ∨ 2 ≤ γ) (hbud : c.nreg ALLOC + κB * (len + 1) ^ 3 ≤ W) :
    ∃ c' k, Exec P W (bruteCall sB) c c' k ∧ k ≤ κB * (len + 1) ^ 3 + 4 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N ∧
        IsCanonicalNF (chainModel C) (Qof P) N γ 4) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ bruteBands → r ≠ 170031 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ bruteBands → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 180000 170016, .copyN 180001 170017, .copyN 180002 170011]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 180000 = s ∧ c1.nreg 180001 = len ∧
      c1.nreg 180002 = γ ∧ (∀ r, r ≠ 180000 → r ≠ 180001 → r ≠ 180002 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact h16, by config_simp; exact h17,
      by config_simp; exact h11, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA1 : c1.nreg ALLOC = c.nreg ALLOC := fr1 _ (by rw [hAl]; decide) (by rw [hAl]; decide)
    (by rw [hAl]; decide)
  obtain ⟨c2, k2, e2, hk2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, fr2⟩ :=
    hB P W c1 hw1 ⟨hG, hWh, by show 1 ≤ c1.nreg 180001; omega,
      by show c1.nreg 180000 + c1.nreg 180001 + 1 ≤ P.n; omega,
      by show 1 ≤ c1.nreg 180002; omega,
      by show c1.nreg 180001 = 1 ∨ 2 ≤ c1.nreg 180002; omega⟩
      (by show c1.nreg ALLOC + κB * (c1.nreg 180001 + 1) ^ 3 ≤ W; rw [hA1, i1]; exact hbud)
  replace hk2 : k2 ≤ κB * (c1.nreg 180001 + 1) ^ 3 := hk2
  rw [i1] at hk2
  obtain ⟨fr2r, fr2rr, fr2m, fr2rm, fr2o, fr2a, fr2b⟩ := fr2
  have hw2 := e2.wb_right
  obtain ⟨c3, k3, e3, hk3, hw3, o31, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 170031 180003]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170031 = c2.nreg 180003 ∧ (∀ r, r ≠ 170031 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA3 : c3.nreg ALLOC = c2.nreg ALLOC := fr3 _ (by rw [hAl]; decide)
  have hbb : ∀ r, bandOf r ∉ bruteBands → r < 180000 ∨ 190000 ≤ r := by
    intro r hr
    by_contra hc
    exact hr (by rw [band_brute (by omega) (by omega)]; decide)
  refine ⟨c3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, hw3, by rw [hA3, ← hA1]; exact fr2a,
    by rw [hA3, ← hA1]; omega, ⟨C, N, hCP, by rw [hCs]; exact i0, by rw [hCm]; exact i1,
      by rw [o31, hm3, hA3]; exact hNW, by rw [← i2]; exact hc⟩,
    fun a ha => by rw [hm3, fr2m a (by rw [hA1]; exact ha), hm1],
    fun a ha => by rw [hrm3, fr2rm a (by rw [hA1]; exact ha), hrm1],
    by rw [ho3, fr2o, ho1], fun r h1 h2 h3 => ?_, fun r h1 => by rw [hrr3, fr2rr r h1, hrr1]⟩
  have := hbb r h1
  rw [fr3 r h2, fr2r r h1 h3, fr1 r (by omega) (by omega) (by omega)]

end proofs

end

end Chazelle.Core.Up
