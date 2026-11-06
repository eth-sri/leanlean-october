module

public import Chazelle.Core.UpPhase4
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
set_option maxHeartbeats 16000000

/-!
# WP-J up phase, part 5: calling Lemma 4.1 and the oracle preprocessing

`l41Call_exec` and `prepCall_exec`: the contracts `Lemma41Spec O` and `O.Valid` (preprocessing)
read back in the up phase's registers.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

/-- **Lemma 4.1, called from the up phase.** -/
theorem l41Call_exec {O : OracleIface} {sL : Stmt} {κL : ℕ}
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem (rd c bL41 0) (c.nreg ALLOC) ∧
        rd c bL41 3 ≤ c.nmem (rd c bL41 0) ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ (rd c bL41 3 - 1) < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bL41 4) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran (rd c bL41 3)) 4)
      (fun _ c => κL * (lemma41Nat (rd c bL41 3) + 1)))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {h s len g : ℕ} (h05 : c.nreg 170005 = h) (h16 : c.nreg 170016 = s)
    (h17 : c.nreg 170017 = len) (h07 : c.nreg 170007 = g)
    (hX : (gradeCtx O).holds P c.nmem h (c.nreg ALLOC)) (hgΛ : g ≤ c.nmem h) (h7 : 7 ≤ g)
    (hsl : s + len + 1 ≤ P.n) (hl1 : 2 ^ (g - 1) < len) (hl2 : len ≤ 2 ^ g)
    (hbud : c.nreg ALLOC + κL * (lemma41Nat g + 1) ≤ W) :
    ∃ c' k, Exec P W (l41Call sL) c c' k ∧ k ≤ κL * (lemma41Nat g + 1) + 5 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran g) 4) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ l41Bands → r ≠ 170031 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ l41Bands → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, i3, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 160000 170005, .copyN 160001 170016, .copyN 160002 170017,
        .copyN 160003 170007]) c c1 k1 ∧
      k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 160000 = h ∧ c1.nreg 160001 = s ∧
      c1.nreg 160002 = len ∧ c1.nreg 160003 = g ∧
      (∀ r, r ≠ 160000 → r ≠ 160001 → r ≠ 160002 → r ≠ 160003 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact h05, by config_simp; exact h16,
      by config_simp; exact h17, by config_simp; exact h07, fun r a1 a2 a3 a4 => ?_, rfl, rfl,
      rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA1 : c1.nreg ALLOC = c.nreg ALLOC := fr1 _ (by rwd [hAl]) (by rwd [hAl])
    (by rwd [hAl]) (by rwd [hAl])
  have hX1 : (gradeCtx O).holds P c1.nmem (rd c1 bL41 0) (c1.nreg ALLOC) := by
    show (gradeCtx O).holds P c1.nmem (c1.nreg 160000) _
    rwx [i0, hm1, hA1]
  obtain ⟨c2, k2, e2, hk2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, fr2⟩ :=
    hL P W c1 hw1 ⟨hG, hWh, hX1,
      by show c1.nreg 160003 ≤ c1.nmem (c1.nreg 160000); rw [i3, i0, hm1]; exact hgΛ,
      by show lemma41Start ≤ c1.nreg 160003; rwx [i3],
      by show c1.nreg 160001 + c1.nreg 160002 + 1 ≤ P.n; omega,
      by show 2 ^ (c1.nreg 160003 - 1) < c1.nreg 160002; rwx [i3, i2],
      by show c1.nreg 160002 ≤ 2 ^ c1.nreg 160003; rwx [i3, i2]⟩
      (by show c1.nreg ALLOC + κL * (lemma41Nat (c1.nreg 160003) + 1) ≤ W
          rwx [hA1, i3])
  replace hk2 : k2 ≤ κL * (lemma41Nat (c1.nreg 160003) + 1) := hk2
  rw [i3] at hk2
  obtain ⟨fr2r, fr2rr, fr2m, fr2rm, fr2o, fr2a, fr2b⟩ := fr2
  have hw2 := e2.wb_right
  obtain ⟨c3, k3, e3, hk3, hw3, o31, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 170031 160004]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170031 = c2.nreg 160004 ∧ (∀ r, r ≠ 170031 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA3 : c3.nreg ALLOC = c2.nreg ALLOC := fr3 _ (by rwd [hAl])
  have hbb : ∀ r, bandOf r ∉ l41Bands → r < 160000 ∨ 170000 ≤ r := by
    intro r hr
    by_contra hc
    exact hr (by rwd [band_l41' (by omega) (by omega)])
  refine ⟨c3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, hw3, by rw [hA3, ← hA1]; exact fr2a,
    by rwo [hA3, ← hA1], ⟨C, N, hCP, by rwx [hCs], by rwx [hCm],
      by rwx [o31, hm3, hA3], by rwx [← i3]⟩,
    fun a ha => by rw [hm3, fr2m a (by rwx [hA1]), hm1],
    fun a ha => by rw [hrm3, fr2rm a (by rwx [hA1]), hrm1],
    by rw [ho3, fr2o, ho1], fun r h1 h2 h3 => ?_, fun r h1 => by rw [hrr3, fr2rr r h1, hrr1]⟩
  have := hbb r h1
  rw [fr3 r h2, fr2r r h1 h3, fr1 r (by omega) (by omega) (by omega) (by omega)]

/-- **The oracle preprocessing, called from the up phase.** -/
theorem prepCall_exec {O : OracleIface} (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c) {B F γ : ℕ} {H : Host}
    {C : Chain} {N : NF} (h30 : c.nreg 170030 = B) (h31 : c.nreg 170031 = F)
    (h11 : c.nreg 170011 = γ) (hwf : ChainWF P (c.nreg ALLOC) c.nmem B)
    (hd : ChainDescAt c.nmem B (Qof P) H C) (hCP : C.P = Qof P)
    (hNW : NFWithin c.nmem F (c.nreg ALLOC) N) (hc : IsCanonicalNF (chainModel C) (Qof P) N γ 4)
    (hbud : c.nreg ALLOC + O.κ * (c.nmem F * (Nat.clog 2 (c.nmem (B + 2)) + 1) + 1) ≤ W) :
    ∃ c' k, Exec P W (prepCall O.prep) c c' k ∧
      k ≤ O.κ * (c.nmem F * (Nat.clog 2 (c.nmem (B + 2)) + 1) + 1) + 4 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      c.nreg ALLOC ≤ c'.nreg 170032 ∧ c'.nreg 170032 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem (c'.nreg 170032) = B ∧ c'.nmem (c'.nreg 170032 + 1) = F ∧
      c'.nmem (c'.nreg 170032 + 2) = γ ∧
      (∀ m', (∀ a, a < c'.nreg ALLOC → m' a = c'.nmem a) → O.At P m' (c'.nreg 170032)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → r ≠ 170032 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨hVb, hVp, -⟩ := hV
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 110000 170030, .copyN 110001 170031, .copyN 110002 170011]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 110000 = B ∧ c1.nreg 110001 = F ∧
      c1.nreg 110002 = γ ∧ (∀ r, r ≠ 110000 → r ≠ 110001 → r ≠ 110002 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact h30, by config_simp; exact h31,
      by config_simp; exact h11, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA1 : c1.nreg ALLOC = c.nreg ALLOC := fr1 _ (by rwd [hAl]) (by rwd [hAl])
    (by rwd [hAl])
  have hwf1 : ChainWF P (c1.nreg ALLOC) c1.nmem (rd c1 bOPrep 0) := by
    show ChainWF P (c1.nreg ALLOC) c1.nmem (c1.nreg 110000)
    rwx [i0, hm1, hA1]
  have hd1 : ChainDescAt c1.nmem (rd c1 bOPrep 0) (Qof P) H C := by
    show ChainDescAt c1.nmem (c1.nreg 110000) (Qof P) H C
    rwx [i0, hm1]
  have hN1 : NFWithin c1.nmem (rd c1 bOPrep 1) (c1.nreg ALLOC) N := by
    show NFWithin c1.nmem (c1.nreg 110001) (c1.nreg ALLOC) N
    rwx [i1, hm1, hA1]
  have hc1 : IsCanonicalNF (chainModel C) (Qof P) N (rd c1 bOPrep 2) 4 := by
    show IsCanonicalNF (chainModel C) (Qof P) N (c1.nreg 110002) 4
    rwx [i2]
  obtain ⟨c2, k2, e2, hk2, ⟨q0, q0', q1, q2, q3, q4⟩, fr2⟩ :=
    hVp P W c1 hw1 ⟨hG, hWh, hwf1, H, C, N, hd1, hCP, hN1, hc1⟩
      (by show c1.nreg ALLOC + O.κ * (c1.nmem (c1.nreg 110001) *
            (Nat.clog 2 (c1.nmem (c1.nreg 110000 + 2)) + 1) + 1) ≤ W
          rwx [hA1, i0, i1, hm1])
  replace hk2 : k2 ≤ O.κ * (c1.nmem (c1.nreg 110001) *
    (Nat.clog 2 (c1.nmem (c1.nreg 110000 + 2)) + 1) + 1) := hk2
  rw [i0, i1, hm1] at hk2
  obtain ⟨fr2r, fr2rr, fr2m, fr2rm, fr2o, fr2a, fr2b⟩ := fr2
  have hw2 := e2.wb_right
  obtain ⟨c3, k3, e3, hk3, hw3, o32, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 170032 110003]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170032 = c2.nreg 110003 ∧ (∀ r, r ≠ 170032 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA3 : c3.nreg ALLOC = c2.nreg ALLOC := fr3 _ (by rwd [hAl])
  have hbb : ∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → r < 110000 ∨ 120000 ≤ r := by
    intro r hr
    by_contra hc
    exact hr (by rwd [band_prep (by omega) (by omega)])
  have hsub : ∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → bandOf r ∉ O.bands := fun r hr h' =>
    hr (hVb h')
  refine ⟨c3, k1 + (k2 + k3), .seq e1 (.seq e2 e3), by omega, hw3, by rw [hA3, ← hA1]; exact fr2a,
    by rwo [hA3, ← hA1], by rwx [o32, ← hA1], by rwx [o32, hA3],
    by rw [o32, hm3]; exact q1.trans i0, by rw [o32, hm3]; exact q2.trans i1,
    by rw [o32, hm3]; exact q3.trans i2,
    fun m' hm' => by rw [o32]; exact q4 m' (by rwx [← hA3, ← hm3]),
    fun a ha => by rw [hm3, fr2m a (by rwx [hA1]), hm1],
    fun a ha => by rw [hrm3, fr2rm a (by rwx [hA1]), hrm1],
    by rw [ho3, fr2o, ho1], fun r h1 h2 h3 => ?_,
    fun r h1 => by rw [hrr3, fr2rr r (hsub r h1), hrr1]⟩
  have := hbb r h1
  rw [fr3 r h2, fr2r r (hsub r h1) h3, fr1 r (by omega) (by omega) (by omega)]

end proofs

end

end Chazelle.Core.Up
