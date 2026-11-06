module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.UpPhase12

/-!
# WP-J up phase, part 13: one chain

`chainS = lenS; descU; nfU; prepCall; cellB` and `chainS_exec`: from the chain-loop invariant
`ChainMem` for chain `i` to the invariant for chain `i + 1`, at cost `stepB g`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- **One chain of the current grade.** -/
def chainS (sB sL sG sP : Stmt) : Stmt :=
  .seq lenS (.seq descU (.seq (nfU sB sL sG) (.seq (prepCall sP) cellB)))

/-- A bound on the chord count of a normal form of grade `g`. -/
noncomputable def NB (g : ℕ) : ℕ := l23c 4 * (2 ^ (g + 1) + 8) / (gradeGran g + 1)

/-- **The cost bound of one chain of grade `g`.** -/
noncomputable def stepB (κB κL : ℕ) (κG : ℕ → ℕ) (κO g : ℕ) : ℕ :=
  nfB κB κL κG g + κO * (NB g * (g + 1) + 1) + 1924

/-- **The memory invariant of the chain loop**: the grade record at `h` (grade `g` in progress,
the row of grade `g - 1` at `R`) and the cells of chains `< i`. -/
def ChainMem (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h hp g R x i A : ℕ) : Prop :=
  UpTab O P m h hp A ∧ m h = g ∧ (1 ≤ g → m (m (h + 2) + (g - 1)) = R) ∧
    Cells O P m A hp g x i

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

set_option maxHeartbeats 64000000 in
/-- **One chain.** -/
theorem chainS_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
      (fun _ c => κB * (rd c bBrute 1 + 1) ^ 3))
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
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
          NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M →
        NFAt c.nmem (rd c bGran 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
          N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
          IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
      (fun _ c => κG (rd c bGran 2) *
        (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1)))
    (hV : O.Valid) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R x A : ℕ}
    (hu : URegs c P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R)
    (hA : c.nreg ALLOC = A) (h15 : c.nreg 170015 = i) (h16 : c.nreg 170016 = gradeStart g i)
    (h18 : c.nreg 170018 = x) (h35 : c.nreg 170035 = 6 * i) (h36 : c.nreg 170036 = 2 * i + 1)
    (hi : i < gradeCount P.n g) (h2g : 2 ^ g ≤ 2 * P.n)
    (hM : Robust A c.nmem fun m => ChainMem O P m h hp g R x i A)
    (hW : A + stepB κB κL κG O.κ g + 6 ≤ W) :
    ∃ c' k, Exec P W (chainS sB sL sG O.prep) c c' k ∧ k ≤ stepB κB κL κG O.κ g ∧
      WordsBounded W c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      URegs c' P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R ∧
      c'.nreg 170015 = i + 1 ∧ c'.nreg 170016 = gradeStart g (i + 1) ∧
      c'.nreg 170035 = 6 * (i + 1) ∧ c'.nreg 170036 = 2 * (i + 1) + 1 ∧
      Robust (c'.nreg ALLOC) c'.nmem
        (fun m => ChainMem O P m h hp g R (c'.nreg 170018) (i + 1) (c'.nreg ALLOC)) ∧
      (∀ a, a < A → c'.nmem a = c.nmem a) ∧ (∀ a, a < A → c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
        r ≠ 170036 → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  have hWn : P.n + 3 ≤ W := by grind [hostWords]
  have hfit := gradeLen_fit hn hi
  have hl1 := gradeLen_pos hn hi
  have hl2 := gradeLen_le P.n g i
  have hcnt : gradeCount P.n g ≤ P.n := by
    unfold gradeCount; have := Nat.div_le_self (P.n - 2) (2 ^ g); omega
  unfold stepB at hW
  have hW128 : 128 * P.n + 8 ≤ W := by grind [hostWords]
  obtain ⟨hT0, hmh0, hR0, hC0⟩ := hM.holds
  obtain ⟨-, -, -, hH, hhp, -, -, -, -⟩ := hT0
  -- `lenS`
  obtain ⟨c1, k1, e1, hk1, hw1, l17, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    lenS_exec (P := P) hw hu.r28 h16 hu.r10
  have h17 : c1.nreg 170017 = gradeLen P.n g i := by rw [l17]; rfl
  have hu1 := hu.of_frame fun r hr => fr1 r (by grind [URegR])
    (by grind [URegR])
  have hA1 : c1.nreg ALLOC = A := by grind
  have g1 : ∀ r, r ≠ 170017 → r ≠ 170033 → c1.nreg r = c.nreg r := fr1
  -- `descU`
  have hM1 : Robust A c1.nmem fun m => ChainMem O P m h hp g R x i A := by grind
  obtain ⟨c2, k2, e2, hk2, hw2, a21, a22, d5, dh, hdesc, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descU_exec (O := O) hG hWn hn hw1 hu1 hA1 (by grind)
      (by grind)
      (by grind) hi hM1.holds.1 hM1.holds.2.1
      hM1.holds.2.2.1 (by omega) (by omega)
  obtain ⟨d, hd⟩ : ∃ d, c2.nreg 170030 = d := ⟨_, rfl⟩
  rw [hd] at d5 dh hdesc
  have hu2 := hu1.of_kept fr2
  have kk2 : ∀ r, r = 170015 ∨ r = 170016 ∨ r = 170017 ∨ r = 170018 ∨ r = 170035 ∨
      r = 170036 → c2.nreg r = c1.nreg r := fun r hr => fr2 r (kept_of
        (by unfold bandOf bUp; omega) (by omega))
  -- memory: `c2` agrees with `c` below `A`
  have mc2 : ∀ a, a < A → c2.nmem a = c.nmem a := fun a ha => by grind
  have hM2 : Robust (c2.nreg ALLOC) c2.nmem fun m => UpTab O P m h hp (c2.nreg ALLOC) ∧
      m h = g ∧ (1 ≤ g → m (m (h + 2) + (g - 1)) = R) :=
    robust_of (hM.transport mc2) a21 fun m' h' => ⟨h'.1.mono a21, h'.2.1, h'.2.2.1⟩
  -- `nfU`
  have hWnf : c2.nreg ALLOC + nfB κB κL κG g + 6 ≤ W := by omega
  obtain ⟨c3, k3, e3, hk3, hw3, a31, a32, hnf, m31, m32, o3, fr3, frr3⟩ :=
    nfU_exec (O := O) (sB := sB) (sL := sL) (sG := sG) hB hL hGr hG hWh hn hw2 hu2 rfl
      (by grind)
      (by grind)
      (by grind) hi hM2 hd d5 dh hdesc
      hWnf
  obtain ⟨f, hf⟩ : ∃ f, c3.nreg 170031 = f := ⟨_, rfl⟩
  rw [hf] at hnf
  have hu3 := hu2.of_kept fun r hr => fr3 r (Or.inl hr)
  let C0 := gChain P g i hn hi
  obtain ⟨N, hNW, hc⟩ := hnf C0 rfl rfl rfl
  have h30' : c3.nreg 170030 = d := (fr3 _ (Or.inr rfl)).trans hd
  have mc3 : ∀ a, a < c2.nreg ALLOC → c3.nmem a = c2.nmem a := m31
  have hH3 : HostAt c3.nmem hp (Host.whole P.n) :=
    L41.hostAt_agree (A := A) hH rfl (by omega) fun a ha => by
      grind
  have hd3 : ChainDescAt c3.nmem d (Qof P) (Host.whole P.n) C0 :=
    chainDescAt_agree (hdesc C0 rfl rfl rfl) d5 dh (by omega) mc3
  have dh3 : c3.nmem d = hp := by grind
  have hNo : NodeOK P c3.nmem (c3.nreg ALLOC) hp d f C0 (gradeGran g) :=
    ⟨hd3, rfl, dh3, by omega, by omega, hfit, N, hNW, hc⟩
  have hwf := chainWF_of_node (by omega) hNo hH3
  -- the preprocessing cost
  have hP : C0.P.Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hcnt3 := nChords_mul_le hP hc
  have hNB : c3.nmem f ≤ NB g := by
    rw [hNW.holds.1]
    unfold NB
    rw [Nat.le_div_iff_mul_le (by omega)]
    refine le_trans hcnt3 (Nat.mul_le_mul_left _ ?_)
    show 2 * gradeLen P.n g i + 8 ≤ 2 ^ (g + 1) + 8
    omega
  have hlog : Nat.clog 2 (c3.nmem (d + 2)) ≤ g := by
    rw [hd3.2.2.2.1]; exact Nat.clog_le_of_le_pow hl2
  have hpc : O.κ * (c3.nmem f * (Nat.clog 2 (c3.nmem (d + 2)) + 1) + 1) ≤
      O.κ * (NB g * (g + 1) + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul hNB (by omega)) 1)
  -- `prepCall`
  obtain ⟨c4, k4, e4, hk4, hw4, a41, a42, o1, o2, t0, t1, t2, hAt, m41, m42, o4, fr4, frr4⟩ :=
    prepCall_exec (P := P) (N := N) hV hG hWh hw3 h30' hf hu3.r11 hwf hd3 rfl hNW hc
      (by omega)
  obtain ⟨o, hoo⟩ : ∃ o, c4.nreg 170032 = o := ⟨_, rfl⟩
  rw [hoo] at o1 o2 t0 t1 t2 hAt
  have kk4 : ∀ r, Kept r → c4.nreg r = c3.nreg r := fun r hr =>
    fr4 r (hr.not_mem (by decide) (by decide) (by decide)) (by have := hr.range; omega)
      hr.ne_alloc
  have hu4 := hu3.of_kept kk4
  have k4' : ∀ r, r = 170015 ∨ r = 170016 ∨ r = 170018 ∨ r = 170035 ∨ r = 170036 →
      c4.nreg r = c.nreg r := fun r hr => by
    have kr : Kept r := kept_of (by unfold bandOf bUp; omega) (by omega)
    rw [kk4 r kr, fr3 r (Or.inl kr), fr2 r kr, g1 r (by omega) (by omega)]
  -- `cellB`
  have hsb : gradeStart g i + 2 ^ g ≤ 3 * P.n := by omega
  obtain ⟨c5, k5, e5, hk5, hw5, A5e, x5, i5, s5, q5, t5, w0, w1, w2, w3, mw, fr5, hrr5, hrm5,
      ho5⟩ :=
    cellB_exec (P := P) (d := d) (f := f) (o := o) (x := x) (i := i) (s := gradeStart g i)
      (q := 6 * i) (t := 2 * i + 1) hw4 rfl
      (by rw [fr4 170030 (by decide) (by decide) (by decide)]; exact h30')
      (by rw [fr4 170031 (by decide) (by decide) (by decide)]; exact hf) hoo
      (by rw [k4' _ (by omega)]; exact h18) (by rw [k4' _ (by omega)]; exact h15)
      (by rw [k4' _ (by omega)]; exact h16) hu4.r10 (by rw [k4' _ (by omega)]; exact h35)
      (by rw [k4' _ (by omega)]; exact h36) hu4.r20 hu4.r21 hu4.r25 hu4.r26
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have mc5 : ∀ a, a < A → c5.nmem a = c.nmem a := fun a ha => by
    rw [mw a (Or.inl (by omega)), m41 a (by omega), mc3 a (by omega), mc2 a ha]
  have mc53 : ∀ a, a < c3.nreg ALLOC → c5.nmem a = c3.nmem a := fun a ha => by
    rw [mw a (Or.inl (by omega)), m41 a ha]
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    by unfold stepB; omega, hw5, by omega, by omega,
    hu4.of_frame fun r hr => fr5 r (by unfold URegR at hr; omega) (by unfold URegR at hr; omega)
      (by unfold URegR at hr; omega) (by unfold URegR at hr; omega)
      (by unfold URegR at hr; omega) (by unfold URegR at hr; omega)
      (by unfold URegR at hr; omega),
    i5, by rw [s5]; unfold gradeStart; ring, by omega, by omega, ?_, mc5,
    fun a ha => by ram_simp, by
      grind, fun r hr a1 a2 a3 a4 a5 a6 => ?_, fun r hr => by
      rw [hrr5, frr4 r (hr.not_mem (by decide)), frr3 r hr, frr2 r hr, hrr1]⟩
  · rw [x5, A5e]
    intro m hm
    have hmc : ∀ a, a < A → m a = c.nmem a := fun a ha => (hm a (by omega)).trans (mc5 a ha)
    have hm3 : ∀ a, a < c3.nreg ALLOC → m a = c3.nmem a := fun a ha =>
      (hm a (by omega)).trans (mc53 a ha)
    obtain ⟨hT, hmh, hR, hCl⟩ := hM m hmc
    refine ⟨hT.mono (by omega), hmh, hR, ?_⟩
    have e0 : m (c4.nreg ALLOC) = d := (hm _ (by omega)).trans w0
    have e1 : m (c4.nreg ALLOC + 1) = f := (hm _ (by omega)).trans w1
    have e2 : m (c4.nreg ALLOC + 2) = o := (hm _ (by omega)).trans w2
    have e3 : m (c4.nreg ALLOC + 3) = x := (hm _ (by omega)).trans w3
    show _ ∧ _ ∧ _
    rw [e0, e1, e2, e3]
    refine ⟨by omega, ⟨fun C a b f' => ?_, hAt m fun a ha => (hm a (by omega)).trans
        (mw a (Or.inl ha)), (hm o (by omega)).trans ((mw o (Or.inl (by omega))).trans t0),
      (hm _ (by omega)).trans ((mw _ (Or.inl (by omega))).trans t1),
      (hm _ (by omega)).trans ((mw _ (Or.inl (by omega))).trans t2)⟩,
      hCl.mono (by omega)⟩
    have : C0 = C := chain_eq a.symm b.symm f'.symm
    subst this
    exact ⟨chainDescAt_agree hd3 (by omega) dh3 (by omega) hm3, rfl,
      by rw [hm3 _ (by omega)]; exact dh3, by omega, by omega, hfit, N,
      fun m'' hm'' => hNW m'' fun a ha => (hm'' a (by omega)).trans (hm3 a ha), hc⟩
  · have ha5 : r ≠ 170034 := by have := hr.range; omega
    rw [fr5 r ha5 a4 a1 a2 a5 a6 hr.ne_alloc, kk4 r hr, fr3 r (Or.inl hr), fr2 r hr,
      g1 r a3 (by have := hr.range; omega)]

end proofs

end

end Chazelle.Core.Up
