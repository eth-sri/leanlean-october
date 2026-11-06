module

public import Chazelle.Core.UpPhase11
public import Chazelle.Core.MergeAsmMath
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 32000000

/-!
# WP-J up phase, part 12: the normal form of a chain from the grade record

`nfU_exec`: the three cases of `nfU` with a uniform result, the cost bound `nfB g` depending on
the grade only (the coarsened child has at most `FB g` chords by Lemma 2.3).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The constant of Lemma 2.3, explicitly: `l23c D = 140 (D + 2)` (the witness of `lemma23`;
named explicitly, not chosen, so that the constants of the named program are explicit). -/
def l23c : ℕ → ℕ := fun D => 140 * (D + 2)

/-- A bound on the chord count of the child coarsened at grade `g`. -/
noncomputable def FB (g : ℕ) : ℕ := l23c 4 * (2 ^ g + 8) / (gradeGran (g - 1) + 1)

/-- **The cost bound of the normal form of a chain of grade `g`.** -/
noncomputable def nfB (κB κL : ℕ) (κG : ℕ → ℕ) (g : ℕ) : ℕ :=
  if g < 7 then κB * (2 ^ g + 1) ^ 3 + 5 else
    κL * (lemma41Nat g + 1) + 8 + (κG 4 * (FB g * (Nat.clog 2 (FB g) + 1) + 1) + 37)

section proofs

/-- **Lemma 2.3 with the explicit constant `l23c`** (the proof of `lemma23`). -/
theorem l23c_spec (M : Model) (Q : Polygon) (F : Set (Set Point)) (γ D : ℕ) (hM : GoodModel M)
    (hF : M.ChordFamily Q F) (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * (γ + 1) ≤ l23c D * (M.size + 1) := by
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk M hM
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact absurd hgran.1 (hW.not_semigranular_zero hAdm hfin hne hp₀ hc₀)
  · have h := hW.lemma23_walk hAdm hfin hdeg hgran
    calc F.ncard * (γ + 1) ≤ 2 * (F.ncard * γ) := by nlinarith
      _ ≤ 2 * (2 * (D + 2) * (5 * M.W.n)) := Nat.mul_le_mul_left _ h
      _ ≤ 2 * (2 * (D + 2) * (5 * (7 * (M.size + 1)))) := by gcongr
      _ = l23c D * (M.size + 1) := by ufring l23c

variable {O : OracleIface} {P : Polygon} {W : ℕ}

/-- **Lemma 2.3 for a canonical normal form of a chain.** -/
theorem nChords_mul_le {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hN : IsCanonicalNF (chainModel C) Q N γ 4) : N.nChords * (γ + 1) ≤ l23c 4 * (2 * C.m + 8) := by
  obtain ⟨hnf, hdeg, hgr, -⟩ := hN
  have h := l23c_spec _ Q _ γ 4 (Or.inl ⟨C, hP, rfl⟩) hnf.1 hdeg hgr
  rw [Gran.ncard_F hnf] at h
  have hs := MergeAsm.size_le_n (chainModel C)
  rw [MergeAsm.chainModel_n] at hs
  calc N.nChords * (γ + 1) ≤ l23c 4 * ((chainModel C).size + 1) := h
    _ ≤ l23c 4 * (2 * C.m + 8) := Nat.mul_le_mul_left _ (by omega)

theorem one_le_gradeGran (g : ℕ) : 1 ≤ gradeGran g := by
  unfold gradeGran; have := Nat.one_le_two_pow (n := Cost.ceilBeta g); omega

theorem two_le_gradeGran {g : ℕ} (hg : 1 ≤ g) : 2 ≤ gradeGran g := by
  unfold gradeGran
  have h1 := Cost.one_le_ceilBeta hg
  have : 2 ^ 1 ≤ 2 ^ Cost.ceilBeta g := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem clogCost_mono (κ : ℕ) {x y : ℕ} (h : x ≤ y) :
    κ * (x * (Nat.clog 2 x + 1) + 1) ≤ κ * (y * (Nat.clog 2 y + 1) + 1) := by
  apply Nat.mul_le_mul_left
  have := Nat.clog_mono_right 2 h
  have := Nat.mul_le_mul h (Nat.add_le_add_right this 1)
  omega

/-- A short last chain of grade `g ≥ 1` is the single child `2i`. -/
theorem single_child {n g i : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hi : i < gradeCount n g)
    (hl : gradeLen n g i ≤ 2 ^ (g - 1)) :
    gradeCount n (g - 1) ≤ 2 * i + 1 ∧ gradeLen n (g - 1) (2 * i) = gradeLen n g i := by
  have hgg : g - 1 + 1 = g := by omega
  by_cases h : 2 * i + 1 < gradeCount n (g - 1)
  · exfalso
    obtain ⟨h1, h2, -⟩ := gradeLen_succ_two (g := g - 1) hn h
    rw [hgg] at h2
    have := gradeLen_pos (g := g - 1) (i := 2 * i + 1) hn h
    omega
  · refine ⟨by omega, ?_⟩
    have := gradeLen_succ_one (g := g - 1) (i := i) hn (by rwx [hgg]) (by omega)
    rw [hgg] at this; exact this.symm

/-- **The normal form of chain `(g, i)`**, all three cases. -/
theorem nfU_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
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
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R A d : ℕ}
    (hu : URegs c P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R)
    (hA : c.nreg ALLOC = A) (h16 : c.nreg 170016 = gradeStart g i)
    (h17 : c.nreg 170017 = gradeLen P.n g i) (h35 : c.nreg 170035 = 6 * i)
    (hi : i < gradeCount P.n g)
    (hT : Robust A c.nmem fun m => UpTab O P m h hp A ∧ m h = g ∧
      (1 ≤ g → m (m (h + 2) + (g - 1)) = R))
    (h30 : c.nreg 170030 = d) (hd5 : d + 5 ≤ A) (hdh : c.nmem d = hp)
    (hdesc : ∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
      ChainDescAt c.nmem d (Qof P) (Host.whole P.n) C)
    (hW : A + nfB κB κL κG g + 6 ≤ W) :
    ∃ c' k, Exec P W (nfU sB sL sG) c c' k ∧ k ≤ nfB κB κL κG g ∧ WordsBounded W c' ∧
      A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ∃ N, NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (gradeGran g) 4) ∧
      (∀ a, a < A → c'.nmem a = c.nmem a) ∧
      (∀ a, a < A → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, Kept r ∨ r = 170030 → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hfit := gradeLen_fit hn hi
  have hl1 := gradeLen_pos hn hi
  have hl2 := gradeLen_le P.n g i
  have hk0 : ∀ r, Kept r ∨ r = 170030 → bandOf r ∉ pkgBands := fun r hr => by
    rcases hr with hr | rfl
    · exact hr.not_mem (by decide) (by decide) (by decide)
    · decide
  have hkm : ∀ r, Kept r ∨ r = 170030 → ¬ MdRG r := fun r hr => by
    rcases hr with hr | rfl
    · have := hr.range; ufo MdRG
    · ufo MdRG
  have hk31 : ∀ r, Kept r ∨ r = 170030 → r ≠ 170031 := fun r hr => by
    rcases hr with hr | rfl
    · have := hr.range; omega
    · omega
  have hk34 : ∀ r, Kept r ∨ r = 170030 → r ≠ 170034 := fun r hr => by
    rcases hr with hr | rfl
    · have := hr.range; omega
    · omega
  have hkA : ∀ r, Kept r ∨ r = 170030 → r ≠ ALLOC := fun r hr => by
    rcases hr with hr | rfl
    · exact hr.ne_alloc
    · decide
  have hb0 : ∀ r, OutB (bandOf r) → bandOf r ∉ pkgBands := fun r hr => hr.not_mem (by decide)
  -- the chain of the case analysis
  let C0 := gChain P g i hn hi
  rcases Nat.lt_or_ge g 7 with hg7 | hg7
  · -- brute force
    have hb : nfB κB κL κG g = κB * (2 ^ g + 1) ^ 3 + 5 := by unfold nfB; rw [ite_eq_left hg7]
    rw [hb] at hW ⊢
    have hpow : κB * (gradeLen P.n g i + 1) ^ 3 ≤ κB * (2 ^ g + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    obtain ⟨c', k, e, hk, hw', a1, a2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, m1, m2, o, fr, frr⟩ :=
      nfU_brute (P := P) (sL := sL) (sG := sG) hB hG hWh hw hu.r07 hu.r37 hg7 h16 h17 hu.r11
        hl1 (by ufo gradeStart at hfit ⊢) (one_le_gradeGran g)
        (by
          rcases Nat.eq_zero_or_pos g with h0 | h0
          · left; subst h0; have := gradeLen_le P.n 0 i; sio at this
          · exact Or.inr (two_le_gradeGran h0))
        (by rwo [hA])
    refine ⟨c', k, e, by omega, hw', by omega, by omega, fun C' a b f => ?_,
      fun a ha => m1 a (by omega), fun a ha => m2 a (by omega), o,
      fun r hr => fr r (hk0 r hr) (hkm r hr) (hk31 r hr) (hk34 r hr) (hkA r hr),
      fun r hr => frr r (hb0 r hr)⟩
    have : C = C' := chain_eq (hCP.trans a.symm) (hCs.trans b.symm) (hCm.trans f.symm)
    subst this; exact ⟨N, hNW, hc⟩
  · have hb : nfB κB κL κG g = κL * (lemma41Nat g + 1) + 8 +
        (κG 4 * (FB g * (Nat.clog 2 (FB g) + 1) + 1) + 37) := by
      unfold nfB; rw [ite_eq_right (by omega)]
    rw [hb] at hW ⊢
    have hTh := hT.holds
    obtain ⟨hTab, hmh, hR⟩ := hTh
    by_cases hlen : 2 ^ (g - 1) < gradeLen P.n g i
    · -- Lemma 4.1
      have hX : (gradeCtx O).holds P c.nmem h A :=
        holds_of_upTab hn (robust_of hT le_rfl fun m' h' => h'.1)
      obtain ⟨c', k, e, hk, hw', a1, a2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, m1, m2, o, fr, frr⟩ :=
        nfU_l41 (P := P) (sB := sB) (sG := sG) hL hG hWh hw hu.r07 hu.r37 hg7 hu.r19 hu.r05 h16
          h17 (by rwx [hA]) (by omega) (by ufo gradeStart at hfit ⊢) hlen hl2
          (by rwo [hA])
      refine ⟨c', k, e, by omega, hw', by omega, by omega, fun C' a b f => ?_,
      fun a ha => m1 a (by omega), fun a ha => m2 a (by omega), o,
        fun r hr => fr r (hk0 r hr) (hkm r hr) (hk31 r hr) (hk34 r hr) (hkA r hr),
        fun r hr => frr r (hb0 r hr)⟩
      have : C = C' := chain_eq (hCP.trans a.symm) (hCs.trans b.symm) (hCm.trans f.symm)
      subst this; exact ⟨N, hNW, hc⟩
    · -- coarsening the child
      have hg1 : 1 ≤ g := by omega
      obtain ⟨hsc, hlc⟩ := single_child hn hg1 hi (by omega)
      have h2i := two_mul_lt_gradeCount hg1 hi
      have hR' := hR hg1
      obtain ⟨-, -, -, hH, hhp, -, -, hrow, hE⟩ := hTab
      have hgm : g - 1 < c.nmem h := by omega
      have hrw := hrow (g - 1) hgm
      rw [hR'] at hrw
      obtain ⟨hNL, -⟩ := hE (g - 1) (2 * i) hgm h2i
      have e6 : ∀ x, x + 3 * (2 * i) = x + 6 * i := fun x => by ring
      simp [rowE, hR', e6] at hNL
      have hsc' : gradeStart (g - 1) (2 * i) = gradeStart g i := by
        rw [← gradeStart_succ, show g - 1 + 1 = g by omega]
      obtain ⟨-, -, -, -, -, -, N, hNW, hc⟩ := hNL C0 rfl hsc'.symm hlc.symm
      have hP : C0.P.Simple := (shearInvariance (epsOf P) P).1 hG.1
      have hcnt := nChords_mul_le hP hc
      have hFB : c.nmem (c.nmem (R + 6 * i + 1)) ≤ FB g := by
        have hNA := hNW.holds
        rw [hNA.1]
        unfold FB
        rw [Nat.le_div_iff_mul_le (by omega)]
        refine le_trans hcnt (Nat.mul_le_mul_left _ ?_)
        show 2 * gradeLen P.n g i + 8 ≤ 2 ^ g + 8
        have : 2 ^ g = 2 * 2 ^ (g - 1) := by
          rw [← pow_succ', show g - 1 + 1 = g by omega]
        omega
      have hcm := clogCost_mono (κG 4) hFB
      obtain ⟨c', k, e, hk, hw', a1, a2, ⟨N', hNW', hc'⟩, m1, m2, o, fr, frr⟩ :=
        nfU_gran (P := P) (sB := sB) (sL := sL) (C := C0) (N := N) (hp := hp) (q := 6 * i)
          hGr hG hWh hw hu.r07 hu.r37 hg7 hu.r19 h17 (by omega) hu.r14 h35 (by omega) rfl hA
          h30 hu.r11 hu.r20 hu.r25 hu.r26 hu.r29 (hdesc C0 rfl rfl rfl) hdh hd5 (by omega) rfl
          (by show gradeStart g i + gradeLen P.n g i + 1 ≤ P.n; exact hfit) hNW hc
          (gradeGran_mono (by omega)) (by omega)
      refine ⟨c', k, e, by omega, hw', a1, a2, fun C' a b f => ?_,
      fun a ha => m1 a (by omega), fun a ha => m2 a (by omega), o,
        fun r hr => fr r (hk0 r hr) (hkm r hr) (hk31 r hr) (hk34 r hr) (hkA r hr),
        fun r hr => frr r (hb0 r hr)⟩
      have : C0 = C' := chain_eq a.symm b.symm f.symm
      subst this; exact ⟨N', hNW', hc'⟩

end proofs

end

end Chazelle.Core.Up
