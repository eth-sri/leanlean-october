module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41ExecB
public import Chazelle.Core.Lemma41Levels

/-!
# WP-J, part 26: Lemma 4.1 on the RAM, executed

`l41_exec`: from the precondition of `Lemma41Spec` (and a word budget `A + l41Big`), the program
`l41S sM` computes a `γ'_λ`-canonical normal form of the chain `v_a … v_{a+L}` of `Q`, robust
below the new allocator, within `l41Big` steps and the frame of `l41Bands`: the prologue
(`l41A_exec`), the leaves (`l41B_exec`), the merge tree (`tree_exec`) and the output.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle Chazelle.Merge

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}


/-- **Lemma 4.1 on the RAM.** -/
theorem l41_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} (hMM : MergeMeets sM κ F G H (gradeCtx O) OkModel)
    (hF : Monotone F) (hGm : Monotone G) (hH : Monotone H)
    {c : Config} (hw : WordsBounded W c) {A h a L lam : ℕ}
    (hA : c.nreg ALLOC = A) (r0 : c.nreg 160000 = h) (r1 : c.nreg 160001 = a)
    (r2 : c.nreg 160002 = L) (r3 : c.nreg 160003 = lam)
    (hX : (gradeCtx O).holds P c.nmem h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ (lam - 1) < L) (hL2 : L ≤ 2 ^ lam)
    (hbud : A + l41Big κ F G H lam a L ≤ W) :
    ∃ c' k, Exec P W (l41S sM) c c' k ∧ k ≤ l41Big κ F G H lam a L ∧
      (∃ C N, C.P = Qof P ∧ C.s = a ∧ C.m = L ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg 160004) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran lam) 4) ∧
      Frame l41Bands c c' k := by
  have hAl : ALLOC = 9999 := rfl
  have hWn : P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  have hR := hX
  have hBig0 : 40 * lam ^ 2 + 169 * lam + 84 + 11 * (cover lam (a + L) a).length ≤
      l41Big κ F G H lam a L := by unfold l41Big; omega
  have hsqpos : lam ≤ lam ^ 2 := by nlinarith
  -- the prologue
  obtain ⟨c5, k5, e5, hk5, hk5', hw5, h5A, hhost, m5c, rr5, rm5, o5, fr5, s00, s10, s11, s14, s15, s20,
      s21, s22, s24, s26, s27, s32, s33, s80, s81, s82, s83, s84, s87⟩ :=
    l41A_exec hG hWh hw hA r0 r1 r2 r3 hR hlΛ h7 han hL1 hL2 (by omega)
  -- the leaves
  obtain ⟨c8, k8, e8, hk8, hw8, h8A, h8Ak, hLev, m8c, s8_14, s8_66, fr8, rr8, rm8, o8⟩ :=
    l41B_exec hG hWh hw5 hR hlΛ h7 han hL1 hL2 m5c hhost h5A s10 s11 s14 s15 s20 s21 s22 s24
      s26 s27 s81 s82 s87 (by omega)
  have hj2l : (cover lam (a + L) a).length ≤ 2 * lam := cover_length_le (by omega) (by omega)
  have hj2 : 2 ≤ (cover lam (a + L) a).length := two_le_cover (by omega) (by omega)
  obtain ⟨j, hj⟩ : ∃ j, (cover lam (a + L) a).length = j := ⟨_, rfl⟩
  rw [hj] at hk8 h8A hLev s8_14 s8_66 hj2l hj2 hBig0
  have c85 : ∀ r, 160000 ≤ r → r < 160090 → ¬ CovRG r → ¬ L0RG r → r ≠ 160066 →
      c8.nreg r = c5.nreg r := fun r a1 a2 a3 a4 a5 => fr8 r a3 a4 a5 (by rw [hAl]; omega)
  have s8 : ∀ r, (r = 160000 ∨ r = 160024 ∨ r = 160032 ∨ r = 160033 ∨ r = 160080 ∨
      r = 160081 ∨ r = 160083 ∨ r = 160084) → c8.nreg r = c5.nreg r := fun r hr =>
    c85 r (by omega) (by omega) (by unfold CovRG AscRG; omega) (by unfold L0RG; omega) (by omega)
  -- the merge tree
  have hlen0 : (leafShp lam (a + L) a).length = j := by rw [leafShp_length, hj]
  have hgran0 := leafShp_gran (lam := lam) (b := a + L) (a := a)
  have hstep := gradeGran_step (lam - 1)
  rw [show lam - 1 + 1 = lam by omega] at hstep
  have hcj : Nat.clog 2 j ≤ Nat.clog 2 lam + 1 := clog_le_of_le_two_mul hj2l
  have hfl : fuseLoss = 1 := rfl
  have hGcap := gradeGran_cap (g := lam) h7
  have hG0cl : gradeGran (lam - 1) + Nat.clog 2 j ≤ gradeGran lam := by
    rw [hfl] at hstep; omega
  have hXs : (gradeCtx O).holds P c8.nmem h (c8.nreg ALLOC) := by
    rw [h8A]
    exact (gradeCtx O).mono _ _ _ _ _ (by omega)
      ((gradeCtx O).local_ _ _ _ _ _ (fun x hx => (m8c x hx).symm) hX)
  have hst0 : TreeSt P W (gradeCtx O) c8 (c8.nreg ALLOC) A h (gradeGran lam) a L
      (leafShp lam (a + L) a) (gradeGran (lam - 1)) c8 := by
    refine ⟨hw8, by rw [s8_14, hlen0], by rw [s8 _ (by decide)]; exact s33,
      ⟨A + 7 + 6 * j, s8_66, by rw [h8A, hlen0]; omega, by rw [h8A]; exact hLev⟩,
      leafShp_consec _ _ _, by omega, leafShp_first (lam := lam) (b := a + L) (a := a) (by omega),
      by rw [leafShp_sum]; omega, fun k hk => (hgran0 k hk).1,
      fun k hk => (hgran0 k hk).2, fun h1 => by omega, by rw [hlen0]; exact hG0cl, le_rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, hXs, rfl⟩
  have hPI : PInv (gradeGran (lam - 1)) (gradeGran lam) j L (leafKb lam a L)
      (leafShp lam (a + L) a) (gradeGran (lam - 1)) := by
    refine ⟨by omega, by omega, by rw [leafShp_sum]; omega, by rw [hlen0]; exact hG0cl,
      le_rfl, le_rfl, fun x hx hxl => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := (hgran0 k hk).1
    unfold nd at this
    rw [List.getD_eq_getElem _ _ hk] at this
    unfold leafP at hxl
    simp only [decide_eq_false_iff_not] at hxl
    omega
  have hTC := totCost_le κ F G H hF hGm hH (Gl := gradeGran lam) (G0 := gradeGran (lam - 1))
    (J := j) (L := L)
    (LS0 := leafKb lam a L) j (leafShp lam (a + L) a) (gradeGran (lam - 1)) (by omega) hPI
  rw [hlen0] at hTC
  have hBig2 : 40 * lam ^ 2 + 169 * lam + 84 + 11 * j +
      Nat.clog 2 j * (lvBound κ F G H (gradeGran lam) (gradeGran (lam - 1)) j L (leafKb lam a L) + 2) =
      l41Big κ F G H lam a L := by unfold l41Big; rw [hj]
  have hGcapX : gradeGran lam ≤ (gradeCtx O).cap P c8.nmem h := by
    show gradeGran lam ≤ 2 ^ (c8.nmem h - 1)
    have hh : h < A := le_lt hR (x := h) (v := topGrade P.n + 1) fun m' _ hm' => hm'.1
    rw [m8c h hh]
    have hGcap := gradeGran_cap (g := lam) h7
    have : 2 ^ (lam - 1) ≤ 2 ^ (c.nmem h - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨c9, k9, ns', γ', e9, hk9, h9A, hlen', hst9⟩ :=
    tree_exec hG hWh hWn hMM (gradeCtx_capLocal O) (fun C hC => okModel_chain hG C hC)
      (by rw [s8 _ (by decide)]; exact s32) (by rw [s8 _ (by decide)]; exact s00)
      (by rw [s8 _ (by decide)]; exact s24) (by rw [s8 _ (by decide)]; exact s80)
      (by rw [s8 _ (by decide)]; exact s81) (by rw [s8 _ (by decide)]; exact s83)
      (by rw [s8 _ (by decide)]; exact s84) hGcapX (by omega) j (leafShp lam (a + L) a)
      (gradeGran (lam - 1)) c8 (by omega) hst0
      (by rw [h8A]; omega)
  obtain ⟨hw9, -, -, ⟨B9, h9_66, hB9, hLev9⟩, -, -, hfirst, hsum, -, -, hone, -, hAs9, hm98,
    hrm98, ho98, fr98, frr98, -, -⟩ := hst9
  -- the single node
  obtain ⟨C, hCs, hCm, hN⟩ := hLev9 0 (by omega)
  have hγ1 := hone hlen'
  have hCm' : C.m = L := by
    rw [hCm]
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen'
    subst hx
    simpa [nd] using hsum
  have hCs' : C.s = a := by rw [hCs]; exact hfirst
  have nLv : ∀ r, (r < 160000 ∨ 170000 ≤ r) → ¬ LvRG r := fun r hr => by
    unfold LvRG PairRG DescRG RbRG; omega
  have s9_24 : c9.nreg 160024 = 1 := by
    rw [fr98 _ (bandOK_l41 (by decide) (by decide)) (by unfold LvRG PairRG DescRG RbRG; decide)
      (by rw [hAl]; decide), s8 _ (by decide)]; exact s24
  have hB9W : B9 + 1 ≤ W := by have := hw9.1 ALLOC; omega
  obtain ⟨c10, k10, e10, hk10, hw10, t04, fr10, hm10, hrr10, hrm10, ho10⟩ :=
    epiB_exec (P := P) hw9 h9_66 s9_24 hB9W
  have c10A : c10.nreg ALLOC = c9.nreg ALLOC :=
    fr10 _ (by rw [hAl]; decide) (by rw [hAl]; decide)
  obtain ⟨-, hCP, -, -, -, -, N, hNW, hc⟩ := hN
  simp only [Nat.mul_zero, Nat.add_zero] at hNW
  rw [hγ1] at hc
  refine ⟨c10, k5 + (k8 + (k9 + k10)), .seq e5 (.seq e8 (.seq e9 e10)), ?_,
    ⟨C, N, hCP, hCs', hCm', ?_, hc⟩, ?_⟩
  · have hs : k5 + (k8 + (k9 + k10)) ≤ 40 * lam ^ 2 + 169 * lam + 84 + 11 * j +
        Nat.clog 2 j * (lvBound κ F G H (gradeGran lam) (gradeGran (lam - 1)) j L (leafKb lam a L) + 2) := by omega
    rw [hBig2] at hs; exact hs
  · rw [c10A, hm10, t04]; exact hNW
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
    · obtain ⟨hr1, hr2⟩ := bandOf_not_l41 hr
      rw [fr10 r (by omega) (by omega), fr98 r hr2 (nLv r hr1) hra,
        fr8 r (by unfold CovRG AscRG; omega) (by unfold L0RG; omega) (by omega) hra]
      exact fr5 r hr1 hra
    · obtain ⟨hr1, hr2⟩ := bandOf_not_l41 hr
      rw [hrr10, frr98 r hr2 (nLv r hr1), rr8, rr5]
    · rw [hA] at hx; rw [hm10, hm98 x (by omega), m8c x hx]
    · rw [hA] at hx; rw [hrm10, hrm98 x (by omega), rm8, rm5]
    · rw [ho10, ho98, o8, o5]
    · rw [c10A, hA]; omega
    · rw [c10A, hA]; omega

end proofs

end

end Chazelle.Core.L41
