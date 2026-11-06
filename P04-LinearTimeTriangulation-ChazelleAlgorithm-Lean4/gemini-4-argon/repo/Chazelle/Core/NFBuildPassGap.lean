module

public import Chazelle.Core.NFBuildPassArc

/-!
# WP-C (BuildNF), RAM part 11: the gap test of the main pass

`gapS_exec`: at position `m` of the sorted codes `E` (at `SE`), with the walk position of `E[m]`
in `r42110`, `r42111`: if `m + 1 = 2K` or the key strictly increases from `E[m]` to `E[m + 1]`,
the arc record (region `r43117`, ends `E[m]` and `E[(m + 1) mod 2K]`) and its weight are written
at `AT + 5 A`, `WT + A`, and `A` is incremented; otherwise nothing changes.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (wposOf)

@[expose] public section

/-- The registers `gapS` writes. -/
def Bgap (r : ℕ) : Bool :=
  Barc r || BhalfS 42116 42117 r || decide (r = 43106 ∨ r = 43140 ∨ r = 43141 ∨ r = 43142) ||
    decide (42113 ≤ r ∧ r < 42116) || decide (r = 43120)

theorem wr_gapS : wrM Bgap gapS = true := by
  have h1 : wrM Bgap arcS = true := wrM_mono (fun r hr => by simp [Bgap, hr]) wr_arcS
  have h2 : wrM Bgap (halfS 42110 42111 42113 42114 42116 42117) = true :=
    wrM_of_wr (wr_mono (fun r hr => by simp [Bgap, hr]) wr_halfS)
  simp only [gapS, wrM, block, loadRec, h1, h2, Bool.and_true, Bool.true_and]
  decide

theorem Bgap_false {r : ℕ} (h : r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40103 ≤ r ∧ r < 41110) ∨
    (41120 ≤ r ∧ r < 42113) ∨ (42117 < r ∧ r < 43102) ∨ (43102 < r ∧ r < 43106) ∨
    (43106 < r ∧ r < 43120) ∨ (43128 ≤ r ∧ r < 43140) ∨ (43142 < r ∧ r < 43150) ∨ 43151 < r) :
    Bgap r = false := by
  have ha := Barc_false (r := r) (by omega)
  simp only [Bgap, ha, BhalfS, Bhalf, Bool.false_or, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega

theorem bhalf_of_bgap {r : ℕ} (h : Bgap r = false) : BhalfS 42116 42117 r = false := by
  simp only [Bgap, Bool.or_eq_false_iff] at h; exact h.1.1.1.2

theorem ne_of_bgap {r : ℕ} (h : Bgap r = false) : r ≠ 43106 ∧ r ≠ 43140 ∧ r ≠ 43141 ∧
    r ≠ 43142 ∧ r ≠ 42113 ∧ r ≠ 42114 ∧ r ≠ 42115 ∧ r ≠ 43120 := by
  simp only [Bgap, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  omega

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The gap test and the arc.** -/
theorem gapS_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config)
    (hw : WordsBounded W d) {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE m A AT WT : ℕ} (hL : ChordTriplesOK M (Qof P) L)
    (hElen : E.length = 2 * L.length) (hEc : ∀ j, j < E.length → E.getD j 0 < 2 * L.length)
    (hm : m < E.length) (h100 : d.nreg 43100 = m) (hN : d.nreg 42001 = E.length)
    (h103 : d.nreg 43103 = SE + m) (h104 : d.nreg 43104 = SE)
    (hSE : ∀ j, j < E.length → d.nmem (SE + j) = E.getD j 0)
    (hT : d.nreg 42000 = T) (hR : RecsAt d.nmem T L) (h102 : d.nreg 42102 = 1)
    (h110 : d.nreg 42110 = (wposOf L (E.getD m 0)).edge)
    (h111 : d.nreg 42111 = (wposOf L (E.getD m 0)).hgt)
    (hD : d.nreg 40000 = D) (hwf : ModelDescWF P H d.nmem D) (hM : ModelDescAt d.nmem D (Qof P) M)
    (hHW : H ≤ W) (h23 : d.nreg 41023 = d.nmem D) (h19 : d.nreg 41019 = 1)
    (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT) (hWT : d.nreg 44007 = WT)
    (h1 : d.nreg 43011 = 1) (hATH : H ≤ AT) (hWTH : H ≤ WT)
    (hATW : AT + 5 * A + 4 ≤ W) (hWTW : WT + A + 1 ≤ W) (hTW : T + 8 * L.length ≤ H)
    (hSEW : SE + E.length ≤ W)
    (hcI : ∀ p, p < M.W.n → (M.counted p ↔ d.nreg 44020 ≤ p ∧ p < d.nreg 44020 + d.nreg 44021)) :
    ∃ d' k, Exec P W gapS d d' k ∧ k ≤ 11600 ∧ FrameM Bgap d d' ∧
      ((m + 1 = E.length ∨ M.key (Qof P) (wposOf L (E.getD m 0)) <
          M.key (Qof P) (wposOf L (E.getD ((m + 1) % E.length) 0))) →
        d'.nreg 43102 = A + 1 ∧
        ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted (wposOf L (E.getD ((m + 1) % E.length) 0)).edge ∧
            M.param (Qof P) (wposOf L (E.getD ((m + 1) % E.length) 0)) ≠ 0) ∧
          d'.nmem = upd (wr5 d.nmem (AT + 5 * A) (d.nreg 43117)
              (wposOf L (E.getD m 0)).edge (wposOf L (E.getD m 0)).hgt
              (wposOf L (E.getD ((m + 1) % E.length) 0)).edge
              (wposOf L (E.getD ((m + 1) % E.length) 0)).hgt) (WT + A)
            (wtG (d.nreg 44020) (d.nreg 44021) (wposOf L (E.getD m 0)).edge
              (wposOf L (E.getD ((m + 1) % E.length) 0)).edge pz
              (if m + 1 < E.length then 1 else 0))) ∧
      (¬ (m + 1 = E.length ∨ M.key (Qof P) (wposOf L (E.getD m 0)) <
          M.key (Qof P) (wposOf L (E.getD ((m + 1) % E.length) 0))) →
        d'.nreg 43102 = A ∧ d'.nmem = d.nmem) := by
  have hn : (Qof P).n = P.n := shear_n _ _
  have hW' : P.n + 3 ≤ W := by unfold hostWords at hWn; omega
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf hHW hWn
  set N := E.length
  set m' := (m + 1) % N with hm'
  have hm'N : m' < N := Nat.mod_lt _ (by omega)
  set c := E.getD m 0
  set c' := E.getD m' 0 with hc'
  have hcK := hEc m hm
  have hc'K := hEc m' hm'N
  have pe := properPos_ev hL hc'K
  have ee := edge_lt hL hc'K
  obtain ⟨r0, r1, -, -⟩ := hR c' hc'K
  -- the step `m + 1`
  have x₀ := Exec.addN (P := P) hw 43106 43100 43011 (by rw [h100, h1]; omega)
  set d₀ : Config := { d with nreg := upd d.nreg 43106 (d.nreg 43100 + d.nreg 43011) } with hd₀
  have w₀ := x₀.wb_right
  have g₀ : ∀ r, r ≠ 43106 → d₀.nreg r = d.nreg r := fun r hr => by rw [hd₀]; simp [hr]
  have v₀ : d₀.nreg 43106 = m + 1 := by rw [hd₀]; simp [h100, h1]
  -- loading the end code and its record, common to both branches
  have load : ∀ {e : Config}, WordsBounded W e → e.nmem = d.nmem → e.nreg 43141 = c' →
      e.nreg 42000 = T → e.nreg 42102 = 1 →
      ∃ e' k, Exec P W (loadRec 43141 43142 42113) e e' k ∧ k = 8 ∧
        e'.nreg 42113 = (wposOf L c').edge ∧ e'.nreg 42114 = (wposOf L c').hgt ∧
        (∀ r, r ≠ 43142 → r ≠ 42113 → r ≠ 42114 → r ≠ 42115 → e'.nreg r = e.nreg r) ∧
        e'.nmem = e.nmem := fun {e} we me e141 e42 e102 => by
    obtain ⟨e', k, x, hk, v1, v2, -, fr, mm, -⟩ := loadRec_exec (P := P) e we
      (src := 43141) (ad := 43142) (o := 42113) (c := c') (T := T) e141 e42 e102
      (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
    exact ⟨e', k, x, hk, by rw [v1, me, r0], by rw [v2, me, r1], fr, mm⟩
  -- the arc, common to both branches
  have arc : ∀ {e : Config}, WordsBounded W e → e.nmem = d.nmem →
      (∀ r, Bgap r = false → e.nreg r = d.nreg r) → e.nreg 43102 = A →
      e.nreg 42110 = d.nreg 42110 →
      e.nreg 42113 = (wposOf L c').edge → e.nreg 42114 = (wposOf L c').hgt →
      e.nreg 43120 = (if m + 1 < N then 1 else 0) → e.nreg 43117 = d.nreg 43117 →
      e.nreg 44020 = d.nreg 44020 → e.nreg 44021 = d.nreg 44021 →
      ∃ e' k, Exec P W arcS e e' k ∧ k ≤ 6040 ∧ FrameM Barc e e' ∧ e'.nreg 43102 = A + 1 ∧
        ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted (wposOf L c').edge ∧
            M.param (Qof P) (wposOf L c') ≠ 0) ∧
          e'.nmem = upd (wr5 d.nmem (AT + 5 * A) (d.nreg 43117)
              (wposOf L c).edge (wposOf L c).hgt (wposOf L c').edge (wposOf L c').hgt) (WT + A)
            (wtG (d.nreg 44020) (d.nreg 44021) (wposOf L c).edge (wposOf L c').edge pz
              (if m + 1 < N then 1 else 0)) :=
      fun {e} we me fe e102 e110 e113 e114 e120 e117 e20 e21 => by
    obtain ⟨e', k, x, hk, fr, v, pz, pz1, pziff, mm⟩ := arcS_exec (P := P) hG hWn e we (M := M)
      (D := D) (H := H) (A := A) (AT := AT) (WT := WT)
      (by rw [fe _ (Bgap_false (by omega)), hD]) (by rwa [me]) (by rwa [me]) hHW
      (by rw [fe _ (Bgap_false (by omega)), h23, me]) (by rw [fe _ (Bgap_false (by omega)), h19])
      e102 (by rw [fe _ (Bgap_false (by omega)), hAT])
      (by rw [fe _ (Bgap_false (by omega)), hWT]) (by rw [fe _ (Bgap_false (by omega)), h1])
      (by rw [e120]; split_ifs <;> omega) (by rwa [e113]) (by rw [e114]; exact pe.2.2)
      hATH hWTH hATW hWTW (by rwa [e20, e21])
    refine ⟨e', k, x, hk, fr, v, pz, pz1, by rwa [e113, e114] at pziff, ?_⟩
    rw [mm, me, e117, e110, h110, fe 42111 (Bgap_false (by omega)), h111, e113, e114, e20, e21,
      e120]
  unfold gapS
  refine spec_seq ⟨d₀, 1, x₀, ?_⟩
  have hsame : d₀.nmem = d.nmem := rfl
  by_cases hlt : m + 1 < N
  · -- no wrap: compare with `E[m + 1]`
    have hm'e : m' = m + 1 := Nat.mod_eq_of_lt hlt
    refine spec_ifLtN_true (by rwa [v₀, g₀ _ (by norm_num), hN]) ?_
    obtain ⟨d₁, X1, g₁, v₁, mm₁⟩ : ∃ d₁, Exec P W (block [.addN 43140 43103 43011,
        .loadN 43141 43140]) d₀ d₁ 2 ∧ (∀ r, r ≠ 43140 → r ≠ 43141 → d₁.nreg r = d₀.nreg r) ∧
        d₁.nreg 43141 = c' ∧ d₁.nmem = d.nmem := by
      have y1 := Exec.addN (P := P) w₀ 43140 43103 43011 (by
        rw [g₀ _ (by norm_num), g₀ _ (by norm_num), h103, h1]; omega)
      have y2 := Exec.loadN (P := P) y1.wb_right 43141 43140
      refine ⟨_, .seq y1 (.seq y2 (.skip y2.wb_right)), fun r a1 a2 => by simp [a1, a2], ?_, rfl⟩
      simp only [upd_same]
      rw [g₀ _ (by norm_num), g₀ _ (by norm_num), h103, h1, hsame, show SE + m + 1 = SE + (m + 1)
        by omega, hSE _ hlt, hc', hm'e]
    have w₁ := X1.wb_right
    obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, g₂, mm₂⟩ := load w₁ mm₁ v₁
      (by rw [g₁ _ (by norm_num) (by norm_num), g₀ _ (by norm_num), hT])
      (by rw [g₁ _ (by norm_num) (by norm_num), g₀ _ (by norm_num), h102])
    have w₂ := x₂.wb_right
    have G₂ : ∀ r, r ≠ 43106 → r ≠ 43140 → r ≠ 43141 → r ≠ 43142 → r ≠ 42113 → r ≠ 42114 →
        r ≠ 42115 → d₂.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
      rw [g₂ r a4 a5 a6 a7, g₁ r a2 a3, g₀ r a1]
    have hD₂ : d₂.nreg 40000 = D := by
      rw [G₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), hD]
    have mm₂' : d₂.nmem = d.nmem := by rw [mm₂, mm₁]
    have pc := properPos_ev hL hcK
    have ec := edge_lt hL hcK
    obtain ⟨d₃, k₃, x₃, hk₃, -, dst₃, f₃⟩ := halfS_exec (P := P) hG hW' d₂ w₂
      (qe := 42110) (qh := 42111) (se := 42113) (sh := 42114) (dd := 42116) (dst := 42117)
      (by decide) (by decide) (by decide) (by rwa [hD₂]) (by rwa [hD₂, mm₂'])
      (M := M) (by rwa [hD₂, mm₂'])
      (by rwa [G₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), h110])
      (by rw [G₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), h111]; exact pc.2.2)
    have w₃ := x₃.wb_right
    have hbit : d₃.nreg 42117 = if M.key (Qof P) (wposOf L c') ≤ M.key (Qof P) (wposOf L c)
        then 1 else 0 := by
      rw [dst₃, G₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), G₂ 42111 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num), h110, h111, e₂, h₂]
      have := keyDec_ev hL hc'K hcK
      by_cases hk : M.key (Qof P) (wposOf L c') ≤ M.key (Qof P) (wposOf L c)
      · rw [ite_eq_left (this.2 hk), ite_eq_left hk]
      · rw [ite_eq_right (fun h => hk (this.1 h)), ite_eq_right hk]
    have G₃ : ∀ r, Bgap r = false → d₃.nreg r = d.nreg r := fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := ne_of_bgap hr
      rw [f₃.1 r (bhalf_of_bgap hr), G₂ r n1 n2 n3 n4 n5 n6 n7]
    have o₃ : d₃.nreg 43011 = 1 := by rw [G₃ _ (Bgap_false (by omega)), h1]
    have mm₃ : d₃.nmem = d.nmem := by rw [f₃.2.2.1, mm₂']
    have e113₃ : d₃.nreg 42113 = (wposOf L c').edge := by rw [f₃.1 _ (by decide), e₂]
    have e114₃ : d₃.nreg 42114 = (wposOf L c').hgt := by rw [f₃.1 _ (by decide), h₂]
    have e102₃ : d₃.nreg 43102 = A := by
      rw [f₃.1 _ (by decide), G₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), hA]
    have X0 : ∀ {s : Stmt} {d' : Config} {k : ℕ}, Exec P W s d₃ d' k →
        Exec P W (.seq (block [.addN 43140 43103 43011, .loadN 43141 43140])
          (.seq (loadRec 43141 43142 42113) (.seq (halfS 42110 42111 42113 42114 42116 42117) s)))
          d₀ d' (2 + (k₂ + (k₃ + k))) := fun x => .seq X1 (.seq x₂ (.seq x₃ x))
    by_cases hg : M.key (Qof P) (wposOf L c) < M.key (Qof P) (wposOf L c')
    · -- a gap: the arc
      have b0 : d₃.nreg 42117 = 0 := by rw [hbit, ite_eq_right (not_le.2 hg)]
      have z1 := Exec.constN (P := P) w₃ 43120 1 (by have := hw.1 43011; omega)
      set d₄ : Config := { d₃ with nreg := upd d₃.nreg 43120 1 } with hd₄
      have g₄ : ∀ r, r ≠ 43120 → d₄.nreg r = d₃.nreg r := fun r hr => by rw [hd₄]; simp [hr]
      obtain ⟨d₅, k₅, x₅, hk₅, fr₅, v₅, pz, pz1, pziff, mm₅⟩ := arc z1.wb_right
        (by rwa [hd₄])
        (fun r hr => by rw [g₄ r (ne_of_bgap hr).2.2.2.2.2.2.2, G₃ r hr])
        (by rw [g₄ _ (by norm_num), e102₃])
        (by rw [g₄ _ (by norm_num), G₃ _ (Bgap_false (by omega))])
        (by rw [g₄ _ (by norm_num), e113₃]) (by rw [g₄ _ (by norm_num), e114₃])
        (by rw [hd₄]; simp [hlt])
        (by rw [g₄ _ (by norm_num), G₃ _ (Bgap_false (by omega))])
        (by rw [g₄ _ (by norm_num), G₃ _ (Bgap_false (by omega))])
        (by rw [g₄ _ (by norm_num), G₃ _ (Bgap_false (by omega))])
      have X := X0 (.ifLtN_true (a := 42117) (b := 43011) (e := .skip)
        (show d₃.nreg 42117 < d₃.nreg 43011 by rw [b0, o₃]; omega) (.seq z1 x₅))
      refine ⟨d₅, _, X, by omega, exec_frameM (Exec.seq x₀ (Exec.ifLtN_true (a := 43106)
        (b := 42001) (by rwa [v₀, g₀ _ (by norm_num), hN]) X)) wr_gapS,
        fun _ => ⟨v₅, pz, pz1, pziff, mm₅⟩, fun h => absurd (Or.inr hg) h⟩
    · -- no gap
      have b1 : d₃.nreg 42117 = 1 := by rw [hbit, ite_eq_left (not_lt.1 hg)]
      have X := X0 (.ifLtN_false (a := 42117) (b := 43011) (t := .seq (.instr (.constN 43120 1)) arcS)
        (show ¬ d₃.nreg 42117 < d₃.nreg 43011 by rw [b1, o₃]; omega) (.skip w₃))
      refine ⟨d₃, _, X, by omega, exec_frameM (Exec.seq x₀ (Exec.ifLtN_true (a := 43106)
        (b := 42001) (by rwa [v₀, g₀ _ (by norm_num), hN]) X)) wr_gapS,
        fun h => absurd h (by rintro (h | h); omega; exact hg h), fun _ => ⟨e102₃, mm₃⟩⟩
  · -- the wrap: the end is `E[0]`
    have hmN : m + 1 = N := by omega
    have hm'e : m' = 0 := by rw [hm', hmN, Nat.mod_self]
    refine spec_ifLtN_false (by rwa [v₀, g₀ _ (by norm_num), hN]) ?_
    have y1 := Exec.loadN (P := P) w₀ 43141 43104
    obtain ⟨d₁, X1, g₁, v₁, mm₁⟩ : ∃ d₁, Exec P W (.instr (.loadN 43141 43104)) d₀ d₁ 1 ∧
        (∀ r, r ≠ 43141 → d₁.nreg r = d₀.nreg r) ∧ d₁.nreg 43141 = c' ∧ d₁.nmem = d.nmem := by
      refine ⟨_, y1, fun r a1 => by simp [a1], ?_, rfl⟩
      simp only [upd_same]
      rw [g₀ _ (by norm_num), h104, hsame, ← Nat.add_zero SE, hSE 0 (by omega), hc', hm'e]
    have w₁ := X1.wb_right
    obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, g₂, mm₂⟩ := load w₁ mm₁ v₁
      (by rw [g₁ _ (by norm_num), g₀ _ (by norm_num), hT])
      (by rw [g₁ _ (by norm_num), g₀ _ (by norm_num), h102])
    have w₂ := x₂.wb_right
    have G₂ : ∀ r, Bgap r = false → d₂.nreg r = d.nreg r := fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := ne_of_bgap hr
      rw [g₂ r n4 n5 n6 n7, g₁ r n3, g₀ r n1]
    have e102₂ : d₂.nreg 43102 = A := by
      rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g₁ _ (by norm_num),
        g₀ _ (by norm_num), hA]
    have z1 := Exec.constN (P := P) w₂ 43120 0 (Nat.zero_le _)
    set d₄ : Config := { d₂ with nreg := upd d₂.nreg 43120 0 } with hd₄
    have g₄ : ∀ r, r ≠ 43120 → d₄.nreg r = d₂.nreg r := fun r hr => by rw [hd₄]; simp [hr]
    obtain ⟨d₅, k₅, x₅, hk₅, fr₅, v₅, pz, pz1, pziff, mm₅⟩ := arc z1.wb_right
      (by rw [hd₄]; show d₂.nmem = d.nmem; rw [mm₂, mm₁])
      (fun r hr => by rw [g₄ r (ne_of_bgap hr).2.2.2.2.2.2.2, G₂ r hr])
      (by rw [g₄ _ (by norm_num), e102₂])
      (by rw [g₄ _ (by norm_num), G₂ _ (Bgap_false (by omega))])
      (by rw [g₄ _ (by norm_num), e₂]) (by rw [g₄ _ (by norm_num), h₂])
      (by rw [hd₄]; simp [hlt])
      (by rw [g₄ _ (by norm_num), G₂ _ (Bgap_false (by omega))])
      (by rw [g₄ _ (by norm_num), G₂ _ (Bgap_false (by omega))])
      (by rw [g₄ _ (by norm_num), G₂ _ (Bgap_false (by omega))])
    have X : Exec P W (.seq (.instr (.loadN 43141 43104)) (.seq (loadRec 43141 43142 42113)
        (.seq (.instr (.constN 43120 0)) arcS))) d₀ d₅ (1 + (k₂ + (1 + k₅))) :=
      .seq X1 (.seq x₂ (.seq z1 x₅))
    refine ⟨d₅, _, X, by omega, exec_frameM (Exec.seq x₀ (Exec.ifLtN_false (a := 43106)
      (b := 42001) (by rwa [v₀, g₀ _ (by norm_num), hN]) X)) wr_gapS,
      fun _ => ⟨v₅, pz, pz1, pziff, mm₅⟩, fun h => absurd (Or.inl hmN) h⟩


end exec

end

end BuildRam

end Chazelle.Core
