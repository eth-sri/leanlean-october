module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvLoopStartR

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, RAM part 2: one stop step)

`stStep_irs`: from `StI`, one stop step keeps `StI`, advances `sP` iff the stop `sP` lies at the
start key, and writes only the registers `WS` (inside `StR`) and the oracle bands.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

section
variable {l : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {i : ℕ} (h : i < l.length)
include h
theorem getD_d5 :
    l.getD i (0, 0, 0, 0, 0) = l[i] := List.getD_eq_getElem _ _ h

theorem getD_d5' :
    l.getD i d5 = l[i] := List.getD_eq_getElem _ _ h


end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **One stop step.** -/
theorem stStep_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {J : Merge.Junction} {N₁ N₂ : NF}
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hSD : StopData P J N₂ c rs ax)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hS : StI P J N₂ rs ax c) (hkE : c.nreg kE = pK0 J) (hkH : c.nreg kH = 0)
    (hroom : c.nreg ALLOC + stStepK ≤ W) :
    IRS P W c₀ stStep c stStepK (fun c' => StI P J N₂ rs ax c' ∧
      (∀ hi : c.nreg sP < rs.length, soff P J rs[c.nreg sP] = Lst J →
        c'.nreg sP = c.nreg sP + 1) ∧
      ((∀ hi : c.nreg sP < rs.length, soff P J rs[c.nreg sP] ≠ Lst J) →
        c'.nreg sP = c.nreg sP) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ WS r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨hl, hlax, hSR, hAR, hst, hw, haux, -⟩ := hSD
  obtain ⟨sN, sP2, sPl, sAt, sLen, sLab, sReg, aF1, aFi⟩ := hS
  have hK₀ := E.hK.fix hI
  have hP := E.hP
  have hNF := E.hNF₂
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hW4 : 4 ≤ W := by have := E.hWh; grind [hostWords]
  obtain ⟨⟨hpKn, hpKp, hpK6⟩, hoK, -⟩ := startMathTask P J N₂ hP hNF
  have hoK' : offK P J (pK0 J) 0 = Lst J := by
    have : offK P J (pK0 J) 0 = oW J (((pK0 J : ℕ) : ℝ) + 0) := by
      unfold offK oW; rfl
    rw [this]; unfold pK0; omega
  set i := c.nreg sP with hid
  have nob : ∀ j, j < 10000 → bandOf (sw j) ∉ oracleBands := fun j hj => not_oracle_sw (by omega_nf) (by omega_nf)
  unfold stStep
  refine (IRS.ite (K := 11990) (fun hlt => ?_) (fun hge => ?_)).mono
    (by omega_nf) (fun _ h => h)
  swap
  · refine IRS.skip hI ⟨⟨sN, sP2, sPl, sAt, sLen, sLab, sReg, aF1, aFi⟩,
      fun hi => absurd hi (by omega), fun _ => rfl, fun _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩
  have hi : i < rs.length := by omega
  have hr1 := hSR i hi
  rw [getD_d5 hi] at hr1
  obtain ⟨ra, rb, -, -, -⟩ := hr1
  obtain ⟨hpw, -, -, -⟩ := hw rs[i] (List.getElem_mem hi)
  obtain ⟨-, -, -, hsL⟩ := stop_facts hst hi
  -- 1. load the stop
  have hok1 : okB W c.nmem lsStLoad c.nreg := stLoad_ok _ _ hK₀.2.1 (by omega)
  refine IRS.seq (K₁ := 7) (K₂ := 11008 + 84) (IRS.block lsStLoad hI hok1) ?_ |>.mono
    (by simp) (fun _ h => h)
  rintro c₁ hI₁ hA₁ - hc₁
  obtain ⟨v1E, v1H⟩ := stLoad_val c.nmem c.nreg hK₀.2.1
  
  have k1 : ∀ q, q ≠ zX → q ≠ zE → q ≠ zH → c₁.nreg q = c.nreg q := fun q h1 h2 h3 => by
    rw [hc₁]; exact stLoad_other _ _ h1 h2 h3
  have e1E : c₁.nreg zE = rs[i].1 := by ram_simp
  have e1H : c₁.nreg zH = rs[i].2.1 := by ram_simp
  have e1kE : c₁.nreg kE = pK0 J := by
    rw [k1 _ (by omega_nf) (by omega_nf) (by omega_nf)]; exact hkE
  have e1kH : c₁.nreg kH = 0 := by
    rw [k1 _ (by omega_nf) (by omega_nf) (by omega_nf)]; exact hkH
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC :=
    k1 _ (by omega_nf) (by omega_nf) (by omega_nf)
  have hgw := E.gw' hI₁
  have hC := corr_right0 J hP hNF.1.2.1 hNF.1.1
  -- 2. compare the offsets
  refine IRS.seq (K₁ := 11008) (K₂ := 84) (callOff_irs (dsc := sw 2) (ex := kE) (hx := kH)
    (ey := zE) (hy := zH) (g := cGW) (o := zO) (C := J.whole) hI₁ (E.ctxW' hI₁)
    (by omega_nf) (by omega_nf)
    (by rw [e1kE]; exact hpKn) (by rw [e1E]; exact hpw.1) (by rw [hgw]; exact hC.hg)
    (by rw [e1kE, e1kH]; exact hpKp) (by rw [e1E, e1H]; exact hpw.2.1)
    (by rw [e1kE, e1kH]; exact fun _ => hpK6 rfl) (by rw [e1E, e1H]; exact hpw.2.2)
    (by rw [hA1]; unfold stStepK at hroom; omega)) ?_
  rintro c₂ hI₂ hA₂ - ⟨b2, -, k2, hal2, hm2⟩
  rw [hgw, e1kE, e1kH, e1E, e1H] at b2
  have hb2 : BitIs c₂ zO (Lst J < soff P J rs[i]) := by
    have e : off (chainModel J.whole).W.n (gW J : ℝ) ((chainModel J.whole).key (Qof P) ⟨pK0 J, 0⟩)
        = Lst J := hoK'
    rw [e] at b2
    exact b2
  have k12 : ∀ q, bandOf q ∉ oracleBands → q ≠ zX → q ≠ zE → q ≠ zH → q ≠ zO → q ≠ zO + 1 →
      q ≠ ALLOC → c₂.nreg q = c.nreg q := fun q hq h1 h2 h3 h4 h5 h6 => by
    rw [k2 q hq h4 h5 h6, k1 q h1 h2 h3]
  have k0₂ : c₂.nreg K0 = 0 := (E.hK.fix hI₂).1
  have hm12 : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    ram_simp
  -- the registers of the state, kept so far
  have keepS : ∀ q, (LblR kN kL q ∨ q = aF ∨ q = sP) → c₂.nreg q = c.nreg q := by
    intro q hq
    have hq' : 242400 ≤ q ∧ q ≤ 242484 := by
      unfold LblR at hq
      simp only [kN, kL, aF, sP, sw] at hq
      omega
    refine k12 q (not_oracle_sw (by omega) (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals omega_nf
  have fr12 : ∀ r, bandOf r ∉ oracleBands → ¬ WS r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
    fun r hr hws hra => k12 r hr (fun h => hws (Or.inl h)) (fun h => hws (Or.inr (Or.inl h)))
      (fun h => hws (Or.inr (Or.inr (Or.inl h)))) (fun h => hws (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      (fun h => hws (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hra
  -- 3. the test
  refine IRS.ite (K := 82) (fun h => ?_) (fun h => ?_)
  · -- the stop lies beyond the key
    rw [k0₂] at h
    have hgt : Lst J < soff P J rs[i] := hb2.2.1 (by have := hb2.1; omega)
    exact IRS.skip hI₂ ⟨stI_congr ⟨sN, sP2, sPl, sAt, sLen, sLab, sReg, aF1, aFi⟩ keepS,
      fun hi' he => absurd he (ne_of_gt hgt), fun _ => keepS sP (Or.inr (Or.inr rfl)), fr12,
      by omega, hm12⟩
  · -- the stop lies at the key
    rw [k0₂] at h
    have hat : soff P J rs[i] = Lst J := by
      have : ¬ Lst J < soff P J rs[i] := fun hh => h (by have := hb2.2.2 hh; omega)
      linarith
    have hi1 : i ≤ 1 := by
      by_contra h2
      
      have h0 := sAt 0 (by omega) (by omega)
      have := stops_two hP hNF hst (i := 0) (by omega)
      grind
    have hax := hAR i (by omega)
    rw [getD_d5 (by omega)] at hax
    obtain ⟨xa, xn, xl, xm, -⟩ := hax
    have haux' := haux i hi
    rw [getD_d5 hi, getD_d5 (show i < ax.length by omega)] at haux'
    obtain ⟨ax1, -, axn, axl, axm, -⟩ := haux'
    -- the auxiliary record
    have sP2' : c₂.nreg sP = i := keepS sP (Or.inr (Or.inr rfl))
    have aB2 : c₂.nreg aB = c.nreg aB := k12 _ (nob _ (by norm_num)) (by omega_nf)
      (by omega_nf) (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf)
    have hok3 : okB W c₂.nmem stAux c₂.nreg := stAux_ok _ _ (E.hK.fix hI₂).2.1 (by
      omega)
    refine IRS.seq (K₁ := 11) (K₂ := 70 + 1) (IRS.block stAux hI₂ hok3) ?_ |>.mono
      (by simp) (fun _ h => h)
    rintro c₃ hI₃ - - hc₃
    obtain ⟨v3A, v3N, v3L, v3M⟩ := stAux_val c₂.nmem c₂.nreg (E.hK.fix hI₂).2.1
    have mm : ∀ k, k < 5 → c₂.nmem (c.nreg aB + 5 * i + k) = c.nmem (c.nreg aB + 5 * i + k) :=
      fun k hk => hm12 _ (by omega)
    
    have e3A : c₃.nreg zA = (ax[i]'(by omega)).1 := by
      rw [hc₃]; show regB _ _ _ _ = _; rw [v3A, aB2, sP2', ← xa]
      simpa using mm 0 (by norm_num)
    have e3N : c₃.nreg zN = (ax[i]'(by omega)).2.1 := by
      rw [hc₃]; show regB _ _ _ _ = _; rw [v3N, aB2, sP2', ← xn]; exact mm 1 (by norm_num)
    have e3L : c₃.nreg zL = (ax[i]'(by omega)).2.2.1 := by
      rw [hc₃]; show regB _ _ _ _ = _; rw [v3L, aB2, sP2', ← xl]; exact mm 2 (by norm_num)
    have e3M : c₃.nreg zM = (ax[i]'(by omega)).2.2.2.1 := by
      rw [hc₃]; show regB _ _ _ _ = _; rw [v3M, aB2, sP2', ← xm]; exact mm 3 (by norm_num)
    have k3 : ∀ q, q ≠ zX → q ≠ zA → q ≠ zN → q ≠ zL → q ≠ zM → c₃.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 h4 h5 => by rw [hc₃]; exact stAux_other _ _ h1 h2 h3 h4 h5
    have keep3 : ∀ q, (LblR kN kL q ∨ q = aF ∨ q = sP) → c₃.nreg q = c₂.nreg q := by
      intro q hq
      have hq' : 242400 ≤ q ∧ q ≤ 242484 := by
        unfold LblR at hq
        simp only [kN, kL, aF, sP, sw] at hq
        omega
      refine k3 q ?_ ?_ ?_ ?_ ?_ <;>
        omega_nf
    have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC :=
      k3 _ (by omega_nf) (by omega_nf) (by omega_nf)
        (by omega_nf) (by omega_nf)
    -- the labels
    have n3 : c₃.nreg kN ≤ 4 := by
      rw [keep3 kN (Or.inl (Or.inl rfl)), keepS kN (Or.inl (Or.inl rfl))]; exact sN
    refine IRS.seq (K₁ := 70) (K₂ := 1) (stLabs_irs hI₃ E.hK n3 (by omega) hW4) ?_
    rintro c₄ hI₄ hA₄ - ⟨n4, l4, a4, f4, m4⟩
    -- advance the pointer
    have sP4 : c₄.nreg sP = i := by
      rw [f4 _ (by omega_nf) (by omega_nf), keep3 sP (Or.inr (Or.inr rfl)),
        sP2']
    have k1₄ := (E.hK.fix hI₄).2.1
    refine (IRS.instr1 (i := .addN sP sP K1) hI₄ ⟨iscr_sw (by omega_nf) (by omega_nf),
      by omega⟩).mono le_rfl ?_
    rintro c₅ hc₅
    have f5 : ∀ q, q ≠ sP → c₅.nreg q = c₄.nreg q := fun q hq => by
      rw [hc₅]; simp [regI, upd_other _ _ _ hq]
    have v5 : c₅.nreg sP = i + 1 := by rw [hc₅]; simp [regI, sP4, k1₄]
    
    -- the label list
    have hlab3 : lblOf c₃ kN kL = lblOf c kN kL := by
      rw [lblOf_congrK (fun q hq => keep3 q (Or.inl hq)), lblOf_congrK (fun q hq => keepS q (Or.inl hq))]
    have hlab5 : lblOf c₅ kN kL = lblOf c₄ kN kL :=
      lblOf_congrK (fun q hq => f5 q (by unfold LblR at hq; simp only [kN, kL, sP, sw] at hq ⊢; omega))
    rw [hlab3] at l4
    have e3A' : c₃.nreg zA = 1 ↔ (ax[i]'(by omega)).1 = 1 := by rw [e3A]
    have hlen2 : (lblOf c kN kL).length ≤ 2 := by omega
    have aF3 : c₃.nreg aF = c.nreg aF := by
      rw [keep3 aF (Or.inr (Or.inl rfl)), keepS aF (Or.inr (Or.inl rfl))]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => by rw [v5], fun hn => absurd hat (hn hi),
      fun r hr hws hra => ?_, ?_, fun a ha => ?_⟩
    · rw [f5 _ (by omega_nf)]; exact n4
    · omega
    · omega
    · intro j hj hj'
      rw [v5] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h' | rfl
      · exact sAt j hj h'
      · exact hat
    · rw [hlab5, l4, v5]
      split_ifs
      · have := labAdd_len (lblOf c kN kL) (c₃.nreg zN) (c₃.nreg zL) (c₃.nreg zM); omega
      · omega
    · intro j hj v hv
      rw [hlab5, l4]
      rw [v5] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
      · have := sLab j h' v hv
        split_ifs
        · exact labAdd_old this
        · exact this
      · rw [getD_d5' (show i < ax.length by omega)] at hv
        unfold axLabs at hv
        by_cases ha : (ax[i]'(by omega)).1 = 1
        · rw [ite_eq_left ha] at hv
          rw [ite_eq_left (e3A'.2 ha), e3N, e3L, e3M]
          refine labAdd_new hlen2 ?_
          simp only [List.mem_append] at hv
          rcases hv with hv | hv
          · split_ifs at hv with hh
            · exact Or.inl ⟨hh, by simpa using hv⟩
            · simp at hv
          · split_ifs at hv with hh
            · exact Or.inr ⟨hh, by simpa using hv⟩
            · simp at hv
        · rw [ite_eq_right ha] at hv; simp at hv
    · intro v hv
      rw [hlab5, l4] at hv
      split_ifs at hv with ha
      · rcases labAdd_mem hv with hv | ⟨h0, rfl⟩ | ⟨h1, rfl⟩
        · exact sReg v hv
        · omega
        omega
      · exact sReg v hv
    · rw [f5 _ (by omega_nf), a4]
      split_ifs
      all_goals omega
    · rw [f5 _ (by omega_nf), a4, v5]
      by_cases ha : c₃.nreg zA = 1
      · rw [ite_eq_left ha]
        refine ⟨fun _ => ⟨i, by omega, ?_⟩, fun _ => rfl⟩
        rw [getD_d5' (show i < ax.length by omega)]; omega
      · rw [ite_eq_right ha, aF3, aFi]
        constructor
        · rintro ⟨j, hj, hjx⟩; exact ⟨j, by omega, hjx⟩
        · rintro ⟨j, hj, hjx⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
          · exact ⟨j, h', hjx⟩
          · rw [getD_d5' (show i < ax.length by omega)] at hjx
            omega
    · -- the frame
      ram_grind
    · have := f5 ALLOC (by omega_nf)
      omega
    · ram_simp

end

end SweepEv

end Chazelle.Core
