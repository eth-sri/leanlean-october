module

public import Chazelle.Core.SweepIoS0CandInitProg

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (straight-line pieces)

`hdrA_irs`, `midS_irs`, `hdr_irs`, `stLd_irs`, `slotSt_irs`, `tbLd_irs`, `cls_irs`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The head block.** -/
theorem hdrA_irs (hI : IInv W c₀ c) (hK : Consts c) (hd : c.nreg (sw 21) + 5 ≤ W)
    (hroom : c.nreg ALLOC + 6 * c.nreg (sw 301) ≤ W) :
    IRS P W c₀ (block hdrA) c 18 (fun c' =>
      c'.nreg ipB = c.nreg ALLOC ∧ c'.nreg pT = c.nreg ALLOC + 6 * c.nreg (sw 301) ∧
      c'.nreg ipX = 0 ∧ c'.nreg ipJ = 0 ∧ c'.nreg ipKc = c.nmem (c.nreg (sw 4)) ∧
      c'.nreg ipM5 = c.nreg (sw 34) - 2 ∧
      c'.nreg ipTm = c.nmem (c.nreg (sw 21) + 2) ∧ c'.nreg ipTt = c.nmem (c.nreg (sw 21) + 3) ∧
      c'.nreg ipTb = c.nmem (c.nreg (sw 21) + 4) ∧
      (∀ r, (r < sw 2482 ∨ (sw 2482 < r ∧ r < sw 4100) ∨ sw 4129 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  obtain ⟨-, -, -, k4, -, k2, k3⟩ := hK
  simp only [K2, K3, K4, sw, ALLOC, Nat.reduceAdd] at k2 k3 k4 hd hroom
  have hfr : ∀ r, (r < sw 2482 ∨ (sw 2482 < r ∧ r < sw 4100) ∨ sw 4129 < r) →
      regB c.nmem hdrA c.nreg r = c.nreg r := by
    intro r hr
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [hdrA, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold ipB pT ipX ipJ ipKc ipM5 ipTa ipTm ipTt ipTb sw ALLOC at *
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
  refine (IRS.block hdrA hI ?_).mono (by simp [hdrA]) ?_
  · simp [hdrA, okB, okI, regI, upd, ipB, pT, ipX, ipJ, ipKc, ipM5, ipTa, ipTm, ipTt, ipTb, K2,
      K3, K4, sw, ALLOC, IScr, k2, k3, k4]
    omega
  · rintro c' rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (simp [hdrA, regB, regI, upd, ipB, pT, ipX, ipJ, ipKc, ipM5, ipTa, ipTm, ipTt,
      ipTb, K2, K3, K4, sw, ALLOC, k2, k3, k4]; try omega)

/-! ## `midT` -/

theorem midF_irs (hI : IInv W c₀ c) {m T : ℕ} (hm : c.nreg ipTm = m) (hT : c.nreg ipTt = T)
    (h2 : T + T ≤ W) :
    IRS P W c₀ ipMidF c 3 (fun c' => c'.nreg ipTM = (if T < m then 2 * T else 0) ∧
      (∀ r, r ≠ ipTM → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold ipMidF
  by_cases h : T < m
  · refine (IRS.ifT (by rwa [hm, hT]) (IRS.instr1 (i := .addN ipTM ipTt ipTt) hI
      ⟨iscr_sw (by unfold ipTM sw; omega) (by unfold ipTM sw; omega), by rwa [hT]⟩)).mono
      (by norm_num) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · simp only [regI, upd_same, hT, ite_eq_left h]; ring
    · simp only [regI]; exact upd_other _ _ _ hr
  · refine (IRS.ifF (by rwa [hm, hT]) (IRS.instr1 (i := .constN ipTM 0) hI
      ⟨iscr_sw (by unfold ipTM sw; omega) (by unfold ipTM sw; omega), Nat.zero_le _⟩)).mono
      (by norm_num) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · simp only [regI, upd_same, ite_eq_right h]
    · simp only [regI]; exact upd_other _ _ _ hr

set_option maxHeartbeats 1000000 in
theorem midS_irs (hI : IInv W c₀ c) (hK : Consts c) {m T b : ℕ} (hm : c.nreg ipTm = m)
    (hT : c.nreg ipTt = T) (hb : c.nreg ipTb = b) (hTm : T ≤ m) (h2m : 2 * m ≤ W) :
    IRS P W c₀ ipMidS c 8 (fun c' =>
      c'.nreg ipTM = (if b = 1 then 2 * m - 2 * T else if T < m then 2 * T else 0) ∧
      (∀ r, r ≠ ipTM → r ≠ ipT2 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have k1 : c.nreg K1 = 1 := hK.2.1
  unfold ipMidS
  have hF : b ≠ 1 → IRS P W c₀ ipMidF c 4 (fun c' =>
      c'.nreg ipTM = (if b = 1 then 2 * m - 2 * T else if T < m then 2 * T else 0) ∧
      (∀ r, r ≠ ipTM → r ≠ ipT2 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := fun hb1 =>
    (midF_irs hI hm hT (by omega)).mono (by norm_num) (fun c' ⟨h1, h2, h3⟩ =>
      ⟨by rw [h1, ite_eq_right hb1], fun r hr _ => h2 r hr, h3⟩)
  by_cases h0 : b < 1
  · exact (IRS.ifT (K := 4) (by rwa [hb, k1]) (hF (by omega))).mono (by norm_num)
      (fun _ h => h)
  · refine (IRS.ifF (K := 6) (by rwa [hb, k1]) ?_).mono le_rfl (fun _ h => h)
    by_cases h1 : 1 < b
    · exact IRS.ifT (K := 4) (by rwa [hb, k1]) (hF (by omega))
    · have hb1 : b = 1 := by omega
      refine (IRS.ifF (K := 4) (by rwa [hb, k1]) ((IRS.block ipMidB hI ?_).mono
        (K' := 4) (by simp [ipMidB]) (fun _ h => h))).mono le_rfl ?_
      · simp [ipMidB, okB, okI, ipT2, ipTM, ipTm, ipTt, sw, IScr]
        simp only [ipTm, sw, Nat.reduceAdd] at hm
        rw [hm]; omega
      · rintro c' rfl
        refine ⟨?_, fun r h1 h2 => ?_, rfl⟩
        · simp only [ipTm, ipTt, sw, Nat.reduceAdd] at hm hT
          simp [ipMidB, regB, regI, upd, ipT2, ipTM, ipTm, ipTt, sw, hm, hT, hb1]
          omega
        · simp only [ipMidB, regB, regI]
          rw [upd_other _ _ _ h1, upd_other _ _ _ h1, upd_other _ _ _ h2]

/-! ## Reading a stop record -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLd_irs (hI : IInv W c₀ c) (hK : Consts c) {AS x : ℕ} (hAS : c.nreg (sw 200) = AS)
    (hx : c.nreg ipX = x) (hW : AS + 5 * x + 4 ≤ W) :
    IRS P W c₀ (block stLd) c 14 (fun c' =>
      c'.nreg lsxE = c.nmem (AS + 5 * x) ∧ c'.nreg lsxH = c.nmem (AS + 5 * x + 1) ∧
      c'.nreg ipK = c.nmem (AS + 5 * x + 2) ∧ c'.nreg ipKk = c.nmem (AS + 5 * x + 3) ∧
      c'.nreg ipS = 1 - c.nmem (AS + 5 * x + 4) ∧
      (∀ r, r ≠ lsxE → r ≠ lsxH → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb → r ≠ ipS →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have k1 : c.nreg K1 = 1 := hK.2.1
  simp only [K1, ipX, sw, Nat.reduceAdd] at k1 hx hAS
  have hfr : ∀ r, r ≠ lsxE → r ≠ lsxH → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb → r ≠ ipS →
      regB c.nmem stLd c.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [stLd, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold lsxE lsxH ipA ipK ipKk ipBb ipS sw at *
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp only [dstI] <;> omega
  refine (IRS.block stLd hI ?_).mono (by simp [stLd]) ?_
  · simp [stLd, okB, okI, regI, upd, lsxE, lsxH, ipA, ipK, ipKk, ipBb, ipS, ipX, K1, sw, IScr,
      k1, hx, hAS]
    omega
  · rintro c' rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (simp [stLd, regB, regI, upd, lsxE, lsxH, ipA, ipK, ipKk, ipBb, ipS, ipX, K1, sw,
      k1, hx, hAS]; first | (congr 1; omega) | (congr 2; omega))

/-! ## Writing a slot -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem slotAd_irs (hI : IInv W c₀ c) {B t s : ℕ} (hB : c.nreg ipB = B) (ht : c.nreg lsI = t)
    (hs : c.nreg ipS = s) (hW : B + 6 * t + 3 * s ≤ W) :
    IRS P W c₀ (block slotAd) c 7 (fun c' => c'.nreg ipT = slotA B t s ∧
      (∀ r, r ≠ ipT → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  simp only [ipB, lsI, ipS, sw, Nat.reduceAdd] at hB ht hs
  refine (IRS.block slotAd hI ?_).mono (by simp [slotAd]) ?_
  · simp [slotAd, okB, okI, regI, upd, ipT, lsI, ipB, ipS, sw, IScr, hB, ht, hs]
    omega
  · rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · simp [slotAd, regB, regI, upd, ipT, lsI, ipB, ipS, sw, hB, ht, hs, slotA]
      omega
    · refine regB_other _ _ _ (fun i hi => ?_)
      simp only [slotAd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
        exact Ne.symm hr

/-- **Writing a slot.** -/
theorem slotSt_irs (hI : IInv W c₀ c) (hK : Consts c) {B t s : ℕ} (hB : c.nreg ipB = B)
    (ht : c.nreg lsI = t) (hs : c.nreg ipS = s) (hB0 : c₀.nreg ALLOC ≤ B)
    (hW : B + 6 * t + 3 * s + 2 ≤ W) :
    IRS P W c₀ slotSt c 12 (fun c' =>
      c'.nmem = slotW c.nmem B t s (c.nreg ipE) (c.nreg ipH) ∧
      (∀ r, r ≠ ipT → c'.nreg r = c.nreg r)) := by
  have k1 : c.nreg K1 = 1 := hK.2.1
  have nT1 : K1 ≠ ipT := by unfold K1 ipT sw; omega
  have nTE : ipE ≠ ipT := by unfold ipE ipT sw; omega
  have nTH : ipH ≠ ipT := by unfold ipH ipT sw; omega
  have iT : IScr ipT := iscr_sw (by unfold ipT sw; omega) (by unfold ipT sw; omega)
  unfold slotSt
  refine IRS.seq (K₁ := 7) (K₂ := 5) (slotAd_irs hI hB ht hs (by omega)) ?_ |>.mono le_rfl
    (fun _ h => h)
  rintro c₁ hI₁ - - ⟨a1, a2, a3⟩
  have e1 : c₁.nreg K1 = 1 := (a2 K1 nT1).trans k1
  refine IRS.seq (K₁ := 1) (K₂ := 4) (IRS.store hI₁ (by rw [a1]; unfold slotA; omega)) ?_
  rintro c₂ hI₂ - - rfl
  refine IRS.seq (K₁ := 1) (K₂ := 3) (IRS.instr1 hI₂ (i := .addN ipT ipT K1)
    ⟨iT, by simp only; rw [a1, e1]; unfold slotA; omega⟩) ?_
  rintro c₃ hI₃ - - rfl
  refine IRS.seq (K₁ := 1) (K₂ := 2) (IRS.store hI₃ (by
    simp only [regI, upd_same]; rw [a1]; unfold slotA; omega)) ?_
  rintro c₄ hI₄ - - rfl
  refine IRS.seq (K₁ := 1) (K₂ := 1) (IRS.instr1 hI₄ (i := .addN ipT ipT K1)
    ⟨iT, by simp only [regI, upd_same]; rw [upd_other _ _ _ nT1, a1, e1]
            unfold slotA; omega⟩) ?_
  rintro c₅ hI₅ - - rfl
  refine (IRS.store hI₅ (by
    simp only [regI, upd_same]; rw [upd_other _ _ _ nT1, a1]
    unfold slotA; omega)).mono le_rfl ?_
  rintro c' rfl
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [regI, upd_same, upd_other _ _ _ nT1,
      upd_other _ _ _ nTE, upd_other _ _ _ nTH]
    rw [a1, e1, a2 _ nTE, a2 _ nTH, a3]
    rfl
  · simp only [regI]
    rw [upd_other _ _ _ hr, upd_other _ _ _ hr, a2 r hr]

/-! ## The head -/

set_option maxHeartbeats 2000000 in
/-- **The head.** -/
theorem hdr_irs (hI : IInv W c₀ c) (hK : Consts c) (hd : c.nreg (sw 21) + 5 ≤ W)
    (hroom : c.nreg ALLOC + 6 * c.nreg (sw 301) ≤ W)
    (hTm : c.nmem (c.nreg (sw 21) + 3) ≤ c.nmem (c.nreg (sw 21) + 2))
    (h2m : 2 * c.nmem (c.nreg (sw 21) + 2) + 6 ≤ W) :
    IRS P W c₀ hdr c 27 (fun c' =>
      c'.nreg ipB = c.nreg ALLOC ∧ c'.nreg pT = c.nreg ALLOC + 6 * c.nreg (sw 301) ∧
      c'.nreg ipX = 0 ∧ c'.nreg ipJ = 0 ∧ c'.nreg ipKc = c.nmem (c.nreg (sw 4)) ∧
      c'.nreg ipM5 = c.nreg (sw 34) - 2 ∧
      c'.nreg ipM6 = (if c.nmem (c.nreg (sw 21) + 4) = 1 then
          2 * c.nmem (c.nreg (sw 21) + 2) - 2 * c.nmem (c.nreg (sw 21) + 3)
        else if c.nmem (c.nreg (sw 21) + 3) < c.nmem (c.nreg (sw 21) + 2) then
          2 * c.nmem (c.nreg (sw 21) + 3) else 0) + 6 ∧
      (∀ r, (r < sw 2482 ∨ (sw 2482 < r ∧ r < sw 4100) ∨ sw 4129 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  unfold hdr
  refine IRS.seq (K₁ := 18) (K₂ := 9) (hdrA_irs hI hK hd hroom) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  have hK₁ : Consts c₁ := by
    obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
    have f : ∀ q, 610 ≤ q → q ≤ 616 → c₁.nreg (sw q) = c.nreg (sw q) := fun q h1 h2 =>
      a10 _ (Or.inl (by unfold sw; omega))
    exact ⟨(f 610 le_rfl (by norm_num)).trans k0, (f 611 (by norm_num) (by norm_num)).trans k1,
      (f 612 (by norm_num) (by norm_num)).trans k6, (f 613 (by norm_num) (by norm_num)).trans k4,
      (f 614 (by norm_num) (by norm_num)).trans k5, (f 615 (by norm_num) (by norm_num)).trans k2,
      (f 616 (by norm_num) le_rfl).trans k3⟩
  refine IRS.seq (K₁ := 8) (K₂ := 1) (midS_irs hI₁ hK₁ a7 a8 a9 hTm (by omega)) ?_
  rintro c₂ hI₂ - - ⟨b1, b2, b3⟩
  have k6 : c₂.nreg K6 = 6 := by
    rw [b2 K6 (by unfold K6 ipTM sw; omega) (by unfold K6 ipT2 sw; omega),
      a10 K6 (Or.inl (by unfold K6 sw; omega))]
    exact hK.2.2.1
  have hv : c₂.nreg ipTM ≤ 2 * c.nmem (c.nreg (sw 21) + 2) := by
    rw [b1]; split_ifs <;> omega
  refine (IRS.instr1 (i := .addN ipM6 ipTM K6) hI₂ ⟨iscr_sw (by unfold ipM6 sw; omega)
    (by unfold ipM6 sw; omega), by rw [k6]; omega⟩).mono le_rfl ?_
  rintro c' rfl
  have o : ∀ r, r ≠ ipM6 → r ≠ ipTM → r ≠ ipT2 → (regI c₂.nmem (.addN ipM6 ipTM K6) c₂.nreg) r =
      c₁.nreg r := fun r h1 h2 h3 => by
    simp only [regI]; rw [upd_other _ _ _ h1, b2 r h2 h3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by simp only; rw [b3, a11]⟩
  · exact (o _ (by unfold ipB ipM6 sw; omega) (by unfold ipB ipTM sw; omega)
      (by unfold ipB ipT2 sw; omega)).trans a1
  · exact (o _ (by unfold pT ipM6 sw; omega) (by unfold pT ipTM sw; omega)
      (by unfold pT ipT2 sw; omega)).trans a2
  · exact (o _ (by unfold ipX ipM6 sw; omega) (by unfold ipX ipTM sw; omega)
      (by unfold ipX ipT2 sw; omega)).trans a3
  · exact (o _ (by unfold ipJ ipM6 sw; omega) (by unfold ipJ ipTM sw; omega)
      (by unfold ipJ ipT2 sw; omega)).trans a4
  · exact (o _ (by unfold ipKc ipM6 sw; omega) (by unfold ipKc ipTM sw; omega)
      (by unfold ipKc ipT2 sw; omega)).trans a5
  · exact (o _ (by unfold ipM5 ipM6 sw; omega) (by unfold ipM5 ipTM sw; omega)
      (by unfold ipM5 ipT2 sw; omega)).trans a6
  · simp only [regI, upd_same]
    rw [b1, k6]
  · exact (o r (by unfold ipM6 sw at *; omega) (by unfold ipTM sw at *; omega)
      (by unfold ipT2 sw at *; omega)).trans (a10 r hr)


/-! ## Reading a table entry -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem tbLd_irs (hI : IInv W c₀ c) {sr AT k s : ℕ} (hsr : sr < sw 4100 ∨ sw 4129 < sr)
    (hAT : c.nreg (sw 302) = AT) (hk : c.nreg ipJ = k) (hs : c.nreg sr = s)
    (hW : AT + 3 * (2 * k + s) ≤ W) :
    IRS P W c₀ (block (tbLd sr)) c 7 (fun c' =>
      c'.nreg ipS = s ∧ c'.nreg ipA = AT + 3 * (2 * k + s) ∧
      c'.nreg ipF = c.nmem (AT + 3 * (2 * k + s)) ∧
      (∀ r, r ≠ ipS → r ≠ ipA → r ≠ ipT → r ≠ ipF → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  simp only [ipJ, sw, Nat.reduceAdd] at hAT hk
  have hfr : ∀ r, r ≠ ipS → r ≠ ipA → r ≠ ipT → r ≠ ipF →
      regB c.nmem (tbLd sr) c.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [tbLd, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4
  refine (IRS.block (tbLd sr) hI ?_).mono (by simp [tbLd]) ?_
  · simp [tbLd, okB, okI, regI, upd, ipS, ipA, ipT, ipF, ipJ, sw, IScr, hAT, hk, hs]
    omega
  · rintro c' rfl
    refine ⟨?_, ?_, ?_, hfr, rfl⟩
    all_goals (try simp [tbLd, regB, regI, upd, ipS, ipA, ipT, ipF, ipJ, sw, hAT, hk, hs])
    all_goals first | omega | (congr 1; omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem tbTg_irs (hI : IInv W c₀ c) (hK : Consts c) {a : ℕ} (ha : c.nreg ipA = a)
    (hW : a + 2 ≤ W) :
    IRS P W c₀ (block tbTg) c 6 (fun c' =>
      c'.nreg ipE = c.nreg oE ∧ c'.nreg ipH = c.nreg oC ∧ c'.nreg lsxE = c.nmem (a + 1) ∧
      c'.nreg lsxH = c.nmem (a + 2) ∧
      (∀ r, r ≠ ipE → r ≠ ipH → r ≠ ipA → r ≠ lsxE → r ≠ lsxH → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have k1 : c.nreg K1 = 1 := hK.2.1
  simp only [K1, ipA, sw, Nat.reduceAdd] at k1 ha
  have hfr : ∀ r, r ≠ ipE → r ≠ ipH → r ≠ ipA → r ≠ lsxE → r ≠ lsxH →
      regB c.nmem tbTg c.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4 h5
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [tbTg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 |
        exact Ne.symm h5
  refine (IRS.block tbTg hI ?_).mono (by simp [tbTg]) ?_
  · simp [tbTg, okB, okI, regI, upd, ipE, ipH, ipA, lsxE, lsxH, oE, oC, K1, sw, IScr, k1, ha]
    omega
  · rintro c' rfl
    refine ⟨?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (try simp [tbTg, regB, regI, upd, ipE, ipH, ipA, lsxE, lsxH, oE, oC, K1, sw, k1, ha])

/-! ## The class test -/

theorem setV_irs (hI : IInv W c₀ c) (hK : Consts c) {v : ℕ} (hv : v ≤ 1) :
    IRS P W c₀ (setV v) c 1 (fun c' => c'.nreg ipV = v ∧ (∀ r, r ≠ ipV → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN ipV v) hI ⟨iscr_sw (by unfold ipV sw; omega)
    (by unfold ipV sw; omega), by have := hI.hw.1 K1; rw [hK.2.1] at this; omega⟩).mono le_rfl ?_
  · rintro c' rfl
    exact ⟨by simp [regI], fun r hr => by simp only [regI]; exact upd_other _ _ _ hr, rfl⟩

theorem eqT_irs {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (ipEqT a b t e) c (K + 4) Q := by
  unfold ipEqT
  by_cases h1 : c.nreg a < c.nreg b
  · exact (IRS.ifT (K := K) h1 (he (by omega))).mono (by omega) (fun _ h => h)
  · refine (IRS.ifF (K := K + 2) h1 ?_).mono (by omega) (fun _ h => h)
    by_cases h2 : c.nreg b < c.nreg a
    · exact IRS.ifT h2 (he (by omega))
    · exact IRS.ifF h2 (ht (by omega))

set_option maxHeartbeats 2000000 in
/-- **The class test.** -/
theorem cls_irs (hI : IInv W c₀ c) (hK : Consts c) :
    IRS P W c₀ cls c 19 (fun c' =>
      (c'.nreg ipV = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg (sw 41) ∧
          c.nreg oE ≠ c.nreg ipM6)))) ∧ c'.nreg ipV ≤ 1 ∧
      (∀ r, r ≠ ipV → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hK' := hK
  obtain ⟨k0, -, k6, -⟩ := hK
  have sv : ∀ v, v ≤ 1 → (v = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg (sw 41) ∧
          c.nreg oE ≠ c.nreg ipM6)))) → ∀ K, 1 ≤ K → IRS P W c₀ (setV v) c K (fun c' =>
      (c'.nreg ipV = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg (sw 41) ∧
          c.nreg oE ≠ c.nreg ipM6)))) ∧ c'.nreg ipV ≤ 1 ∧
      (∀ r, r ≠ ipV → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) :=
    fun v hv hiff K hK => (setV_irs hI hK' hv).mono hK (fun c' ⟨h1, h2, h3⟩ =>
      ⟨by rwa [h1], by rwa [h1], h2, h3⟩)
  unfold cls
  by_cases a1 : c.nreg oE < c.nreg K6
  · exact (IRS.ifT a1 (sv 0 (by norm_num) (by rw [k6] at a1; omega) 1 le_rfl)).mono (by norm_num)
      (fun _ h => h)
  refine (IRS.ifF (K := 17) a1 ?_).mono (by norm_num) (fun _ h => h)
  rw [k6] at a1
  by_cases a2 : c.nreg ipM5 < c.nreg oE
  · exact (IRS.ifT a2 (sv 0 (by norm_num) (by omega) 1 le_rfl)).mono (by norm_num) (fun _ h => h)
  refine IRS.ifF (K := 15) a2 ?_
  by_cases a3 : c.nreg K0 < c.nreg oC
  · exact (IRS.ifT a3 (sv 1 le_rfl (by rw [k0] at a3; omega) 1 le_rfl)).mono (by norm_num)
      (fun _ h => h)
  refine IRS.ifF (K := 13) a3 ?_
  rw [k0] at a3
  refine eqT_irs (K := 9) (fun h => ?_) (fun h => ?_)
  · exact sv 0 (by norm_num) (by rw [k6] at h; omega) 9 (by norm_num)
  rw [k6] at h
  refine eqT_irs (K := 5) (fun h' => ?_) (fun h' => ?_)
  · exact sv 0 (by norm_num) (by omega) 5 (by norm_num)
  refine eqT_irs (K := 1) (fun h'' => ?_) (fun h'' => ?_)
  · exact (sv 0 (by norm_num) (by omega) 1 le_rfl).mono (by norm_num) (fun _ h => h)
  · exact (sv 1 le_rfl (by omega) 1 le_rfl).mono (by norm_num) (fun _ h => h)

end

end S0C

end SweepIo

end Chazelle.Core
