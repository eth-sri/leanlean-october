module

public import Chazelle.Core.SweepEvTasks3

/-!
# The sweep (WP-D), stage 3: the next key (task K), registers and building blocks

Scratch registers `sw 2480 … 2496` (in `KR`) of the next-key step, and its building blocks:

* `kqIsOne r s`: run `s` iff the register `r` holds `1`;
* `offerQ`: offer the position `(kqSE, kqSH)` to the running minimum `(kqF; kqE, kqH)` (offsets
  compared by `callOff`);
* `storeL x vs`: store the registers `vs` at `x, x + 1, …`;
* `ldStopL`, `ldAuxL`: the loads of a stop record and of the flag of an auxiliary record.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## Scratch registers -/

/-- The running minimum: flag, position. -/
def kqF : ℕ := sw 2480
def kqE : ℕ := sw 2481
def kqH : ℕ := sw 2482
/-- The position offered (a stop or the window end). -/
def kqSE : ℕ := sw 2483
def kqSH : ℕ := sw 2484
/-- The comparison bits (`kqO`, `kqO + 1`). -/
def kqO : ℕ := sw 2485
/-- The flags "the best candidate is at the key" and "an anchored stop was skipped". -/
def kqB : ℕ := sw 2487
def kqA : ℕ := sw 2488
/-- The label list under construction: count `kqN`, labels `kqL … kqL + 3`. -/
def kqN : ℕ := sw 2489
def kqL : ℕ := sw 2490
/-- An address and two values. -/
def kqX : ℕ := sw 2494
def kqV : ℕ := sw 2495
def kqY : ℕ := sw 2496

/-! ## `kqIsOne` -/

/-- Run `s` iff the register `r` holds `1`. -/
def kqIsOne (r : ℕ) (s : Stmt) : Stmt := .ifLtN K0 r (.ifLtN r K2 s .skip) .skip

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem kqIsOne_irs {r : ℕ} {s : Stmt} {K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (hK : Consts c) (hs : c.nreg r = 1 → IRS P W c₀ s c K Q) (hq : c.nreg r ≠ 1 → Q c) :
    IRS P W c₀ (kqIsOne r s) c (K + 4) Q := by
  obtain ⟨k0, -, -, -, -, k2, -⟩ := hK
  unfold kqIsOne
  by_cases h1 : c.nreg K0 < c.nreg r
  · by_cases h2 : c.nreg r < c.nreg K2
    · exact (IRS.ifT h1 (IRS.ifT h2 (hs (by omega)))).mono (by omega) (fun _ h => h)
    · exact (IRS.ifT h1 (IRS.ifF h2 (IRS.skip (K := 0) hI (hq (by omega))))).mono (by omega)
        (fun _ h => h)
  · exact (IRS.ifF h1 (IRS.skip (K := 0) hI (hq (by omega)))).mono (by omega) (fun _ h => h)

/-! ## Offer to the running minimum -/

/-- Take the offered position. -/
def kqTake : List Instr := [.constN kqF 1, .copyN kqE kqSE, .copyN kqH kqSH]

/-- **Offer `(kqSE, kqSH)` to the running minimum** (taken if there is none, or if its offset is
smaller). -/
def offerQ : Stmt :=
  .ifLtN K0 kqF
    (.seq (callOff (sw 2) kqSE kqSH kqE kqH cGW kqO) (.ifLtN K0 kqO (block kqTake) .skip))
    (block kqTake)

/-- The registers the offer writes. -/
def OffR (r : ℕ) : Prop := r = kqF ∨ r = kqE ∨ r = kqH ∨ r = kqO ∨ r = kqO + 1

/-- The outputs of the offer. -/
def OfferQOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  c'.nreg kqF = 1 ∧
  ((c.nreg kqF = 1 ∧ c'.nreg kqE = c.nreg kqE ∧ c'.nreg kqH = c.nreg kqH) ∨
    (c'.nreg kqE = c.nreg kqSE ∧ c'.nreg kqH = c.nreg kqSH)) ∧
  offK P J (c'.nreg kqE) (c'.nreg kqH) ≤ offK P J (c.nreg kqSE) (c.nreg kqSH) ∧
  (c.nreg kqF = 1 →
    offK P J (c'.nreg kqE) (c'.nreg kqH) ≤ offK P J (c.nreg kqE) (c.nreg kqH)) ∧
  EFr OffR c c'

theorem kqTake_irs (hI : IInv W c₀ c) (hW : 1 ≤ W) :
    IRS P W c₀ (block kqTake) c 3 (fun c' => c'.nreg kqF = 1 ∧ c'.nreg kqE = c.nreg kqSE ∧
      c'.nreg kqH = c.nreg kqSH ∧ EFr OffR c c') := by
  refine (IRS.block kqTake hI ?_).mono le_rfl ?_
  · simp only [kqTake, okB, okI]
    exact ⟨⟨iscr_sw' (by norm_num) (by norm_num), hW⟩, iscr_sw' (by norm_num) (by norm_num),
      iscr_sw' (by norm_num) (by norm_num), trivial⟩
  · rintro c' rfl
    refine ⟨?_, ?_, ?_, ⟨fun r _ hr hra => ?_, ?_, fun a _ => rfl⟩⟩
    · simp [kqTake, regB, regI, upd, kqF, kqE, kqH, kqSE, kqSH, sw]
    · simp [kqTake, regB, regI, upd, kqF, kqE, kqH, kqSE, kqSH, sw]
    · simp [kqTake, regB, regI, upd, kqF, kqE, kqH, kqSE, kqSH, sw]
    · unfold OffR at hr
      simp only [kqTake, regB, regI]
      rw [upd_other _ _ _ (by tauto), upd_other _ _ _ (by tauto), upd_other _ _ _ (by tauto)]
    · simp only [kqTake, regB, regI]
      rw [upd_other _ _ _ (by unfold ALLOC kqH sw; omega),
        upd_other _ _ _ (by unfold ALLOC kqE sw; omega),
        upd_other _ _ _ (by unfold ALLOC kqF sw; omega)]

set_option maxHeartbeats 4000000 in
/-- **The offer.** -/
theorem offerQ_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c)
    (hctx : ChainCtx P W c (sw 2) J.whole) (hgw : c.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hF : c.nreg kqF ≤ 1)
    (ht : c.nreg kqF = 1 → PosW P J (c.nreg kqE) (c.nreg kqH))
    (hq : PosW P J (c.nreg kqSE) (c.nreg kqSH)) (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ offerQ c 11020 (OfferQOut P J c) := by
  obtain ⟨k0, -, -, -, -, -, -⟩ := hK
  have hW1 : 1 ≤ W := by omega
  have hgw' : ((c.nreg cGW : ℕ) : ℝ) = (gW J : ℝ) := by rw [hgw]
  unfold offerQ
  by_cases h1 : c.nreg K0 < c.nreg kqF
  · have hF1 : c.nreg kqF = 1 := by omega
    have htP := ht hF1
    refine IRS.mono (K := 11015 + 2) (IRS.ifT h1 ?_) (by norm_num) (fun _ h => h)
    refine IRS.seq (K₁ := 11008) (K₂ := 7) (callOff_irs (dsc := sw 2) (ex := kqSE) (hx := kqSH)
      (ey := kqE) (hy := kqH) (g := cGW) (o := kqO) hI hctx
      ⟨by norm_num [sw], by norm_num [sw], by unfold kqSE sw; norm_num, by unfold kqSE sw; norm_num,
        by unfold kqSH sw; norm_num, by unfold kqSH sw; norm_num, by unfold kqE sw; norm_num,
        by unfold kqE sw; norm_num, by unfold kqH sw; norm_num, by unfold kqH sw; norm_num,
        by unfold cGW sw; norm_num, by unfold cGW sw; norm_num⟩
      ⟨by unfold kqO sw; norm_num, by unfold kqO sw; norm_num⟩ hq.1 htP.1 (by rwa [hgw])
      hq.2.1 htP.2.1 hq.2.2 htP.2.2 hroom) ?_
    rintro c₁ hI₁ hA₁ hA₁' ⟨b1, -, k₁, ha₁, hm₁⟩
    rw [hgw'] at b1
    change BitIs c₁ kqO (offK P J (c.nreg kqSE) (c.nreg kqSH) <
      offK P J (c.nreg kqE) (c.nreg kqH)) at b1
    have fr1 : EFr OffR c c₁ := ⟨fun r hr hX hra => k₁ r hr (fun h => hX (Or.inr (Or.inr
      (Or.inr (Or.inl h))))) (fun h => hX (Or.inr (Or.inr (Or.inr (Or.inr h))))) hra, ha₁, hm₁⟩
    have keep : ∀ r, r = kqF ∨ r = kqE ∨ r = kqH ∨ r = kqSE ∨ r = kqSH → c₁.nreg r = c.nreg r := by
      intro r hr
      have hr' : 242480 ≤ r ∧ r ≤ 242484 := by
        unfold kqF kqE kqH kqSE kqSH sw at hr; omega
      exact k₁ r (not_oracle_sw (by omega) (by omega)) (by unfold kqO sw; omega)
        (by unfold kqO sw; omega) (by unfold ALLOC; omega)
    have k01 : c₁.nreg K0 = 0 := by
      rwa [k₁ K0 (not_oracle_sw (by unfold K0 sw; omega) (by unfold K0 sw; omega))
        (by unfold K0 kqO sw; omega) (by unfold K0 kqO sw; omega) (by unfold K0 ALLOC sw; omega)]
    by_cases h2 : c₁.nreg K0 < c₁.nreg kqO
    · rw [k01] at h2
      have hlt := b1.2.1 (by have := b1.1; omega)
      refine IRS.mono (K := 3 + 2) (IRS.ifT (by rwa [k01]) (kqTake_irs hI₁ hW1))
        (by norm_num) ?_
      rintro c' ⟨e1, e2, e3, fr2⟩
      rw [keep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))] at e2
      rw [keep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))] at e3
      exact ⟨e1, Or.inr ⟨e2, e3⟩, by rw [e2, e3], fun _ => by rw [e2, e3]; exact hlt.le,
        fr1.trans fr2⟩
    · rw [k01] at h2
      have hnlt : ¬ offK P J (c.nreg kqSE) (c.nreg kqSH) < offK P J (c.nreg kqE) (c.nreg kqH) :=
        fun h => by have := b1.2.2 h; omega
      refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwa [k01]) (IRS.skip hI₁ rfl))
        (by norm_num) ?_
      rintro c' rfl
      have eF := keep _ (Or.inl rfl)
      have eE := keep _ (Or.inr (Or.inl rfl))
      have eH := keep _ (Or.inr (Or.inr (Or.inl rfl)))
      exact ⟨by rw [eF, hF1], Or.inl ⟨hF1, eE, eH⟩, by rw [eE, eH]; exact not_lt.1 hnlt,
        fun _ => by rw [eE, eH], fr1⟩
  · have hF0 : c.nreg kqF ≠ 1 := by omega
    refine IRS.mono (K := 3 + 2) (IRS.ifF h1 (kqTake_irs hI hW1)) (by norm_num) ?_
    rintro c' ⟨e1, e2, e3, fr2⟩
    exact ⟨e1, Or.inr ⟨e2, e3⟩, by rw [e2, e3], fun h => absurd h hF0, fr2⟩

/-! ## Stores -/

/-- Store the registers `vs` at `x, x + 1, …` (raising `x`). -/
def storeL (x : ℕ) : List ℕ → Stmt
  | [] => .skip
  | v :: vs => .seq (.instr (.storeN x v)) (.seq (.instr (.addN x x K1)) (storeL x vs))

/-- **The stores.** -/
theorem storeL_irs {x : ℕ} (hx : IScr x) (hx1 : x ≠ K1) :
    ∀ (vs : List ℕ) {c : Config}, IInv W c₀ c → c.nreg K1 = 1 → (∀ v ∈ vs, v ≠ x) →
      c₀.nreg ALLOC ≤ c.nreg x → c.nreg x + vs.length ≤ W →
      IRS P W c₀ (storeL x vs) c (2 * vs.length) (fun c' =>
        (∀ i (h : i < vs.length), c'.nmem (c.nreg x + i) = c.nreg (vs[i])) ∧
        (∀ y, (y < c.nreg x ∨ c.nreg x + vs.length ≤ y) → c'.nmem y = c.nmem y) ∧
        (∀ r, r ≠ x → c'.nreg r = c.nreg r))
  | [], c, hI, _, _, _, _ => IRS.skip hI ⟨fun i h => absurd h (by simp), fun _ _ => rfl,
      fun _ _ => rfl⟩
  | v :: vs, c, hI, hK1, hv, hA, hW => by
    have hvx : v ≠ x := hv v List.mem_cons_self
    simp only [List.length_cons] at hW ⊢
    have e : 2 * (vs.length + 1) = 1 + (1 + 2 * vs.length) := by ring
    rw [e]
    refine IRS.seq (IRS.store (v := v) hI hA) ?_
    rintro c₁ hI₁ - - rfl
    refine IRS.seq (IRS.instr1 (i := .addN x x K1) hI₁ ⟨hx, by simp only [hK1]; omega⟩) ?_
    rintro c₂ hI₂ - - rfl
    have hx2 : (upd c.nreg x (c.nreg x + c.nreg K1)) x = c.nreg x + 1 := by
      rw [upd_same, hK1]
    refine (storeL_irs hx hx1 vs hI₂ (by simp only [regI]; rw [upd_other _ _ _ (Ne.symm hx1)]; exact hK1)
      (fun w hw => hv w (List.mem_cons_of_mem _ hw))
      (by simp only [regI]; rw [hx2]; omega)
      (by simp only [regI]; rw [hx2]; omega)).mono le_rfl ?_
    rintro c' ⟨s1, s2, s3⟩
    simp only [regI, hx2] at s1 s2 s3
    refine ⟨fun i hi => ?_, fun y hy => ?_, fun r hr => ?_⟩
    · rcases i with _ | i
      · rw [s2 _ (Or.inl (by omega))]
        simp
      · have := s1 i (by simpa using hi)
        rw [show c.nreg x + (i + 1) = c.nreg x + 1 + i by ring, this]
        simp only [List.getElem_cons_succ]
        rw [upd_other _ _ _ (hv _ (List.mem_cons_of_mem _ (List.getElem_mem _)))]
    · rw [s2 _ (by omega)]
      simp only [upd]
      rw [ite_eq_right (by omega)]
    · rw [s3 r hr, upd_other _ _ _ hr]

/-! ## Loads -/

/-- Load the position of stop `sP`: `kqX = sB + 5 sP + 1`. -/
def ldStopL : List Instr :=
  [.addN kqX sP sP, .addN kqX kqX kqX, .addN kqX kqX sP, .addN kqX kqX sB, .loadN kqSE kqX,
    .addN kqX kqX K1, .loadN kqSH kqX]

theorem ldStop_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1)
    (hW : c.nreg sB + 5 * c.nreg sP + 1 ≤ W) :
    IRS P W c₀ (block ldStopL) c 7 (fun c' =>
      c'.nreg kqSE = c.nmem (c.nreg sB + 5 * c.nreg sP) ∧
      c'.nreg kqSH = c.nmem (c.nreg sB + 5 * c.nreg sP + 1) ∧
      (∀ q, q ≠ kqX → q ≠ kqSE → q ≠ kqSH → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, K1, sB, sP, Nat.reduceAdd] at hK1 hW
  refine (IRS.block ldStopL hI ?_).mono le_rfl ?_
  · simp [ldStopL, okB, okI, regI, upd, kqX, kqSE, kqSH, sP, sB, K1, sw, IScr, hK1]
    omega
  · rintro c' rfl
    simp [ldStopL, regB, regI, upd, kqX, kqSE, kqSH, sP, sB, K1, sw, hK1]
    refine ⟨by ring_nf, by ring_nf, ?_⟩
    intro r ha hb hc
    simp [ha, hb, hc]

/-- Load the flag of the auxiliary record `sP`: `kqX = aB + 5 sP`. -/
def ldAuxL : List Instr :=
  [.addN kqX sP sP, .addN kqX kqX kqX, .addN kqX kqX sP, .addN kqX kqX aB, .loadN kqV kqX]

theorem ldAux_irs (hI : IInv W c₀ c) (hW : c.nreg aB + 5 * c.nreg sP ≤ W) :
    IRS P W c₀ (block ldAuxL) c 5 (fun c' =>
      c'.nreg kqX = c.nreg aB + 5 * c.nreg sP ∧
      c'.nreg kqV = c.nmem (c.nreg aB + 5 * c.nreg sP) ∧
      (∀ q, q ≠ kqX → q ≠ kqV → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, aB, sP, Nat.reduceAdd] at hW
  refine (IRS.block ldAuxL hI ?_).mono le_rfl ?_
  · simp [ldAuxL, okB, okI, regI, upd, kqX, kqV, sP, aB, sw, IScr]
    omega
  · rintro c' rfl
    simp [ldAuxL, regB, regI, upd, kqX, kqV, sP, aB, sw]
    refine ⟨by ring_nf, by ring_nf, ?_⟩
    intro r ha hb
    simp [ha, hb]

/-- Advance `kqX` and load `kqV` (resp. `kqY`) from it. -/
theorem ldNext_irs {r : ℕ} (hr : r = kqV ∨ r = kqY) (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1)
    (hW : c.nreg kqX + 1 ≤ W) :
    IRS P W c₀ (block [.addN kqX kqX K1, .loadN r kqX]) c 2 (fun c' =>
      c'.nreg kqX = c.nreg kqX + 1 ∧ c'.nreg r = c.nmem (c.nreg kqX + 1) ∧
      (∀ q, q ≠ kqX → q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, K1, kqX, Nat.reduceAdd] at hK1 hW
  refine (IRS.block _ hI ?_).mono le_rfl ?_
  · rcases hr with rfl | rfl <;>
    simp [okB, okI, kqX, kqV, kqY, K1, sw, IScr, hK1] <;> omega
  · rintro c' rfl
    rcases hr with rfl | rfl <;>
    · simp [regB, regI, upd, kqX, kqV, kqY, K1, sw, hK1]
      intro r ha hb
      simp [ha, hb]

end

end SweepEv

end Chazelle.Core
