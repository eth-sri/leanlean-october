module

public import Chazelle.Core.SweepEvMapR

/-!
# The sweep (WP-D), stage 3: the far-end test and the walk edge of a candidate (RAM)

* `farChk`: the abscissae of the hit (arrival position `(eA + 1, eA + 2)` of `M₁`) and of the far
  end `(oFE, oFC)` of the chord (in `M₂`), compared in the direction `oD`: the bit `cFr`.
* `mapE`: the walk edge `mEdge d` of `M` from `ψ d` (`cPs`): `cME`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)

@[expose] public section

def cAW : ℕ := sw 2264
def cAF : ℕ := sw 2268
def cFr : ℕ := sw 2272

/-- **The far-end test.** -/
def farChk : Stmt :=
  .seq (callAbs CD₁ (eA + 1) (eA + 2) cAW) (.seq (callAbs (sw 21) oFE oFC cAF)
    (.ifLtN K0 oD (callAbsCmp cAW cAF cFr) (callAbsCmp cAF cAW cFr)))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The far-end test**: `cFr = 1` iff the hit is before the far end in the direction `oD`. -/
theorem farChk_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx1 : ChainCtx P W c CD₁ J.left) (hctx2 : ChainCtx P W c (sw 21) J.right)
    (he1 : c.nreg (eA + 1) < (chainModel J.left).W.n)
    (hpp1 : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩)
    (hy1 : |((chainModel J.left).pos (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩).2| <
      J.left.radius)
    (he2 : c.nreg oFE < (chainModel J.right).W.n)
    (hpp2 : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oFE, c.nreg oFC⟩)
    (hy2 : |((chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩).2| < J.right.radius)
    (hD : c.nreg oD ≤ 1) (hroom : c.nreg ALLOC + 34000 ≤ W) :
    IRS P W c₀ farChk c 34000 (fun c' =>
      BitIs c' cFr (if c.nreg oD = 1 then
          ((chainModel J.left).pos (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩).1 <
            ((chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩).1
        else ((chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩).1 <
            ((chainModel J.left).pos (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩).1) ∧
      EFr (fun r => cAW ≤ r ∧ r ≤ cFr) c c') := by
  have hK := hK₀.fix hI
  have hG := hctx1.1
  have hPW : P.n + 3 ≤ W := by have := hctx1.2.1; unfold hostWords at this; omega
  set x₁ := ((chainModel J.left).pos (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩).1 with hx₁
  set x₂ := ((chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩).1 with hx₂
  refine IRS.seq (K₁ := 16707) (K₂ := 17293) (callAbs_irs (dsc := CD₁) (re := eA + 1)
    (rh := eA + 2) (o := cAW) hI hctx1
    ⟨by unfold CD₁ sw; norm_num, by unfold CD₁ sw; norm_num, by unfold eA sw; norm_num,
      by unfold eA sw; norm_num, by unfold eA sw; norm_num, by unfold eA sw; norm_num⟩
    ⟨by unfold cAW sw; norm_num, by unfold cAW sw; norm_num⟩ he1 hpp1 hy1 (by omega)) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨hr₁, k₁, ha₁, hm₁⟩
  have kk₁ : ∀ r, 240000 ≤ r → r < 250000 → (r < cAW ∨ cAW + 3 < r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => k₁ r (not_oracle_sw h1 h2) h3 (by unfold ALLOC; omega)
  have hctx2' : ChainCtx P W c₁ (sw 21) J.right :=
    hctx2.transport (kk₁ _ (by norm_num [sw]) (by norm_num [sw]) (by unfold cAW sw; omega)) hm₁ ha₁
  have eFE : c₁.nreg oFE = c.nreg oFE := kk₁ _ (by unfold oFE sw; norm_num) (by unfold oFE sw; norm_num)
    (by unfold oFE cAW sw; omega)
  have eFC : c₁.nreg oFC = c.nreg oFC := kk₁ _ (by unfold oFC sw; norm_num) (by unfold oFC sw; norm_num)
    (by unfold oFC cAW sw; omega)
  refine IRS.seq (K₁ := 16707) (K₂ := 586) (callAbs_irs (dsc := sw 21) (re := oFE)
    (rh := oFC) (o := cAF) hI₁ hctx2'
    ⟨by norm_num [sw], by norm_num [sw], by unfold oFE sw; norm_num, by unfold oFE sw; norm_num,
      by unfold oFC sw; norm_num, by unfold oFC sw; norm_num⟩
    ⟨by unfold cAF sw; norm_num, by unfold cAF sw; norm_num⟩ (by rw [eFE]; exact he2)
    (by rw [eFE, eFC]; exact hpp2) (by rw [eFE, eFC]; exact hy2) (by omega)) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨hr₂, k₂, ha₂, hm₂⟩
  rw [eFE, eFC] at hr₂
  have kk₂ : ∀ r, 240000 ≤ r → r < 250000 → (r < cAF ∨ cAF + 3 < r) → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => k₂ r (not_oracle_sw h1 h2) h3 (by unfold ALLOC; omega)
  have hr₁' : AbsRec P c₂ cAW x₁ J.left.radius :=
    ShotList.absRec_copy hr₁ (kk₂ _ (by unfold cAW sw; norm_num) (by unfold cAW sw; norm_num)
      (by unfold cAW cAF sw; omega))
      (kk₂ _ (by unfold cAW sw; norm_num) (by unfold cAW sw; norm_num) (by unfold cAW cAF sw; omega))
      (kk₂ _ (by unfold cAW sw; norm_num) (by unfold cAW sw; norm_num) (by unfold cAW cAF sw; omega))
      (kk₂ _ (by unfold cAW sw; norm_num) (by unfold cAW sw; norm_num) (by unfold cAW cAF sw; omega))
  have hR : J.right.radius = J.left.radius := rfl
  rw [hR] at hr₂
  have eD : c₂.nreg oD = c.nreg oD := by
    rw [kk₂ _ (by unfold oD sw; norm_num) (by unfold oD sw; norm_num) (by unfold oD cAF sw; omega),
      kk₁ _ (by unfold oD sw; norm_num) (by unfold oD sw; norm_num) (by unfold oD cAW sw; omega)]
  have k02 : c₂.nreg K0 = 0 := (hK₀.fix hI₂).1
  have fr2 : EFr (fun r => cAW ≤ r ∧ r ≤ cFr) c c₂ := by
    refine ⟨fun r hr hX hra => ?_, ha₁.trans ha₂, fun a ha => by rw [hm₂ a (by omega), hm₁ a ha]⟩
    rw [k₂ r hr (by by_contra h; push Not at h; exact hX ⟨by unfold cAW cAF sw at *; omega,
      by unfold cAF cFr sw at *; omega⟩) hra]
    exact k₁ r hr (by by_contra h; push Not at h; exact hX ⟨by unfold cAW sw at *; omega,
      by unfold cAW cFr sw at *; omega⟩) hra
  have hroom2 : c₂.nreg ALLOC + 269 ≤ W := by omega
  have fr3 : ∀ c', (∀ r, bandOf r ∉ oracleBands → r ≠ cFr → r ≠ ALLOC → c'.nreg r = c₂.nreg r) →
      c₂.nreg ALLOC ≤ c'.nreg ALLOC → (∀ a, a < c₂.nreg ALLOC → c'.nmem a = c₂.nmem a) →
      EFr (fun r => cAW ≤ r ∧ r ≤ cFr) c c' := fun c' k₃ ha₃ hm₃ =>
    fr2.trans ⟨fun r hr hX hra => k₃ r hr (fun h => hX ⟨by rw [h]; unfold cAW cFr sw; omega,
      by rw [h]⟩) hra, ha₃, hm₃⟩
  by_cases hd : c₂.nreg K0 < c₂.nreg oD
  · rw [k02, eD] at hd
    have hd1 : c.nreg oD = 1 ∨ 1 < c.nreg oD := by omega
    refine IRS.mono (K := 269 + 2) (IRS.ifT (by rw [k02, eD]; exact hd) (callAbsCmp_irs (a := cAW)
      (b := cAF) (o := cFr) hI₂ hG hPW ⟨by unfold cAW sw; norm_num, by unfold cAW sw; norm_num,
        by unfold cAF sw; norm_num, by unfold cAF sw; norm_num⟩
      ⟨by unfold cFr sw; norm_num, by unfold cFr sw; norm_num⟩ hr₁' hr₂ hroom2)) (by norm_num) ?_
    rintro c' ⟨hb, k₃, ha₃, hm₃⟩
    have h1 : c.nreg oD = 1 := by omega
    refine ⟨hb.congr (by rw [ite_eq_left h1]), fr3 c' k₃ ha₃ hm₃⟩
  · rw [k02, eD] at hd
    have h0 : c.nreg oD ≠ 1 := by omega
    refine IRS.mono (K := 269 + 2) (IRS.ifF (by rw [k02, eD]; exact hd) (callAbsCmp_irs (a := cAF)
      (b := cAW) (o := cFr) hI₂ hG hPW ⟨by unfold cAF sw; norm_num, by unfold cAF sw; norm_num,
        by unfold cAW sw; norm_num, by unfold cAW sw; norm_num⟩
      ⟨by unfold cFr sw; norm_num, by unfold cFr sw; norm_num⟩ hr₂ hr₁' hroom2)) (by norm_num) ?_
    rintro c' ⟨hb, k₃, ha₃, hm₃⟩
    refine ⟨hb.congr (by rw [ite_eq_right h0]), fr3 c' k₃ ha₃ hm₃⟩

/-! ## The walk edge -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The walk edge of `M`**: `cME := (cGL + cPs) mod n` (`cGL, cPs < n`). -/
theorem mapE_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hps : c.nreg cPs < (chainModel J.whole).W.n) (hW : 2 * (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ mapE c 4 (fun c' =>
      c'.nreg cME = ((gW J + Lst J) % (chainModel J.whole).W.n + c.nreg cPs) %
        (chainModel J.whole).W.n ∧
      (∀ r, r ≠ cME → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hM := hM₀.fix hI
  have hgl : (gW J + Lst J) % (chainModel J.whole).W.n < (chainModel J.whole).W.n :=
    Nat.mod_lt _ (by rw [cm_n]; omega)
  have hsM : IScr cME := iscr_sw' (by norm_num) (by norm_num)
  refine IRS.seq (K₁ := 1) (K₂ := 3) (IRS.block [.addN cME cGL cPs] hI
    ⟨⟨hsM, by rw [hM.gl]; omega⟩, trivial⟩) ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - rfl
  obtain ⟨c₂, k₂, hk₂, ex₂, v₂, o₂⟩ := condSub_exec (P := P)
    (c := { c with nreg := regB c.nmem [.addN cME cGL cPs] c.nreg }) hI₁.hw cME cME cNW
  refine (irs_of_out hI₁ ex₂ hk₂ o₂ (by simp [hsM])).mono le_rfl ?_
  rintro c' rfl
  obtain ⟨or₂, -, om₂, -, -⟩ := o₂
  simp only [regB, regI, upd_same] at v₂
  have hnw : upd c.nreg cME (c.nreg cGL + c.nreg cPs) cNW = (chainModel J.whole).W.n := by
    rw [upd_other _ _ _ (by unfold cNW cME sw; omega), hM.nw]
  rw [hnw, hM.gl] at v₂
  refine ⟨?_, fun r hr => ?_, om₂⟩
  · rw [v₂]
    by_cases h : (gW J + Lst J) % (chainModel J.whole).W.n + c.nreg cPs < (chainModel J.whole).W.n
    · rw [ite_eq_left h, Nat.mod_eq_of_lt h]
    · rw [ite_eq_right h]
      generalize hX : (gW J + Lst J) % (chainModel J.whole).W.n + c.nreg cPs = X at h ⊢
      have hX2 : X < 2 * (chainModel J.whole).W.n := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [or₂ r (by simp [hr])]
    simp only [regB, regI]
    exact upd_other _ _ _ hr

/-! ## The table write -/

def cTB : ℕ := sw 661
def cTA : ℕ := sw 2273

/-- The address of the table record of the end `oS` of chord `oK`. -/
def tabAddrL : List Instr :=
  [.copyN cTA cTB, .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oK,
    .addN cTA cTA oK, .addN cTA cTA oK, .addN cTA cTA oS, .addN cTA cTA oS, .addN cTA cTA oS]

/-- **The table write**: `(1, cME, eA + 2)` at `cTB + 3 (2 oK + oS)`. -/
def tabW : Stmt :=
  .seq (block tabAddrL) (.seq (.instr (.storeN cTA K1)) (.seq (block [.addN cTA cTA K1])
    (.seq (.instr (.storeN cTA cME)) (.seq (block [.addN cTA cTA K1]) (.instr (.storeN cTA (eA + 2)))))))

theorem tabAddrL_val (m f : ℕ → ℕ) :
    regB m tabAddrL f cTA = f cTB + 3 * (2 * f oK + f oS) ∧
      ∀ q, q ≠ cTA → regB m tabAddrL f q = f q := by
  have hK : oK ≠ cTA := by unfold oK cTA sw; omega
  have hS : oS ≠ cTA := by unfold oS cTA sw; omega
  have hB : cTB ≠ cTA := by unfold cTB cTA sw; omega
  refine ⟨?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [tabAddrL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> exact fun h => hq h.symm)⟩
  simp only [tabAddrL, regB, regI, upd_same, upd_other _ _ _ hK, upd_other _ _ _ hS]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The table write.** -/
theorem tabW_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hT : c₀.nreg ALLOC ≤ c.nreg cTB)
    (hW : c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS) + 2 ≤ W) :
    IRS P W c₀ tabW c 16 (fun c' =>
      c'.nmem = upd (upd (upd c.nmem (c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS)) 1)
        (c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS) + 1) (c.nreg cME))
        (c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS) + 2) (c.nreg (eA + 2)) ∧
      (∀ r, r ≠ cTA → c'.nreg r = c.nreg r)) := by
  have hK := hK₀.fix hI
  have k1 : c.nreg K1 = 1 := hK.2.1
  have hsA : IScr cTA := iscr_sw' (by norm_num) (by norm_num)
  have hK' : oK ≠ cTA := by unfold oK cTA sw; omega
  have hS' : oS ≠ cTA := by unfold oS cTA sw; omega
  have hB' : cTB ≠ cTA := by unfold cTB cTA sw; omega
  set A := c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS) with hA
  have hok : okB W c.nmem tabAddrL c.nreg := by
    simp only [tabAddrL, okB, okI, regI, upd_same, upd_other _ _ _ hK', upd_other _ _ _ hS']
    refine ⟨hsA, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩,
      ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, ⟨hsA, by omega⟩, trivial⟩
  obtain ⟨va, vo⟩ := tabAddrL_val c.nmem c.nreg
  have nK1 : K1 ≠ cTA := by unfold K1 cTA sw; omega
  have nME : cME ≠ cTA := by unfold cME cTA sw; omega
  have nE2 : eA + 2 ≠ cTA := by unfold eA cTA sw; omega
  refine IRS.seq (K₁ := 10) (K₂ := 6) (IRS.block tabAddrL hI hok) ?_
  rintro c₁ hI₁ - - hc1
  have a1 : c₁.nreg cTA = A := by rw [hc1]; exact va
  have o1 : ∀ q, q ≠ cTA → c₁.nreg q = c.nreg q := fun q hq => by rw [hc1]; exact vo q hq
  have m1 : c₁.nmem = c.nmem := by rw [hc1]
  refine IRS.seq (K₁ := 1) (K₂ := 5) (IRS.store hI₁ (by rw [a1]; omega)) ?_
  rintro c₂ hI₂ - - hc2
  have r2 : c₂.nreg = c₁.nreg := by rw [hc2]
  have m2 : c₂.nmem = upd c.nmem A 1 := by rw [hc2]; simp only; rw [a1, o1 _ nK1, k1, m1]
  refine IRS.seq (K₁ := 1) (K₂ := 4) (IRS.block [.addN cTA cTA K1] hI₂
    ⟨⟨hsA, by rw [r2, a1, o1 _ nK1, k1]; omega⟩, trivial⟩) ?_
  rintro c₃ hI₃ - - hc3
  have a3 : c₃.nreg cTA = A + 1 := by
    rw [hc3]; simp only [regB, regI, upd_same]; rw [r2, a1, o1 _ nK1, k1]
  have o3 : ∀ q, q ≠ cTA → c₃.nreg q = c.nreg q := fun q hq => by
    rw [hc3]; simp only [regB, regI]; rw [upd_other _ _ _ hq, r2, o1 q hq]
  have m3 : c₃.nmem = upd c.nmem A 1 := by rw [hc3]; exact m2
  refine IRS.seq (K₁ := 1) (K₂ := 3) (IRS.store hI₃ (by rw [a3]; omega)) ?_
  rintro c₄ hI₄ - - hc4
  have r4 : c₄.nreg = c₃.nreg := by rw [hc4]
  have m4 : c₄.nmem = upd (upd c.nmem A 1) (A + 1) (c.nreg cME) := by
    rw [hc4]; simp only; rw [a3, o3 _ nME, m3]
  refine IRS.seq (K₁ := 1) (K₂ := 2) (IRS.block [.addN cTA cTA K1] hI₄
    ⟨⟨hsA, by rw [r4, a3, o3 _ nK1, k1]; omega⟩, trivial⟩) ?_
  rintro c₅ hI₅ - - hc5
  have a5 : c₅.nreg cTA = A + 2 := by
    rw [hc5]; simp only [regB, regI, upd_same]; rw [r4, a3, o3 _ nK1, k1]
  have o5 : ∀ q, q ≠ cTA → c₅.nreg q = c.nreg q := fun q hq => by
    rw [hc5]; simp only [regB, regI]; rw [upd_other _ _ _ hq, r4, o3 q hq]
  have m5 : c₅.nmem = upd (upd c.nmem A 1) (A + 1) (c.nreg cME) := by rw [hc5]; exact m4
  refine (IRS.store hI₅ (by rw [a5]; omega)).mono (by norm_num) ?_
  rintro c' hc'
  rw [hc']
  simp only
  refine ⟨by rw [a5, o5 _ nE2, m5], fun r hr => o5 r hr⟩

end

end SweepEv

end Chazelle.Core
