module

meta import Chazelle.Programs.RegisterGuard

public import Chazelle.Core.SweepEvCand2

/-!
# The sweep (WP-D), stage 3: one candidate (RAM), the accepting tail

`evAccT_irs`: after a genuine hit before the far end, the map, the table write and the offer:
the candidate is accepted at `(mEdge d, h)` if the offset `d` is valid (`MVal`), else rejected.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem mEdge_eq {J : Merge.Junction} (d : ℕ) :
    ((gW J + Lst J) % J.wholeModel.W.n + ψ J d) % J.wholeModel.W.n = mEdge J d := by
  unfold mEdge; rw [Nat.mod_add_mod, add_assoc]

theorem ψ_le (J : Merge.Junction) (d : ℕ) : ψ J d ≤ d := by
  unfold ψ; split_ifs <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The accepting tail.** -/
theorem evAccT_irs {J : Merge.Junction} {S₂ : Set (Set Point)} (hI : IInv W c₀ c)
    (hK₀ : Consts c₀) (hM₀ : MapK J c₀) (hP : J.P.Simple) (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {ch : Set Point} (hch : ch ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend ch) ∨ (σ = -1 ∧ a = Merge.rend ch)) (haR : a ∈ J.right.set)
    (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < (Merge.rend ch).1 - (Merge.lend ch).1)
    (hpA : c.nreg (eA + 1) < J.leftModel.W.n)
    (hpp : ProperPos J.leftModel (Qof P) P.n ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩)
    (hnorm : c.nreg (eA + 2) = 0 ↔
      J.leftModel.param (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩ = 0)
    (hA : Arrival J.leftModel.W (rayPt a σ τ) σ (c.nreg (eA + 1))
      (J.leftModel.param (Qof P) ⟨c.nreg (eA + 1), c.nreg (eA + 2)⟩))
    (hctx₀ : ChainCtx P W c₀ (sw 2) J.whole) (hgw₀ : c₀.nreg cGW = gW J)
    (hk : PosW P J (c.nreg kE) (c.nreg kH)) (hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH))
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4) (hT : c₀.nreg ALLOC ≤ c.nreg cTB)
    (hTW : c.nreg cTB + 3 * (2 * c.nreg oK + c.nreg oS) + 2 ≤ W)
    (hW : 2 * J.wholeModel.W.n ≤ W) (hroom : c.nreg ALLOC + 22300 ≤ W) :
    IRS P W c₀ evAccT c 22300 (fun c' =>
      (SweepEv.MVal J ((c.nreg (eA + 1) + J.leftModel.W.n - b₁ J) %
          J.leftModel.W.n) (c.nreg (eA + 2)) →
        AccAt P J S₂ (c.nreg cTB) (2 * c.nreg oK + c.nreg oS) (c.nreg oUp) (c.nreg oDn) a σ c c'
          (mEdge J ((c.nreg (eA + 1) + J.leftModel.W.n - b₁ J) %
            J.leftModel.W.n)) (c.nreg (eA + 2))) ∧
      (¬ SweepEv.MVal J ((c.nreg (eA + 1) + J.leftModel.W.n - b₁ J) %
          J.leftModel.W.n) (c.nreg (eA + 2)) → RejAt c c') ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  have hn1 : J.leftModel.W.n ≤ J.wholeModel.W.n := by
    simp [cm_n]
  have hgn : gW J < J.wholeModel.W.n := by
    unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega
  set n₁ := J.leftModel.W.n with hn₁
  set d := (c.nreg (eA + 1) + n₁ - b₁ J) % n₁ with hd
  set hN := c.nreg (eA + 2) with hhN
  -- 1. the map
  refine IRS.seq (K₁ := 20) (K₂ := 22280) (mapC_irs hI hK₀ hM₀ hpA (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨m1, m2, m3, m4, m5, m6⟩
  have kk₁ := m5
  have k01 := (hK₀.fix hI₁).1
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := kk₁ _ (by reg_omega)
    (by reg_omega) (by reg_omega)
  
  by_cases hv : c₁.nreg K0 < c₁.nreg cV
  · rw [k01] at hv
    have hv1 : c₁.nreg cV = 1 := by omega
    have hMV := m3.1 hv1
    have hps := m4 hv1
    refine IRS.mono (K := 22278 + 2) (IRS.ifT (by rwa [k01]) ?_) le_rfl (fun _ h => h)
    have hψn : ψ J d < J.wholeModel.W.n := by
      have := ψ_le J d
      have : d < n₁ := Nat.mod_lt _ (by rw [hn₁, cm_n]; omega)
      omega
    -- 2. the walk edge
    refine IRS.seq (K₁ := 4) (K₂ := 22274) (mapE_irs hI₁ hM₀ (by rwa [hps]) hW) ?_
    rintro c₂ hI₂ hA₂ hA₂' ⟨e2, k2, mm2⟩
    rw [hps, mEdge_eq] at e2
    have kk₂ := fun r h1 h2 h3 h4 =>
      (k2 r h4).trans (kk₁ r h1 h2 h3)
    have eTB : c₂.nreg cTB = c.nreg cTB := kk₂ _ (by register_guard) (by register_guard)
      (by reg_omega) (by reg_omega)
    have eK : c₂.nreg oK = c.nreg oK := kk₂ _ (by register_guard) (by register_guard)
      (by register_guard) (by register_guard)
    have eS : c₂.nreg oS = c.nreg oS := kk₂ _ (by register_guard) (by register_guard)
      (by register_guard) (by register_guard)
    have eH2 : c₂.nreg (eA + 2) = hN := kk₂ _ (by register_guard) (by register_guard)
      (by register_guard) (by register_guard)
    -- 3. the table write
    refine IRS.seq (K₁ := 16) (K₂ := 22258) (tabW_irs hI₂ hK₀ (by rwa [eTB])
      (by rwa [eTB, eK, eS])) ?_
    rintro c₃ hI₃ hA₃ hA₃' ⟨mm3, k3⟩
    have kk₃ := fun r h1 h2 h3 h4 h5 => (k3 r h5).trans (kk₂ r h1 h2 h3 h4)
    have kk₃' : ∀ r, (r < sw 2260 ∨ sw 2273 < r) → c₃.nreg r = c.nreg r := fun r hr =>
      kk₃ r (by register_guard) (by register_guard) (by register_guard)
        (by register_guard) (by register_guard)
    have eME3 : c₃.nreg cME = mEdge J d := by
      ram_rw [k3, e2]
    have eH3 : c₃.nreg (eA + 2) = hN := by ram_rw [k3, eH2]
    have hA3 : c₃.nreg ALLOC = c.nreg ALLOC := kk₃' _ (by register_guard)
    -- the candidate
    have hcand := candOK_of (S₂ := S₂) hP hS₂ hS₂f hch ha haR hav ha₁ hg hlt hpA hpp hnorm hA hMV
    have hposW : PosW P J (c₃.nreg cME) (c₃.nreg (eA + 2)) := by
      rw [eME3, eH3]; exact hcand.2.2.2.2.2.1
    have hctx₃ := hctx₀.transport (hI₃.hin _ (by register_guard)) hI₃.hm hI₃.hA
    have hgw₃ := (hI₃.hin _ (by register_guard)).trans hgw₀
    have sameB : ∀ r, BestR r → c₃.nreg r = c.nreg r := fun r hr => kk₃' r
      (by unfold BestR LblR bF bE bH bN bL sw at hr; unfold sw; omega)
    have eKE : c₃.nreg kE = c.nreg kE := kk₃' _ (by register_guard)
    have eKH : c₃.nreg kH = c.nreg kH := kk₃' _ (by register_guard)
    have eUp : c₃.nreg oUp = c.nreg oUp := kk₃' _ (by register_guard)
    have eDn : c₃.nreg oDn = c.nreg oDn := kk₃' _ (by register_guard)
    have eBF := sameB _ (Or.inl rfl)
    have eBE := sameB _ (Or.inr (Or.inl rfl))
    have eBH := sameB _ (Or.inr (Or.inr (Or.inl rfl)))
    have eBN := sameB _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have eLb := lblOf_congr (fun q hq => sameB q (Or.inr (Or.inr (Or.inr hq))))
    have bsame : ∀ c' : Config, BestSame c₃ c' → BestSame c c' := fun c' h =>
      ⟨h.1.trans eBF, h.2.1.trans eBE, h.2.2.1.trans eBH, h.2.2.2.1.trans eLb,
        h.2.2.2.2.trans eBN⟩
    refine (offerC_irs hI₃ hK₀ hctx₃ hgw₃ hgn hposW (by rwa [eKE, eKH])
      (by rwa [eBF, eBE, eBH]) (by rwa [eBF]) (by rwa [eBN])
      (by omega)).mono (by norm_num) ?_
    rintro c' ⟨o1, o2, o3, o4, o5, o6, ofr⟩
    rw [eKE, eKH, eME3, eH3] at o3
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH, eUp, eDn] at o4
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH, eLb, eUp, eDn] at o5
    rw [eKE, eKH, eME3, eH3, eBF, eBE, eBH] at o6
    refine ⟨fun _ => ⟨hcand, fun x hx => ?_, o1, o2, fun h => bsame c' (o3 h), o4,
      fun h1 h2 h3 => ?_, fun h1 h2 h3 => bsame c' (o6 h1 h2 h3)⟩, fun h => absurd hMV h,
      fun r hr hX hra => ?_, ?_⟩
    · ram_rw [ofr.2.2 x, mm3, mm2, m6, eTB, eK, eS, e2, eH2]; rfl
    · obtain ⟨q1, q2, q3, q4⟩ := o5 h1 h2 h3
      exact ⟨q1, q2, q3, q4⟩
    · rw [ofr.1 r hr (fun h => hX (by
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl ⟨by unfold cO sw at h; unfold sw; omega,
            by unfold cO2 sw at h; unfold sw; omega⟩))) hra]
      exact kk₃' r (by
        by_contra h; push Not at h
        exact hX (Or.inr (Or.inl (by reg_omega))))
    · rw [← hA3]; exact ofr.2.1
  · rw [k01] at hv
    have hnv : ¬ SweepEv.MVal J d hN := fun h => by have := m3.2 h; omega
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwa [k01]) (IRS.skip hI₁ rfl)) (by norm_num) ?_
    rintro c' rfl
    refine ⟨fun h => absurd h hnv, fun _ => ⟨fun x _ => by rw [m6], ?_⟩, fun r _ hr hra => ?_, hA1.ge⟩
    · have same : ∀ r, BestR r → c₁.nreg r = c.nreg r := fun r hr => kk₁ r
        (by register_guard)
        (by register_guard)
        (by register_guard)
      exact ⟨same _ (Or.inl rfl), same _ (Or.inr (Or.inl rfl)), same _ (Or.inr (Or.inr (Or.inl rfl))),
        lblOf_congr (fun q hq => same q (Or.inr (Or.inr (Or.inr hq)))),
        same _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact kk₁ r (fun h => hr (Or.inr (Or.inl ⟨by rw [h]; unfold cD sw; omega, by rw [h]; unfold cD sw; omega⟩)))
        (fun h => hr (Or.inr (Or.inl ⟨by rw [h]; unfold cV sw; omega, by rw [h]; unfold cV sw; omega⟩)))
        (fun h => hr (Or.inr (Or.inl (by reg_omega))))

end

end SweepEv

end Chazelle.Core
