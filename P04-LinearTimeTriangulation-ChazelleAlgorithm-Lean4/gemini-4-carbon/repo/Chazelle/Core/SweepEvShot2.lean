module

public import Chazelle.Core.SweepEvShot
public import Chazelle.Core.SweepEvCand

/-!
# The sweep (WP-D), stage 3: the shot of a candidate (RAM), the run

`evShot_irs`: the contract `ShotOut` of `evShot`, from the symbolic point of a valid origin (a
point of `C₂` other than the shared vertex, not above the top of `C₁`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A valid origin lies in the domain of `C₁`. -/
theorem origin_mem_left_dom {J : Merge.Junction} (hP : J.P.Simple) {a : Point}
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) : a ∈ J.left.dom := by
  by_contra hn
  rcases (Merge.not_mem_dom_iff J.left ha₁).1 hn with hb | hs
  · have hR : J.left.radius = J.right.radius := rfl
    rw [hR] at hb; exact hb (J.right.set_subset_box haR)
  · exact not_mem_left_of_right hP haR hav hs

/-- The direction of a code `≤ 1` and of its complement. -/
theorem dirOf_rev {d : ℕ} (hd : d ≤ 1) : -dirOf (1 - d) = dirOf d := by
  unfold dirOf
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with rfl | rfl <;> norm_num

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The shot of a candidate.** -/
theorem evShot_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {J : Merge.Junction} {N : NF} {L : List ℕ}
    (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hP : J.P.Simple)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel J.left)) (hNF : IsNF (chainModel J.left) (Qof P) N)
    (hsg : (chainModel J.left).Semigranular (N.F (chainModel J.left) (Qof P)) (c₀.nreg (sw 5)))
    (hmd : ModelDescAt c.nmem (c.nreg MD₁) (Qof P) (chainModel J.left))
    (hmwf : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg MD₁)) (hm0 : c.nmem (c.nreg MD₁) = 0)
    (hctx : ChainCtx P W c CD₁ J.left) (hcd : c.nreg CD₁ = c.nreg MD₁ + 1)
    (hL : ∀ a ∈ L, a < N.arcs.length) (hgK : c.nreg wGK = L.length)
    (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem (c.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N (L.getD k 0))
    {s : SymPt} (hs : SymPtIn c oSym s) (hsl : s.Lt P.n)
    (haR : s.eval (Qof P) ∈ J.right.set) (hav : s.eval (Qof P) ≠ J.shared)
    (ha₁ : (s.eval (Qof P)).2 ≤ J.left.top.2) (hD : c.nreg oD ≤ 1)
    (hroom : c.nreg ALLOC + evShotK (F (c₀.nreg (sw 5))) L.length ≤ W) :
    IRS P W c₀ (evShot sh) c (evShotK (F (c₀.nreg (sw 5))) L.length) (fun c' =>
      ShotOut P J c.nmem (c.nreg wGB) L.length (s.eval (Qof P)) (dirOf (c.nreg oD)) c' ∧
      EFr ShW c c') := by
  have hK := hK₀.fix hI
  set a := s.eval (Qof P) with ha
  set σ := dirOf (c.nreg oD) with hσ
  set K := L.length with hKd
  have hσ' : σ = 1 ∨ σ = -1 := by rw [hσ]; unfold dirOf; split_ifs <;> simp
  have hW2 : 2 ≤ W := by unfold hostWords at hWh; have := hG.1.1; nlinarith
  have hPW : P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  have haD : a ∈ J.left.dom := origin_mem_left_dom hP haR hav ha₁
  have hR₁ : J.left.radius = J.right.radius := rfl
  have hay : |a.2| < J.left.radius := by
    rw [hR₁]
    exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2 J.right.coordBound_lt_radius
  -- 1. prepare the shot block
  have hok : okB W c.nmem evPrepL c.nreg := by
    simp only [evPrepL, okB, okI]
    exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), by omega⟩,
      iscr_sw (by unfold eRD sw; norm_num) (by unfold eRD sw; norm_num), trivial⟩
  refine IRS.seq (K₂ := ShotList.shotCost (F (c₀.nreg (sw 5))) K + 49989)
    (IRS.block evPrepL hI hok) ?_ |>.mono
    (by simp only [evPrepL, evShotK, List.length_cons, List.length_nil]; omega) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, pR, po⟩ := evPrepL_val c.nmem c.nreg
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have q1 : ∀ q, (q < 241300 ∨ 241309 < q) → q ≠ eRD → c₁.nreg q = c.nreg q := fun q hq hq' => by
    rw [hc1]; exact po q hq hq'
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := q1 _ (by unfold ALLOC; omega) (by unfold eRD ALLOC sw; omega)
  have c0 : c₁.nreg RS = c.nreg MD₁ := by rw [hc1]; exact p0
  have c1' : c₁.nreg (RS + 1) = c.nreg wGB := by rw [hc1]; exact p1
  have c2' : c₁.nreg (RS + 2) = K := by rw [hc1]; show regB _ _ _ 241302 = _; rw [p2, hgK]
  have c6 : c₁.nreg (RS + 6) = c.nreg oD := by rw [hc1]; exact p6
  have c7 : c₁.nreg (RS + 7) = c₀.nreg (sw 5) := by
    rw [hc1]; show regB _ _ _ 241307 = _; rw [p7]; exact hI.hin _ (by unfold IFix sw; omega)
  have c8 : c₁.nreg (RS + 8) = c₀.nreg (sw 10) := by
    rw [hc1]; show regB _ _ _ 241308 = _; rw [p8]; exact hI.hin _ (by unfold IFix sw; omega)
  have c9 : c₁.nreg (RS + 9) = 0 := by rw [hc1]; exact p9
  have cR : c₁.nreg eRD = 1 - c.nreg oD := by
    rw [hc1]; show regB c.nmem evPrepL c.nreg eRD = _; rw [pR, show c.nreg K1 = 1 from hK.2.1]
  have hhl : ShotList.holeList c₁ RS = [] := by
    unfold ShotList.holeList; rw [c9]; rfl
  have hori : OriginIn c₁ (RS + 3) (.sym s) := by
    show SymPtIn c₁ (RS + 3) s
    exact symPtIn_transport hs (by rw [hc1]; exact p3) (by rw [hc1]; exact p4)
      (by rw [hc1]; exact p5)
  -- 2. the precondition of the shot
  have hlow : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := hI₁.hm
  have hX1 : X.holds P c₁.nmem (c₁.nreg (RS + 8)) (c₁.nreg ALLOC) := by
    rw [c8]
    exact X.mono _ _ _ _ _ hI₁.hA (X.local_ _ _ _ _ _ (fun a ha => (hlow a ha).symm) hX)
  have hcap1 : c₁.nreg (RS + 7) ≤ X.cap P c₁.nmem (c₁.nreg (RS + 8)) := by
    rw [c7, c8, hXl P c₀.nmem c₁.nmem _ _ (fun a ha => hlow a ha) hX]; exact hcap
  have hreg := hctx.hostReg
  obtain ⟨-, -, -, ⟨H, hCD, -⟩, -, hWm⟩ := id hctx
  have hmD : ModelDescAt c₁.nmem (c₁.nreg RS) (Qof P) (chainModel J.left) := by
    rw [c0, hm1]; exact hmd
  have hRS1 : c₁.nreg RS + 1 = c.nreg CD₁ := by rw [c0, hcd]
  have pre : ShotList.ShotPre X Ok RS P W c₁ := by
    refine ⟨hG, hWh, hX1, hcap1, by rw [c0, hm1, hA1]; exact hmwf, by rw [c0, hm1]; exact hm0,
      by rw [c1', c2', hA1]; exact hAB, by rw [c9]; norm_num, H, J.left,
      by rw [hRS1, hm1]; exact hCD, by rw [hRS1, hm1]; exact hreg, hOk, hWm, fun j hj => ?_,
      fun j hj => by rw [c9] at hj; omega, .sym s, hori, hsl,
      Or.inr ⟨IOrc.innerPt_chain J.left ?_ ?_, fun x hx => by cases hx⟩, hay, ?_⟩
    · rw [c2'] at hj
      rw [c1', hm1, harcs j hj, c7]
      exact nArc_piece hP hNF hsg (hL _ (getD_mem_of_lt hj))
    · have hR : J.left.P = J.right.P := rfl
      rw [hR]; exact (J.right.abs_le_coordBound_of_mem_set haR).1
    · have hR : J.left.P = J.right.P := rfl
      rw [hR]; exact (J.right.abs_le_coordBound_of_mem_set haR).2
    · intro p t hp ht0 ht1 hpt
      exfalso
      have hM : WalkAx (chainModel J.left) := FactsChain.walkAx J.left hP
      apply hM.trace p hp t ht0 ht1
      show sidePt (chainModel J.left).W p t ∈ J.left.dom
      have : sidePt (chainModel J.left).W p t = Geometry.lerp ((chainModel J.left).wa p)
          ((chainModel J.left).wb p) t := rfl
      rw [this, hpt]; exact haD
  -- 3. the shot
  refine IRS.seq (K₂ := 49989 - 11 + 11)
    (shot_irs hsh hBs hXl hI₁ pre (by rw [c7, c2', hA1]; unfold evShotK at hroom; omega)) ?_
    |>.mono (by rw [c7, c2']) (fun _ h => h)
  rintro c₂ hI₂ - hAb ⟨hpost, k2, hA2, hm2⟩
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost (chainModel J.left) (.sym s) hmD hori
  rw [c6] at hyes hno
  have hev : Origin.eval (chainModel J.left) (Qof P) (Origin.sym s) = a := rfl
  rw [hev] at hyes hno
  rw [c1', c2', hhl, hm1] at hlo
  rw [c1', c2', hm1] at hhi
  have hAoff : A ⊆ J.left.domᶜ := by
    intro w hw
    have := hhi hw
    unfold ShotList.hiSet at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, -, hj⟩ := this
    exact Sweep.arcSet_subset_compl_dom J.left hP _ _ hj
  -- registers after the shot
  have keep2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ (RS ≤ r ∧ r < RS + 300) →
      c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => k2 r (not_oracle_sw h1 h2) (by unfold ALLOC; omega) h3
  have hA2' : c.nreg ALLOC ≤ c₂.nreg ALLOC := hA1 ▸ hA2
  have hm2' : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm2 a (by omega), hm1]
  have cd2 : c₂.nreg CD₁ = c.nreg CD₁ :=
    (keep2 _ (by unfold CD₁ sw; norm_num) (by unfold CD₁ sw; norm_num) (by unfold CD₁ RS sw; omega)).trans
      (q1 _ (by unfold CD₁ sw; omega) (by unfold CD₁ eRD sw; omega))
  have hctx2 : ChainCtx P W c₂ CD₁ J.left := hctx.transport cd2 hm2' hA2'
  have eR2 : c₂.nreg eRD = 1 - c.nreg oD :=
    (keep2 _ (by unfold eRD sw; norm_num) (by unfold eRD sw; norm_num) (by unfold eRD RS sw; omega)).trans cR
  -- the frame so far
  have fr2 : EFr ShW c c₂ := by
    refine ⟨fun r hr hX hra => ?_, hA2', hm2'⟩
    by_cases hsw : 240000 ≤ r ∧ r < 250000
    · rw [keep2 r hsw.1 hsw.2 (fun h => hX (Or.inl h))]
      exact q1 r (by
        by_contra h; push Not at h; exact hX (Or.inl ⟨by unfold RS; omega, by unfold RS; omega⟩))
        (fun h => hX (Or.inr ⟨by rw [h]; unfold eF eRD sw; omega, by rw [h]; unfold eNo eRD sw; omega⟩))
    · rw [k2 r hr hra (fun h => hsw ⟨by unfold RS at h; omega, by unfold RS at h; omega⟩)]
      exact q1 r (by omega) (fun h => hsw ⟨by unfold eRD sw at h; omega, by unfold eRD sw at h; omega⟩)
  -- 4. copy the flag
  have hok3 : okB W c₂.nmem [.copyN eF 241320] c₂.nreg :=
    ⟨iscr_sw (by unfold eF sw; norm_num) (by unfold eF sw; norm_num), trivial⟩
  refine IRS.seq (K₁ := 1) (K₂ := 49977) (IRS.block [.copyN eF 241320] hI₂ hok3) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₃ hI₃ - - hc3
  have v3 : c₃.nreg eF = c₂.nreg 241320 := by
    rw [hc3]; simp [regB, regI, eF, sw]
  have k3 : ∀ r, r ≠ eF → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [hc3]; simp only [regB, regI]; exact upd_other _ _ _ hr
  have hm3 : c₃.nmem = c₂.nmem := by rw [hc3]
  have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := k3 _ (by unfold eF ALLOC sw; omega)
  have fr3 : EFr ShW c c₃ := fr2.trans ⟨fun r _ hX _ => k3 r (fun h => hX (Or.inr ⟨by rw [h], by
      rw [h]; unfold eF eNo sw; omega⟩)), hA3.ge, fun a _ => by rw [hm3]⟩
  have hk0 : c₃.nreg K0 = 0 := (hK₀.fix hI₃).1
  -- the uniqueness of the hit parameter for genuine hits
  have huniq : ∀ t, FirstHit A a σ t → ∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) K [] →
      t = τ₀ := by
    intro t hFH τ₀ hg hτ₀
    obtain ⟨hfr, hhp⟩ := (genuine_iff J.left ha₁ hσ').1 hg
    rw [← hhp] at hτ₀ ⊢
    exact firstHit_exit J.left hσ' ha₁ hfr hAoff hFH (hlo hτ₀)
  have hcompl : ∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) K [] →
      c₂.nreg 241320 = 1 := by
    intro τ₀ hg hτ₀
    by_contra hne
    exact hno hne τ₀ hg.1 (hlo hτ₀)
  by_cases hf : c₃.nreg K0 < c₃.nreg eF
  · -- a hit
    rw [hk0, v3] at hf
    have hfl' : c₂.nreg 241320 ≤ 1 := hfl
    have h1 : c₂.nreg 241320 = 1 := by omega
    obtain ⟨t, hFH, hpp2, he2, hpos2⟩ := hyes h1
    have hpos2' : (chainModel J.left).pos (Qof P) ⟨c₂.nreg 241321, c₂.nreg 241322⟩ = rayPt a σ t :=
      hpos2
    have he2' : c₂.nreg 241321 < (chainModel J.left).W.n := he2
    have hpp2' : ProperPos (chainModel J.left) (Qof P) P.n ⟨c₂.nreg 241321, c₂.nreg 241322⟩ := hpp2
    have e3 : c₃.nreg 241321 = c₂.nreg 241321 := k3 _ (by unfold eF sw; omega)
    have h3' : c₃.nreg 241322 = c₂.nreg 241322 := k3 _ (by unfold eF sw; omega)
    have hctx3 : ChainCtx P W c₃ CD₁ J.left :=
      hctx2.transport (k3 _ (by unfold CD₁ eF sw; omega)) (fun a _ => by rw [hm3]) hA3.ge
    have eR3 : c₃.nreg eRD = 1 - c.nreg oD := (k3 _ (by unfold eRD eF sw; omega)).trans eR2
    have hK1 : evShotK (F (c₀.nreg (sw 5))) K = ShotList.shotCost (F (c₀.nreg (sw 5))) K + 50000 :=
      rfl
    rw [c7, c2', hA1] at hAb
    rw [hK1] at hroom
    generalize ShotList.shotCost (F (c₀.nreg (sw 5))) K = S at hAb hroom
    have hroom3 : c₃.nreg ALLOC + 35007 ≤ W := by rw [hA3]; omega
    refine IRS.mono (K := 49975 + 2) (IRS.ifT (by rw [hk0, v3]; exact hf) ?_) (by norm_num)
      (fun _ h => h)
    refine IRS.seq (K₁ := 35007) (K₂ := 14968) (callArr_irs (dsc := CD₁) (re := 241321) (rh := 241322)
      (rd := eRD) (o := eA) hI₃ hctx3
      ⟨by unfold CD₁ sw; norm_num, by unfold CD₁ sw; norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by unfold eRD sw; norm_num, by unfold eRD sw; norm_num⟩
      ⟨by unfold eA sw; norm_num, by unfold eA sw; norm_num⟩ (by rw [e3]; exact he2')
      (by rw [e3, h3']; exact hpp2') (by rw [e3, h3', hpos2']; exact hay) hroom3) ?_ |>.mono
      (by norm_num) (fun _ h => h)
    rintro c₄ hI₄ hA₄ hA₄' ⟨harr, k4, hal4, hm4⟩
    unfold ArrAt at harr
    rw [e3, h3', eR3, hpos2'] at harr
    rw [dirOf_rev hD] at harr
    have k4' : ∀ r, bandOf r ∉ oracleBands → (r < eA ∨ eA + 2 < r) → r ≠ ALLOC →
        c₄.nreg r = c₃.nreg r := fun r hr h hra => k4 r hr (by rcases h with h | h <;> omega)
          (by rcases h with h | h <;> omega) (by rcases h with h | h <;> omega) hra
    have fr4 : EFr ShW c c₄ := fr3.trans ⟨fun r hr hX hra => k4' r hr (by
      by_contra h; push Not at h; exact hX (Or.inr ⟨by unfold eF eA sw at *; omega,
        by unfold eA eNo sw at *; omega⟩)) hra, hal4, hm4⟩
    have eF4 : c₄.nreg eF = 1 := by
      rw [k4' eF (not_oracle_sw (by unfold eF sw; norm_num) (by unfold eF sw; norm_num))
        (by unfold eF eA sw; omega) (by unfold eF ALLOC sw; omega), v3, h1]
    obtain ⟨hfA, hA1', hA0⟩ := harr
    have hk04 : c₄.nreg K0 = 0 := (hK₀.fix hI₄).1
    by_cases ha4 : c₄.nreg K0 < c₄.nreg eA
    · -- normalise the arrival position
      rw [hk04] at ha4
      have hfa1 : c₄.nreg eA = 1 := by omega
      obtain ⟨hpe, hppA, hArr⟩ := hA1' hfa1
      have hctx4 : ChainCtx P W c₄ CD₁ J.left := hctx3.transport (k4' _
        (not_oracle_sw (by unfold CD₁ sw; norm_num) (by unfold CD₁ sw; norm_num))
        (by unfold CD₁ eA sw; omega) (by unfold CD₁ ALLOC sw; omega)) hm4 hal4
      refine (IRS.ifT (by rw [hk04]; exact ha4) (normS_irs (dsc := CD₁) (pe := eA + 1) (ph := eA + 2)
        (o := eNo) hI₄ (hK₀.fix hI₄) hctx4
        ⟨by unfold CD₁ sw; norm_num, by unfold CD₁ sw; norm_num, by unfold eA sw; norm_num,
          by unfold eA sw; norm_num, by unfold eA sw; norm_num, by unfold eA sw; norm_num⟩
        ⟨by unfold eNo sw; norm_num, by unfold eNo sw; norm_num, by unfold eNo eA sw; norm_num,
          by unfold eNo eA sw; norm_num, by unfold eNo eA sw; norm_num, by unfold eNo eA sw; norm_num,
          by norm_num⟩ hpe hppA (fun _ _ _ _ => by
            have e : (chainModel J.left).pos (Qof P) ⟨c₄.nreg (eA + 1), c₄.nreg (eA + 2)⟩ =
                sidePt (chainModel J.left).W (c₄.nreg (eA + 1))
                  ((chainModel J.left).param (Qof P) ⟨c₄.nreg (eA + 1), c₄.nreg (eA + 2)⟩) := rfl
            rw [e, hArr.2.2.2.1]; exact hay)
        (by rw [hA3] at hA₄'; omega))).mono
        (by norm_num) ?_
      rintro c₅ ⟨n1, n2, k5, hal5, hm5⟩
      have k5' : ∀ r, bandOf r ∉ oracleBands → r ≠ eA + 2 → r ≠ eNo → r ≠ eNo + 1 → r ≠ ALLOC →
          c₅.nreg r = c₄.nreg r := k5
      obtain ⟨hppN, hparN, hposN, hnz⟩ := nhgt_facts hppA
      have eA5 : c₅.nreg eA = 1 := by
        rw [k5' eA (not_oracle_sw (by unfold eA sw; norm_num) (by unfold eA sw; norm_num))
          (by unfold eA; omega) (by unfold eA eNo sw; omega) (by unfold eA eNo sw; omega)
          (by unfold eA ALLOC sw; omega), hfa1]
      have eF5 : c₅.nreg eF = 1 := by
        rw [k5' eF (not_oracle_sw (by unfold eF sw; norm_num) (by unfold eF sw; norm_num))
          (by unfold eF eA sw; omega) (by unfold eF eNo sw; omega) (by unfold eF eNo sw; omega)
          (by unfold eF ALLOC sw; omega), eF4]
      refine ⟨⟨by rw [eF5], fun _ _ _ => eF5, fun _ => ⟨t, hFH.1, huniq t hFH, by rw [eA5],
        fun _ => ?_, fun h => absurd eA5 h⟩⟩, fr4.trans ⟨fun r hr hX hra => k5' r hr ?_ ?_ ?_ hra,
          hal5, hm5⟩⟩
      · rw [n1, n2]
        refine ⟨hpe, hppN, ?_, hnz⟩
        rw [hparN]; exact hArr
      · intro h; exact hX (Or.inr ⟨by rw [h]; unfold eF eA sw; omega, by rw [h]; unfold eA eNo sw; omega⟩)
      · intro h; exact hX (Or.inr ⟨by rw [h]; unfold eF eNo sw; omega, by rw [h]; omega⟩)
      · intro h; exact hX (Or.inr ⟨by rw [h]; unfold eF eNo sw; omega, by rw [h]⟩)
    · refine (IRS.ifF ha4 (IRS.skip (K := 0) hI₄ rfl)).mono (by norm_num) ?_
      rintro c' rfl
      rw [hk04] at ha4
      have hfa : c₄.nreg eA ≠ 1 := by omega
      refine ⟨⟨by rw [eF4], fun _ _ _ => eF4, fun _ => ⟨t, hFH.1, huniq t hFH, hfA,
        fun h => absurd h hfa, fun _ => hA0 hfa⟩⟩, fr4⟩
  · -- no hit
    refine (IRS.ifF hf (IRS.skip (K := 0) hI₃ rfl)).mono (by norm_num) ?_
    rintro c' rfl
    rw [hk0, v3] at hf
    have h0 : c₂.nreg 241320 ≠ 1 := by omega
    refine ⟨⟨by rw [v3]; exact hfl, fun τ₀ hg hτ₀ => absurd (hcompl τ₀ hg hτ₀) h0,
      fun h => absurd (v3 ▸ h) h0⟩, fr3⟩

end

end SweepEv

end Chazelle.Core
