module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepIoGather
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.FuseAsmMain

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
structure EvEnv (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF) : Prop where
  hsh : ShooterOK sh Bs F X Ok
  hBs : Bs ⊆ oracleBands
  hXl : X.CapLocal
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hP : J.P.Simple
  hX : X.holds P c₀.nmem ztxj ztdq
  hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj
  hOk₁ : Ok P ztbw
  hNF₁ : IsNF ztbw zta N₁
  hsg₁ : (chainModel J.left).Semigranular ztwjx ztq
  hNW₁ : NFWithin c₀.nmem ztxnx ztdq N₁
  hNF₂ : IsNF ztj zta N₂
  hNW₂ : NFWithin c₀.nmem ztyja ztdq N₂
  hmd : ModelDescAt c₀.nmem ztmhy zta ztbw
  hmwf : ModelDescWF P ztdq c₀.nmem ztmhy
  hm0 : c₀.nmem ztmhy = 0
  hcd : c₀.nreg CD₁ = c₀.nreg MD₁ + 1
  ctx1 : ChainCtx P W c₀ CD₁ J.left
  ctx2 : ChainCtx P W c₀ zted J.right
  ctxW : ChainCtx P W c₀ ztjl J.whole
  hK : Consts c₀
  hO : OrgK P J c₀
  hM : MapK J c₀
  hgw : c₀.nreg cGW = gW J
  hT : c₀.nreg ALLOC ≤ c₀.nreg cTB
  hTW : c₀.nreg cTB + 6 * N₂.nChords + 2 ≤ W
  hWn : 2 * (chainModel J.whole).W.n ≤ W
  hst : ∃ H, JunctionAt c₀.nmem ztbaha ztbahb ztbahd zta H J ∧
    St0S P c₀ H J
  hJWF : JunctionWF P ztdq c₀.nmem ztbaha ztbahb ztbahd
  hOk₂ : Ok P ztj
  hsg₂ : (chainModel J.right).Semigranular ztwis ztq
  hdeg₁ : (chainModel J.left).DegLe ztwjx zto
  hdeg₂ : (chainModel J.right).DegLe ztwis zto
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem zthwa = 2 ^ j
  hbig₁ : N₁.arcs.length < 2 ^ c₀.nreg TLR
  hbig₂ : N₂.arcs.length < 2 ^ c₀.nreg TLR
  hTBR : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC
  hNT₁ : NFWithin c₀.nmem ztxnx ztbmp N₁
  hNT₂ : NFWithin c₀.nmem ztyja ztbmp N₂
  hTLR : c₀.nreg TLR ≤ Nat.clog 2 ztks + 3
  hTA : c₀.nreg cTB = c₀.nreg ALLOC
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
namespace EvEnv
variable (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
include E hI
theorem md : ModelDescAt c.nmem zthvf zta ztbw ∧
    ModelDescWF P ztm c.nmem zthvf ∧ c.nmem zthvf = 0 ∧
    c.nreg CD₁ = c.nreg MD₁ + 1 := by
  have eMD : c.nreg MD₁ = c₀.nreg MD₁ := hI.hin _ by_trivial
  have eCD : c.nreg CD₁ = c₀.nreg CD₁ := hI.hin _ by_trivial
  rcases E.hmd with ⟨-, H, C', hC', hMC⟩ | ⟨h1, -⟩
  swap
  · have := E.hm0; omega
  obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep E.hmwf E.hm0 hC' zttj hI.hA
  rw [eMD, eCD]
  exact ⟨Or.inl ztfwz, w1, w2, E.hcd⟩
theorem ctx1' : ChainCtx P W c CD₁ J.left :=
  E.ctx1.transport ztdhk zttj hI.hA
theorem ctx2' : ChainCtx P W c zted J.right :=
  E.ctx2.transport ztdhk zttj hI.hA
theorem ctxW' : ChainCtx P W c ztjl J.whole :=
  E.ctxW.transport ztdhk zttj hI.hA
theorem gw' : c.nreg cGW = gW J := (hI.hin _ by_trivial).trans E.hgw
omit E hI in
theorem tb' (_E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂)
    (hI : IInv W c₀ c) : c.nreg cTB = c₀.nreg cTB := hI.hin _ by_trivial
theorem nw₂' : NFWithin c.nmem ztwrb ztm N₂ := by
  zubuy
  exact (E.hNW₂.transport zttj).mono hI.hA
end EvEnv
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def CandComp (P : Polygon) (J : Merge.Junction) (S₂ : Set ztf) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (lo : Set Point) (c c' : Config) : Prop :=
  ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W ztxc p t →
    sidePt (chainModel J.whole).W p t = rayPt a σ zton →
    (Lst J : ℝ) < oW J ztk → sidePt (chainModel J.whole).W p t ≠ J.shared →
    J.whole.hitParam a σ < J.right.hitParam a σ → rayPt a σ zton ∈ lo →
    ∃ h, (chainModel J.whole).param zta ztnk = t ∧ AccAt P J S₂ T j u d a σ c c' p h

/-- The cost of a candidate. -/
def evCandK (Fg K KG : ℕ) : ℕ := evShotK Fg K + KG + 56500

/-- The preparation of completeness: the genuine hit, its arrival and its offset. -/
theorem cand_prep {J : Merge.Junction} (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {ch : Set Point} (hch : ch ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztmpq ∨ ztlus) (haR : a ∈ J.right.set)
    (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {p : ℕ} {t : ℝ}
    (h1 : SideAttach (chainModel J.whole).W ztxc p t)
    (h2 : sidePt (chainModel J.whole).W p t = rayPt a σ zton)
    (h3 : (Lst J : ℝ) < oW J ztk) (h4 : sidePt (chainModel J.whole).W p t ≠ J.shared)
    (h5 : J.whole.hitParam a σ < J.right.hitParam a σ) :
    Genuine J.left a σ zton ∧
      J.whole.hitParam a σ < (Merge.rend ch).1 - (Merge.lend ch).1 ∧
      ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Arrival (chainModel J.left).W ztwqt σ
          ztwjw t := by
  zune
  obtain ⟨hfr, -, -, hR, -, -⟩ := right_hit_end ztvub ha
  zuhyp
  obtain ⟨hg, d, hd⟩ := map_complete hP ha₁ hσ hfree h1 h2 h3 h4
  grind
theorem mod_back {n b d : ℕ} (hb : b < n) (hd : d < n) : (zthdo % n + n - b) % n = d := by
  rcases Nat.lt_or_ge zthdo n with h | h
  · rw [Nat.mod_eq_of_lt h, show b + d + n - b = d + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hd]
  · have e : zthdo % n = b + d - n := by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt by_omega]
    rw [e, show b + d - n + n - b = d by omega, Nat.mod_eq_of_lt hd]

/-- Same key and best candidate. -/
def SameKB (c c' : Config) : Prop :=
  c'.nreg kE = c.nreg kE ∧ c'.nreg kH = c.nreg kH ∧ ∀ r, BestR r → c'.nreg r = c.nreg r
theorem bestSame_lift {c c₃ c' : Config} (hs : SameKB c c₃) (h : BestSame c₃ c') : BestSame c c' :=
  ⟨h.1.trans (hs.2.2 _ ztp), h.2.1.trans (hs.2.2 _ ztwiz),
    h.2.2.1.trans (hs.2.2 _ ztbh),
    h.2.2.2.1.trans (lblOf_congr (fun q hq => hs.2.2 q ztcgy)),
    h.2.2.2.2.trans (hs.2.2 _ ztbaje)⟩
theorem offerRel_lift {P : Polygon} {J : Merge.Junction} {c c₃ c' : Config} {e h u d : ℕ}
    (hs : SameKB c c₃) (hO : OfferRel P J c₃ c' e h u d) : OfferRel P J c c' e h u d := by
  obtain ⟨eKE, eKH, hB⟩ := hs
  have eBF := hB _ ztp
  have eBE := hB _ ztwiz
  have eBH := hB _ ztbajm
  have eLb :=
    lblOf_congr (fun q hq => hB q ztcgy)
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hO
  rw [eKE, eKH] at o3 o4 o5 o6
  rw [eBF, eBE, eBH] at o4 o5 o6
  rw [eLb] at o5
  exact ⟨o1, o2, fun h' => bestSame_lift ztrch (o3 h'), o4,
    o5,
    fun h1 h2 h3 => bestSame_lift ztrch by_simp_all⟩
theorem tabUpd_congr {m m' : ℕ → ℕ} {T j e h x : ℕ}
    (hm : x ≠ T + 3 * j → x ≠ T + 3 * j + 1 → x ≠ T + 3 * j + 2 → m' x = m x) :
    tabUpd m' T j e h x = tabUpd m T j e h x := by
  unfold tabUpd upd
  simp_all
theorem accAt_lift {P : Polygon} {J : Merge.Junction} {S₂ : Set ztf} {T j u d : ℕ}
    {a : Point} {σ : ℝ} {c c₃ c' : Config} {e h : ℕ} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (hacc : AccAt P J S₂ T j u d a σ c₃ c' e h) : AccAt P J S₂ T j u d a σ c c' e h :=
  ⟨hacc.1, fun x hx => by
    rw [hacc.2.1 x by_omega]
    exact tabUpd_congr by_simp_all, offerRel_lift hs hacc.2.2⟩
theorem rejAt_lift {c c₃ c' : Config} (hs : SameKB c c₃) (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC)
    (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x) (hr : RejAt c₃ c') : RejAt c c' :=
  ⟨fun x hx => (hr.1 x by_omega).trans by_simp_all, bestSame_lift hs hr.2⟩
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **One candidate.** -/
theorem evCand_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {L : List ℕ} (hL : ∀ a ∈ L, a < N₁.arcs.length)
    (hgK : c.nreg wGK = L.length) (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem ztdcv k =
      nArc ztbw zta N₁ zthbf)
    {ch : Set Point} (hch : ch ∈ N₂.F ztj zta) {a : Point}
    (hD : c.nreg oD ≤ 1)
    (ha : (dirOf ztjsk = 1 ∧ a = Merge.lend ch) ∨ (dirOf ztjsk = -1 ∧ a = Merge.rend ch))
    {s : SymPt} (hsym : SymPtIn c oSym s) (hsl : s.Lt P.n) (hse : s.eval zta = a)
    (habs : AbsRec P c oAbsA a.1 J.left.radius) (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (ha₁ : a.2 ≤ J.left.top.2)
    (hfe : c.nreg oFE < (chainModel J.right).W.n)
    (hfp : ProperPos ztj zta P.n ztdqn)
    (hfar : (chainModel J.right).pos zta ztdqn =
      if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch)
    (hj : 2 * c.nreg oK + c.nreg oS < 2 * N₂.nChords)
    (hk : PosW P J ztwe ztbhr) (hb : c.nreg bF = 1 → PosW P J ztvo ztvp)
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4)
    (hroom : c.nreg ALLOC + evCandK ztwiu L.length KG ≤ W) :
    IRS P W c₀ zttjw c (evCandK ztwiu L.length KG) (fun c' =>
      CandRes P J ztwis ztdmu ztqs
        zthvl zthvk a ztzel c c' ∧
      CandComp P J ztwis ztdmu ztqs
        zthvl zthvk a ztzel
        ztxgl c c' ∧
      ztbid ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  zubns
  have hS₂ : ztrfs := E.hNF₂.1.2.1
  have hS₂f : ztrfe := E.hNF₂.1.1
  zueef
  zujnd
  zune
  obtain ⟨hmd, hmwf, hm0, hcd⟩ := E.md hI
  subst hse
  set lo := ShotList.loSet _ _ c.nmem _ L.length [] with hlo
  -- the rejection
  have rejQ : ∀ c' : Config,
      ztbid →
      c.nreg ALLOC ≤ c'.nreg ALLOC → ztbgf →
      (∀ r, BestR r → c'.nreg r = c.nreg r) →
      (∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W (Merge.shoot J.whole ztwpu σ) p t →
        sidePt (chainModel J.whole).W p t =
          rayPt ztwpu σ ztbarf →
        (Lst J : ℝ) < oW J ztk → sidePt (chainModel J.whole).W p t ≠ J.shared →
        J.whole.hitParam ztwpu σ < J.right.hitParam ztwpu σ →
        rayPt ztwpu σ ztbarf ∈ lo → False) →
      CandRes P J S₂ ztdmu ztqs zthvl zthvk
        ztwpu σ c c' ∧
      CandComp P J S₂ ztdmu ztqs zthvl zthvk
        ztwpu σ lo c c' ∧
      ztbid ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC := by
    intro c' hr hA hm hB hno
    refine ⟨Or.inl ⟨hm, hB _ ztp, hB _ ztwiz, hB _ ztbh,
      lblOf_congr (fun q hq => hB q ztbmd),
      hB _ ztbaje⟩, fun p t h1 h2 h3 h4 h5 h6 =>
        by grind, hr, hA⟩
  -- 1. the shot
  have hroom1 : c.nreg ALLOC + evShotK ztwiu L.length ≤ W := by
    unfold evCandK at hroom; omega
  refine IRS.mono
    (IRS.seq (K₂ := KG + 56500)
    (evShot_irs E.hsh E.hBs E.hXl hI E.hK E.hG E.hWh hP E.hX E.hcap E.hOk₁ E.hNF₁ E.hsg₁ hmd hmwf
      hm0 ztuxt hcd hL hgK hAB harcs hsym hsl haR hav ha₁ hD hroom1) ?_)
    (by unfold evCandK; omega) ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨f1, f2, f3⟩, fr1⟩
  have k01 := (E.hK.fix hI₁).1
  have keep1 :=
    fun r h1 h2 h3 => fr1.1 r ztsg h3 ztu
  have nShW : ∀ r, ShW r → CandR r := fun r hr => by
    unfold ShW RS eF eNo sw at hr; unfold CandR sw; omega
  have best1 : ztflf := fun r hr => keep1 r
    ztsx
    ztsx
    (by unfold BestR LblR bF bE bH bN bL sw at hr; unfold ShW RS eF eNo sw; omega)
  have frR1 : ∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r hr h1 h2 => fr1.1 r hr by_grind h2
  -- the completeness data
  have prep := fun (p : ℕ) (t : ℝ) h1 h2 h3 h4 h5 =>
    cand_prep hP hS₂ hch ha haR hav ha₁ (p := p) (t := t) h1 h2 h3 h4 h5
  by_cases hF : c₁.nreg K0 < c₁.nreg eF
  · zukwt
    have hF1 : c₁.nreg eF = 1 := by_omega
    obtain ⟨τ, hτ, huq, hAle, hA1, hA0⟩ := f3 hF1
    refine IRS.mono (K := KG + 56498 + 2) ztdfp by_omega
      ztb
    by_cases hAr : c₁.nreg K0 < c₁.nreg eA
    · zukws
      have hA11 : c₁.nreg eA = 1 := by_omega
      obtain ⟨hpe, hppA, hArr, hnorm⟩ := hA1 hA11
      refine IRS.mono (K := KG + 56496 + 2) ztdfp by_omega
        ztb
      -- 2. the genuineness check
      have eD1 : c₁.nreg oD = c.nreg oD := keep1 _ by_decide by_decide
        (by unfold ShW RS oD eF eNo sw; omega)
      have habs1 : AbsRec P c₁ oAbsA (s.eval _).1 J.left.radius := ShotList.absRec_copy habs
        (keep1 _ by_decide by_decide
          ztdcn)
        (keep1 _ by_decide by_decide
          ztdcn)
        (keep1 _ by_decide by_decide
          ztdcn)
        (keep1 _ by_decide by_decide
          ztdcn)
      have hroomG : c₁.nreg ALLOC + KG ≤ W := by unfold evCandK at hroom; omega
      refine IRS.seq (hgen c₁ _ σ τ hI₁ hroomG
        by_omega (by rw [eD1]) habs1 haR hav ha₁ hτ hpe hppA hArr) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨hbG, frG⟩
      have k02 := (E.hK.fix hI₂).1
      have keep2 :=
        fun r h1 h2 h3 h4 => (frG.1 r ztsg h4 ztu).trans
          (keep1 r h1 h2 h3)
      have keep2' : ∀ r, ztltr ∨ ztlts →
          c₂.nreg r = c.nreg r := fun r hr => keep2 r ztcmp
        ztcmp (by unfold ShW RS eF eNo sw at *; omega)
        (by unfold GR cG sw at *; omega)
      have keepA2 : ∀ r, eA ≤ r → r ≤ eA + 2 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
        frG.1 r ztfch
          (by unfold GR cG eA sw at *; omega) (by unfold eA ALLOC sw at *; omega)
      have nGR : ∀ r, GR r → CandR r := fun r hr => by unfold GR cG sw at hr; unfold CandR sw; omega
      have frR2 :=
        fun r hr h1 h2 => (frG.1 r hr (fun h => h1 (nGR r h)) h2).trans (frR1 r hr h1 h2)
      have best2 : ztflg := fun r hr => by
        rw [← best1 r hr]
        exact frG.1 r (not_oracle_sw ztsx
          ztsx)
          (by unfold BestR LblR bF bE bH bN bL at hr; unfold GR cG sw at *; omega)
          zthfl
      have hA2c := hA₁.trans frG.2.1
      have hm2c := fun x hx =>
        (frG.2.2 x by_omega).trans (fr1.2.2 x hx)
      by_cases hGb : c₂.nreg K0 < c₂.nreg cG
      · zukwx
        have hgen1 : Genuine J.left _ σ τ := hbG.2.1 (by have := hbG.1; omega)
        refine IRS.mono (K := 56494 + 2) ztdfp by_omega ztb
        -- 3. the far-end test
        have eE1 := keepA2 ztle by_omega by_omega
        have eE2 := keepA2 zthq by_omega by_omega
        have eFE : c₂.nreg oFE = c.nreg oFE := keep2' _ (Or.inl ⟨by_decide,
          by decide⟩)
        have eFC : c₂.nreg oFC = c.nreg oFC := keep2' _ (Or.inl ⟨by_decide,
          by decide⟩)
        have eD2 : ztshk := keep2' _ (Or.inl ⟨by_decide,
          by decide⟩)
        have hw : (chainModel J.left).pos _ ⟨c₁.nreg _, c₁.nreg _⟩ =
            rayPt _ σ τ := hArr.2.2.2.1
        have hy1 : |((chainModel J.left).pos zta ⟨c₁.nreg ztle, c₁.nreg zthq⟩).2| <
            J.left.radius := by
          rw [hw, Visibility.rayPt_snd]
          zukad
          zummt
          exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2
            J.right.coordBound_lt_radius
        have hy2 : |((chainModel J.right).pos zta ⟨c.nreg oFE, c.nreg oFC⟩).2| <
            J.right.radius := by
          rw [hfar]
          obtain ⟨-, -, -, -, hl2, hr2⟩ := right_hit_end ztvub ha
          split_ifs <;> [rw [hr2]; zuowz] <;>
          exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2
            J.right.coordBound_lt_radius
        have hroomF : c₂.nreg ALLOC + 34000 ≤ W := by
          have := frG.2.1; unfold evCandK at hroom; omega
        refine IRS.seq (K₂ := 22494) (farChk_irs hI₂ E.hK ztuxu ztmas
          by_omega ztlgy ztlgy
          by_omega ztfpj ztfpj
          by_omega hroomF) ?_
        rintro c₃ hI₃ hA₃ hA₃' ⟨hbF', frF⟩
        rw [eE1, eE2, eFE, eFC, eD2, hw, hfar] at hbF'
        -- the bit is the far-end condition
        have hfarIff : (if c.nreg oD = 1 then (rayPt ztwpu σ τ).1 <
              (if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch).1
            else (if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch).1 <
              (rayPt ztwpu σ τ).1) ↔ τ < (Merge.rend ch).1 - (Merge.lend ch).1 := by
          rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hd1 : ztuor := by
              by_contra h; rw [hσd] at h1; unfold dirOf at h1; zvnoi at h1; norm_num at h1
            rw [ite_eq_left hd1, ite_eq_left hd1, Visibility.rayPt_fst, h1, h2]
            zufry
          · have hd1 : ztuos := by
              intro h; rw [hσd] at h1; unfold dirOf at h1; zvnbq at h1; norm_num at h1
            rw [ite_eq_right hd1, ite_eq_right hd1, Visibility.rayPt_fst, h1, h2]
            zufry
        have hbFr := hbF'.congr hfarIff
        have k03 := (E.hK.fix hI₃).1
        have keep3 := fun r h1 h2 h3 => frF.1 r h2 h1 h3
        have nF : ∀ r, cAW ≤ r ∧ r ≤ cFr → CandR r := fun r hr => by
          unfold cAW cFr sw at hr; unfold CandR sw; omega
        have frR3 :=
          fun r hr h1 h2 => (keep3 r (fun h => h1 (nF r h)) hr h2).trans (frR2 r hr h1 h2)
        have best3 : ztflh := fun r hr => by
          rw [← best2 r hr]
          exact keep3 r (by unfold BestR LblR bF bE bH bN bL at hr; unfold cAW cFr sw at *; omega)
            (not_oracle_sw ztsx
              ztsx)
            zthfl
        have hA3c := hA2c.trans frF.2.1
        have hm3c := fun x hx =>
          (frF.2.2 x by_omega).trans (hm2c x hx)
        by_cases hFr : c₃.nreg K0 < c₃.nreg cFr
        · zukwy
          have hlt := hbFr.2.1 (by have := hbFr.1; omega)
          refine IRS.mono (K := 22300 + 2) ztdfp by_omega
            ztb
          -- 4. the accepting tail
          have kc3 : ∀ r, ztltr ∨ ztlts →
              c₃.nreg r = c.nreg r := fun r hr => by
            rw [keep3 r (by unfold cAW cFr sw at *; omega)
              ztzxh
              ztum]
            exact keep2' r hr
          have kA3 : ∀ r, eA ≤ r → r ≤ eA + 2 → c₃.nreg r = c₁.nreg r := fun r h1 h2 => by
            rw [keep3 r (by unfold cAW cFr eA sw at *; omega)
              ztfch
              (by unfold ALLOC eA sw at *; omega)]
            exact keepA2 r h1 h2
          have e31 := kA3 ztle by_omega by_omega
          have e32 := kA3 zthq by_omega by_omega
          have hs3 : SameKB c c₃ := ⟨kc3 _ ztxcg,
            kc3 _ ztxcg, best3⟩
          have eK3 : c₃.nreg oK = c.nreg oK := kc3 _ ztihm
          have eS3 : c₃.nreg oS = c.nreg oS := kc3 _ ztwos
          have eU3 : ztshq := kc3 _ ztwos
          have eN3 : ztmvi := kc3 _ ztwos
          have eT3 := (E.tb' hI₃).trans (E.tb' hI).symm
          have hTW3 : c₃.nreg cTB + 3 * (2 * c₃.nreg oK + c₃.nreg oS) + 2 ≤ W := by
            rw [E.tb' hI₃, eK3, eS3]; have := E.hTW; omega
          have hroomA : c₃.nreg ALLOC + 22300 ≤ W := by
            have := frF.2.1; have := frG.2.1; unfold evCandK at hroom; omega
          refine (evAccT_irs hI₃ E.hK E.hM hP hS₂ hS₂f hch ha haR hav ha₁ hgen1 hlt
            by_omega ztfpi ztfpi
            ztfpi E.ctxW E.hgw (by rw [hs3.1, hs3.2.1]; exact hk)
            (by rw [hs3.2.2 _ ztp, hs3.2.2 _ ztwiz,
              hs3.2.2 _ ztbh]; exact hb)
            (by rw [hs3.2.2 _ ztp]; omega)
            (by rw [hs3.2.2 _ ztbaje]; omega)
            (by rw [E.tb' hI₃]; exact E.hT) hTW3 E.hWn hroomA).mono le_rfl ?_
          rintro c' ⟨hacc, hrej, hfr4, hA4⟩
          rw [e31, e32, eT3, eK3, eS3, eU3, eN3] at hacc
          rw [e31, e32] at hrej
          refine ⟨?_, ?_, fun r hr h1 h2 => (hfr4 r hr h1 h2).trans (frR3 r hr h1 h2), hA3c.trans hA4⟩
          · by_cases hMV : SweepEv.MVal J (ztwzs %
                (chainModel J.left).W.n) (c₁.nreg (eA + 2))
            · exact Or.inr ⟨_, _, accAt_lift hs3 hA3c hm3c ztvuk⟩
            · exact Or.inl (rejAt_lift hs3 hA3c hm3c (hrej hMV))
          · zubdv
            obtain ⟨hg, -, d₀, hv₀, hpd, harr₀⟩ := prep p t h1 h2 h3 h4 h5
            have hτT := huq _ hg h6
            subst hτT
            have ha₁' : (s.eval _).2 ≤ J.left.top.2 := ha₁
            obtain ⟨hpq, htq⟩ := arrival_unique hP ha₁' hσ hg hArr harr₀
            have hd₀ := lt_of_lt_of_le hv₀.1 ztjip
            have hdd : ztwzs %
                (chainModel J.left).W.n = d₀ := by
              zumoa
              exact mod_back (b₁_lt) hd₀
            have hMV : SweepEv.MVal J (ztwzs %
                (chainModel J.left).W.n) (c₁.nreg (eA + 2)) := by
              rw [hdd]
              refine ⟨hv₀.1, hv₀.2.1, fun h => hv₀.2.2.1 ⟨h.1, h.2.1, fun ht0 => h.2.2 ?_⟩⟩
              exact hnorm.2 (by rw [htq]; omega)
            have hacc' := accAt_lift hs3 hA3c hm3c ztvuk
            rw [hdd, hpd] at hacc'
            refine ⟨_, ?_, hacc'⟩
            zunw
            obtain ⟨-, hmem, hS, hpt, -⟩ := hacc'.1
            exact (hM.attach_unique (F₂plus_subset J hS₂ hmem) hS h1 (by rw [hpt, h2])).2
        · zukwy
          have hnlt : ¬ τ < (Merge.rend ch).1 - (Merge.lend ch).1 := fun h => by
            have := hbFr.2.2 h; omega
          refine IRS.mono (K := 0 + 2) (IRS.ifF by_omega zthau) by_omega ?_
          zuu
          refine rejQ c₃ frR3 hA3c hm3c best3 ?_
          zubdv
          obtain ⟨hg, hlt', -⟩ := prep p t h1 h2 h3 h4 h5
          have := huq _ hg h6
          zumo
          tauto
      · zukwx
        have hng : ¬ Genuine J.left _ σ τ := fun h => by have := hbG.2.2 h; omega
        refine IRS.mono (K := 0 + 2) (IRS.ifF by_omega (IRS.skip hI₂ rfl)) by_omega ?_
        zuu
        refine rejQ c₂ frR2 hA2c hm2c best2 ?_
        zubdv
        zueay
        have := huq _ hg h6
        zumo
        tauto
    · zukws
      have hA0' : c₁.nreg eA ≠ 1 := by_omega
      zuflr
      zuu
      zuiey
      zubdv
      obtain ⟨hg, -, d, -, -, harr⟩ := prep p t h1 h2 h3 h4 h5
      have := huq _ hg h6
      zumo
      exact hA0 hA0' _ _ harr
  · zukwt
    have hF0 : c₁.nreg eF ≠ 1 := by_omega
    zuflr
    zuu
    zuiey
    zubdv
    zueay
    exact hF0 (f2 _ hg h6)
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def orgDo (sh g : Stmt) : Stmt :=
  .seq orgHead (.seq orgCls (.ifLtN oCl K1 .skip (.ifLtN K1 oCl .skip
    (.seq (callAbs zted oE oC oAbsA) zttjw))))

/-- The cost of one origin. -/
def orgDoK (Fg K KG : ℕ) : ℕ := evCandK Fg K KG + 60000

/-- The registers an origin may write. -/
def OrgR (r : ℕ) : Prop := CandR r ∨ (sw 2202 ≤ r ∧ r ≤ sw 2232)
theorem loSet_congr {M : Model} {Q : Polygon} {m m' : ℕ → ℕ} {A K : ℕ}
    {hs : List ztqx} (h : ∀ x, A ≤ x → x < A + 4 * K → m' x = m x) :
    ShotList.loSet M Q m' A K hs = ShotList.loSet M Q m A K hs := by
  have ha : ∀ j, j < K → ShotList.arcAt m' A j = ShotList.arcAt m A j := fun j hj => by
    unfold ShotList.arcAt
    grind
  zumx
  unfold ShotList.loSet
  grind
theorem candComp_lift {P : Polygon} {J : Merge.Junction} {S₂ : Set ztf} {T j u d : ℕ}
    {a : Point} {σ : ℝ} {lo : Set Point} {c c₃ c' : Config} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (h : CandComp P J S₂ T j u d a σ lo c₃ c') : CandComp P J S₂ T j u d a σ lo c c' :=
  fun p t h1 h2 h3 h4 h5 h6 => by
    obtain ⟨hh, e1, e2⟩ := h p t h1 h2 h3 h4 h5 h6
    exact ⟨hh, e1, accAt_lift hs hA hm e2⟩
theorem candRes_lift {P : Polygon} {J : Merge.Junction} {S₂ : Set ztf} {T j u d : ℕ}
    {a : Point} {σ : ℝ} {c c₃ c' : Config} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (h : CandRes P J S₂ T j u d a σ c₃ c') : CandRes P J S₂ T j u d a σ c c' := by
  rcases h with h | ⟨e, hh, h⟩
  · exact Or.inl (rejAt_lift hs hA hm h)
  · exact Or.inr ⟨e, hh, accAt_lift hs hA hm h⟩

/-- The ends of a chord record are positions of the walk proper. -/
theorem end_facts {P : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hNF : IsNF ztj zta N₂) {k : ℕ} (hk : k < N₂.nChords) (s : ℕ) :
    (endPos N₂ k s).edge < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztlnp ∧
      (farEnd N₂ k s).edge < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztrpl := by
  zuftg
  zugmi
  zuc
  have hpl : ztmts :=
    ⟨hA.1.2.1, hA.1.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; omega⟩
  have hpr : ztmtt :=
    ⟨hA.2.2.1, hA.2.2.2.1, by show (N₂.chord k).h + 1 ≤ P.n; omega⟩
  unfold endPos farEnd
  split_ifs
  · exact ⟨hA.1.1, hpl, hA.2.1, hpr⟩
  · exact ⟨hA.2.1, hpr, hA.1.1, hpl⟩

/-- The origin and the direction of the end `s` of chord `k`. -/
theorem endOrigin_ks {Q : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hNF : IsNF ztj Q N₂) {k s : ℕ} (hk : k < N₂.nChords) (hs : s ≤ 1) :
    endOrigin J Q N₂ ztci = (chainModel J.right).pos Q ztlnp ∧
      endDir ztci = dirOf zteaf ∧
      ((dirOf zteaf = 1 ∧
          endOrigin J Q N₂ ztci = Merge.lend ztwyt) ∨
        (dirOf zteaf = -1 ∧
          endOrigin J Q N₂ ztci = Merge.rend ztwyt)) ∧
      (chainModel J.right).pos Q ztrpl =
        (if zteaf = 1 then Merge.rend ztwyt
          else Merge.lend ztwyt) := by
  have hj : 2 * k + s < 2 * N₂.nChords := by_omega
  have h2 : ztzra := by_omega
  have h3 : ztci % 2 = s := by_omega
  obtain ⟨hO, -⟩ := endOrigin_eq J hNF hj
  have hF := farOrigin_eq J hNF hj
  rw [h2, h3] at hO hF
  refine ⟨hO, ?_, ?_, ?_⟩
  · unfold endDir dirOf; grind
  · unfold endOrigin; rw [h3, h2]
    zuox
    · tauto
    · right; tauto
  simp_all

/-- **An origin above the top of `C₁`** has its first hit in `C` on `C₂`. -/
theorem high_no_hit {J : Merge.Junction} {a : Point} (haR : a ∈ J.right.set) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hhigh : ¬ a.2 ≤ J.left.top.2) :
    ¬ J.whole.hitParam a σ < J.right.hitParam a σ := by
  have ha₂ := J.right.snd_le_top_of_mem_set haR
  have hbox : J.right.hitParam a σ ≤ Merge.rayHit J.whole.radius ∅ a σ := by
    unfold Merge.rayHit
    refine le_csInf ztqag fun t ht => ?_
    obtain ⟨ht0, hout⟩ := ht
    refine J.right.hitParam_le_of_not_mem_dom a σ ht0 fun hd => ?_
    rcases hout with h | h
    · exact h (J.right.dom_subset_box hd)
    simp_all
  rw [whole_hit_right ha₂ hσ by_simp_all hbox]
  simp
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **One origin.** -/
theorem orgDo_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {L : List ℕ} (hL : ∀ a ∈ L, a < N₁.arcs.length)
    (hgK : c.nreg wGK = L.length) (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem ztdcv k =
      nArc ztbw zta N₁ zthbf)
    {k s : ℕ} (hkd : c.nreg oK = k) (hsd : c.nreg oS = s) (hk : k < N₂.nChords) (hs : s ≤ 1)
    (hkey : PosW P J ztwe ztbhr)
    (hb : c.nreg bF = 1 → PosW P J ztvo ztvp)
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4)
    (hroom : c.nreg ALLOC + orgDoK ztwiu L.length KG ≤ W) :
    IRS P W c₀ ztkbr c ztbaqh (fun c' =>
      CandRes P J ztwis ztdmu ztci
        (N₂.chord k).up (N₂.chord k).dn
        ztwut ztxnz c c' ∧
      (endOrigin J zta N₂ ztci ∈ J.right.set →
        endOrigin J zta N₂ ztci ≠ J.shared →
        endOrigin J zta N₂ ztci ≠ J.right.top →
        CandComp P J ztwis ztdmu ztci
          (N₂.chord k).up (N₂.chord k).dn
          ztwut ztxnz
          ztxgl c c') ∧
      (¬ (endOrigin J zta N₂ ztci ∈ J.right.set ∧
        endOrigin J zta N₂ ztci ≠ J.shared ∧
        endOrigin J zta N₂ ztci ≠ J.right.top) → RejAt c c') ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  zueqn
  obtain ⟨hEe, hEp, hFe, hFp⟩ := end_facts hNF hk s
  obtain ⟨hband, -⟩ := endPos_band hNF hk s
  obtain ⟨hO, hDir, hLR, hFar⟩ := endOrigin_ks hNF hk hs
  have hσ : endDir ztci = 1 ∨ endDir ztci = -1 := by
    grind
  -- 1. the head
  refine IRS.mono
    (IRS.seq (K₂ := 31410 + (4 + (16707 + evCandK ztwiu L.length KG)))
      (orgHead_irs hI E.hK ztpxh hNF (E.nw₂' hI) le_rfl by_omega
        by_omega zteqq) ?_)
    (by unfold orgDoK; omega) ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨-, vUp, vDn, vD, vE, vC, vFE, vFC, fr₁, -, hm₁⟩
  simp only [hkd, hsd] at vUp vDn vD vE vC vFE vFC
  obtain ⟨hpp', -, hpos', hnorm'⟩ := nhgt_facts hEp
  have hE1 : c₁.nreg oE < 2 * J.right.m + 7 := by zuogo; have := cm_n J.right; omega
  have hpp1 : ProperPos ztj zta P.n ztkki := by
    simp_all
  have hnorm1 : c₁.nreg oC = 0 ↔
      (chainModel J.right).param zta ztkki = 0 := by
    simp_all
  have hpos1 : (chainModel J.right).pos zta ztkki =
      endOrigin J zta N₂ ztci := by
    simp_all
  -- 2. the class
  refine IRS.seq
    (orgCls_irs hI₁ E.hK E.hO ztuxv hE1 hpp1 hnorm1
      zteqq) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨cl2, cl2iff, cl1iff, clsym, fr₂, -, hm₂⟩
  rw [hpos1] at cl2iff cl1iff clsym
  have keep2 : ∀ r, bandOf r ∉ oracleBands → (r < sw 2202 ∨ sw 2232 < r) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 =>
    (fr₂ r h1 ztfqa h3).trans
      (fr₁ r h1 zteo h3)
  have keep21 : ∀ r, bandOf r ∉ oracleBands → r < oCl → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
    by grind
  have hm12 : ztjbp := by_grind
  have best2 : ztflg := fun r hr => keep2 r
    ztbafo
    ztcuj
    ztggi
  have kE2 : c₂.nreg kE = c.nreg kE := keep2 _ ztbur
    by_decide by_decide
  have kH2 : c₂.nreg kH = c.nreg kH := keep2 _ ztbur
    by_decide by_decide
  have same2 : SameKB c c₂ := ⟨kE2, kH2, best2⟩
  have k1 := (E.hK.fix hI₂).2.1
  -- the rejection (class `0` or `2`)
  have rejQ : c₂.nreg oCl ≠ 1 →
      CandRes P J ztwis ztdmu ztci
        (N₂.chord k).up (N₂.chord k).dn
        ztwut ztxnz c c₂ ∧
      (endOrigin J zta N₂ ztci ∈ J.right.set →
        endOrigin J zta N₂ ztci ≠ J.shared →
        endOrigin J zta N₂ ztci ≠ J.right.top →
        CandComp P J ztwis ztdmu ztci
          (N₂.chord k).up (N₂.chord k).dn
          ztwut ztxnz
          ztxgl c c₂) ∧
      (¬ (endOrigin J zta N₂ ztci ∈ J.right.set ∧
        endOrigin J zta N₂ ztci ≠ J.shared ∧
        endOrigin J zta N₂ ztci ≠ J.right.top) → RejAt c c₂) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c₂.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c₂.nreg ALLOC := by
    intro hn1
    refine ⟨Or.inl ⟨hm12, best2 _ ztp, best2 _ ztwiz,
      best2 _ ztbh,
      lblOf_congr ztyqp,
      best2 _ ztbaje⟩, ?_, fun _ => ⟨hm12, best2 _ (Or.inl rfl),
      best2 _ ztwiz, best2 _ ztbh,
      lblOf_congr ztyqp,
      best2 _ ztbaje⟩, ?_, by_omega⟩
    · intro haR hav hat p t _ _ _ _ h5 _
      have hhigh : ¬ (endOrigin J _ N₂ _).2 ≤ J.left.top.2 :=
        fun h => hn1 (cl1iff.2 ⟨haR, hav, hat, h⟩)
      exact absurd h5 (high_no_hit haR hσ hhigh)
    · zuete
      exact keep2 r h1 (by unfold OrgR at h2; omega) h3
  by_cases hc0 : c₂.nreg oCl < c₂.nreg K1
  · exact IRS.mono (K := 0 + 2) (IRS.ifT hc0 (IRS.skip hI₂ (rejQ by_omega))) by_omega
      ztb
  refine IRS.mono (K := 16707 + evCandK ztwiu L.length KG + 2 + 2)
    (IRS.ifF hc0 ?_) by_omega ztb
  by_cases hc2 : c₂.nreg K1 < c₂.nreg oCl
  · exact IRS.mono (K := 0 + 2) (IRS.ifT hc2 (IRS.skip hI₂ by_grind)) by_omega
      ztb
  refine IRS.ifF hc2 ?_
  have hcl : c₂.nreg oCl = 1 := by_omega
  obtain ⟨haR, hav, hat, ha₁⟩ := cl1iff.1 hcl
  obtain ⟨sy, hsym, hsl, hse⟩ := clsym hcl
  -- 3. the abscissa
  have eE2 : c₂.nreg oE = c₁.nreg oE := keep21 _ ztbur
    by_decide by_decide
  have eC2 : c₂.nreg oC = c₁.nreg oC := keep21 _ ztbur
    by_decide by_decide
  have hpos2 : (chainModel J.right).pos zta ztkkm =
      endOrigin J zta N₂ ztci := by_grind
  have hy2 : |((chainModel J.right).pos zta ⟨c₂.nreg oE, c₂.nreg oC⟩).2| < J.right.radius := by
    grind
  refine IRS.seq
    (callAbs_irs hI₂ ztmas
      by_decide by_decide
      by_omega by_grind hy2
      zteqq) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨habs3, fr₃, -, hm₃⟩
  rw [hpos2] at habs3
  have keep32 := fr₃
  have keep3 := fun r h1 h2 h3 =>
    (keep32 r h1 (by unfold oAbsA sw at *; omega) h3).trans (keep2 r h1 h2 h3)
  have keep31 :=
    fun r h1 h2 h3 => (keep32 r h1 (by unfold oAbsA oCl sw at *; omega) h3).trans
      (keep21 r h1 h2 h3)
  have hm3 := fun x hx =>
    (hm₃ x by_omega).trans (hm12 x hx)
  have best3 : ztflh := fun r hr => keep3 r
    ztbafo
    ztcuj
    ztggi
  have r3 :=
    fun r h1 h2 h3 => keep3 r zthse h3 ztu
  have r31 :=
    fun r h1 h2 => keep31 r (band_sw_not ⟨h1, by unfold oCl sw at h2; omega⟩) h2
      ztu
  have same3 : SameKB c c₃ :=
    ⟨r3 _ by_decide by_decide by_decide,
      r3 _ by_decide by_decide by_decide, best3⟩
  have eGK : c₃.nreg wGK = c.nreg wGK :=
    r3 _ by_decide by_decide by_decide
  have eGB : c₃.nreg wGB = c.nreg wGB :=
    r3 _ by_decide by_decide by_decide
  have eK : ztusq := by
    rw [r3 _ by_decide by_decide by_decide, hkd]
  have eS : c₃.nreg oS = s := by
    rw [r3 _ by_decide by_decide by_decide, hsd]
  have eUp : c₃.nreg oUp = (N₂.chord k).up := by
    rw [r31 _ by_decide by_decide, vUp]
  have eDn : c₃.nreg oDn = (N₂.chord k).dn := by
    rw [r31 _ by_decide by_decide, vDn]
  have eD : c₃.nreg oD = if s = 0 then 1 else 0 := by
    rw [r31 _ by_decide by_decide, vD]
  have eFE : c₃.nreg oFE = (farEnd N₂ k s).edge := by
    rw [r31 _ by_decide by_decide, vFE]
  have eFC : c₃.nreg oFC = (farEnd N₂ k s).hgt := by
    rw [r31 _ by_decide by_decide, vFC]
  have eTB : c₃.nreg cTB = c.nreg cTB :=
    (hI₃.hin _ by_trivial).trans (hI.hin _ by_trivial).symm
  have hsym3 := symPtIn_transport hsym
    (keep32 _ ztbur by_decide
      by_decide)
    (keep32 _ ztbur by_decide
      by_decide)
    (keep32 _ ztbur by_decide
      by_decide)
  have hfar3 : (chainModel J.right).pos zta ⟨c₃.nreg oFE, c₃.nreg oFC⟩ =
      if c₃.nreg oD = 1 then Merge.rend ztwyu
      else Merge.lend ztwyu := by
    rw [eFE, eFC, eD]; omega
  have hch : (N₂.chord k).toSet ztj zta ∈ N₂.F ztj zta := by
    refine ⟨N₂.chord k, ?_, rfl⟩
    zudly
    zukpu
    zulee
  have hlo : ShotList.loSet ztbw zta c₃.nmem (c₃.nreg wGB) L.length [] =
      ShotList.loSet ztbw zta c.nmem ztdcv L.length [] := by
    zupca; exact loSet_congr (fun x _ hx => hm3 x by_omega)
  -- 4. the candidate
  have hev := evCand_irs E hI₃ hgen hL by_omega by_omega
    (fun i hi => by rw [eGB, ← harcs i hi]; unfold ShotList.arcAt
                    rw [hm3 _ by_omega, hm3 _ by_omega, hm3 _ by_omega, hm3 _ by_omega])
    hch (by zunle; split_ifs <;> omega) (by zunle; omega) hsym3 hsl hse habs3 haR hav ha₁
    by_omega ztfpj hfar3 by_omega
    (by rw [same3.1, same3.2.1]; omega)
    (by rw [best3 _ ztp, best3 _ ztwiz,
      best3 _ ztbh]; exact hb)
    (by rw [best3 _ ztp]; omega)
    (by rw [best3 _ ztbaje]; omega)
    zteqq
  refine hev.mono le_rfl ?_
  rintro c' ⟨hres, hcomp, hfr, hA'⟩
  rw [eTB, eK, eS, eUp, eDn, eD, ← hDir] at hres hcomp
  rw [hlo] at hcomp
  refine ⟨candRes_lift same3 by_omega hm3 hres, fun _ _ _ => candComp_lift same3 by_omega hm3 hcomp,
    (absurd ztrcv), fun r h1 h2 h3 => ?_, by_omega⟩
  unfold OrgR at h2
  push Not at h2
  rw [hfr r h1 h2.1 h3]
  exact keep3 r h1 by_omega h3
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine WalkEmbed Sweep
@[expose] public section
theorem F₂plus_chordFamily' {J : Merge.Junction} {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hvtx : ∀ k, ∃ h, h < Q.n ∧ (J.whole.vertex k).2 = (Q.vtx h).2) :
    (chainModel J.whole).ChordFamily Q ztbi := by
  zuftz
  refine ⟨F₂plus_finite J hS₂.1, F₂plus_subset J hS₂a, fun e he => ?_⟩
  -- a point of `e` at a vertex height of `Q`
  obtain ⟨z, hz, h, hh, hzh⟩ : ∃ z ∈ e, ∃ h, h < Q.n ∧ z.2 = (Q.vtx h).2 := by
    rcases f2_cases hS₂a he with ⟨c, hc, a, σ, ha, -, rfl⟩ | ⟨σ, -, -, rfl⟩ | ⟨σ, -, -, rfl⟩
    · refine ⟨a, origin_mem J, ?_⟩
      obtain ⟨h, hh, a', b', hceq⟩ := hS₂.2.2 c hc
      obtain ⟨y, l, r, hH, -, hcy, hl, hr⟩ := Merge.augChords_spec ztmkx
      zubwk
      have hmem : a ∈ c := by
        rcases ha with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · rw [hl, hcy]; exact ⟨rfl, le_rfl, hlr.le⟩
        · rw [hr, hcy]; exact ⟨rfl, hlr.le, le_rfl⟩
      rw [hceq] at hmem
      exact ⟨h, hh, hmem.1⟩
    · obtain ⟨h, hh, e⟩ := hvtx J.m₁
      exact ⟨J.shared, origin_mem J, h, hh, e⟩
    · obtain ⟨h, hh, e⟩ := hvtx ztrw
      refine ⟨J.right.top, origin_mem J, h, hh, ?_⟩
      rw [← e, Merge.Junction.whole_vertex_add]; rfl
  obtain ⟨y, l, r, -, -, rfl, -, -⟩ := Merge.augChords_spec ztleq
  refine ⟨h, hh, l, r, ?_⟩
  rw [show y = (Q.vtx h).2 from hz.1.symm.trans hzh]

/-- **The vertices of a described chain are at vertex heights of `Qof P`.** -/
theorem whole_vertex_height {P : Polygon} (hn3 : 3 ≤ P.n) {E : ℕ} {m : ℕ → ℕ} {B : ℕ} {H : Host}
    {C : Chain} (hwf : ChainWF P E m B) (hC : ChainDescAt m B zta H C) (k : ℕ) :
    ∃ h, h < (Qof P).n ∧ (C.vertex k).2 = ((Qof P).vtx h).2 := by
  zuc
  have hHwf : HostWF (Qof P).n H := by zvmxg; exact (hwf.2 H C hC).2.1
  zukdy
  rw [DownMath.chain_vertex_host hC.2.1 k, Gran.eval_snd]
  refine ⟨_, Gran.hv_lt ?_, rfl⟩
  set L := H.pts (Qof P).n
  by_cases hi : zttw % L.length < L.length
  · zuews
    exact NFLoc.hostWF_pts hHwf hn _ ztdbx
  · rw [List.getD_eq_default _ _ by_omega]
    exact hn

/-- **`F₂⁺` is a chord family of `Qof P`** in the environment of the event loop. -/
theorem F₂plus_chordFamily {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) :
    (chainModel J.whole).ChordFamily zta (F₂plus J ztwis) := by
  obtain ⟨-, -, hwf, ⟨H, hC, -⟩, -, -⟩ := E.ctxW
  exact F₂plus_chordFamily' E.hNF₂.1 (whole_vertex_height E.hG.1.1 hwf hC)
open Machine.Stmt Programs SweepIo SweepPrim SweepRam
open Chazelle.Chain (SideAttach sidePt)
def GenTask : Prop :=
  ∃ (mkG : Stmt → Stmt) (κG : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
      GenOK P W c₀ J ztqtq
        ztbaqj

/-! ## B: stage 2 (the stops) -/

/-- The output registers of stage 2: the stop records (`sB`, count `sC`) and the auxiliary
records (`aB`). -/
def sB : ℕ := sw 2600
def sC : ℕ := sw 2601
def aB : ℕ := sw 2602

/-- The registers stage 2 may write (besides the oracle bands and the allocator). -/
def S2R (r : ℕ) : Prop :=
  ztgz ∨ ztltt ∨ ztcok

/-- `E` auxiliary records of five words `(anc, nl, l₀, l₁, par)` at `A`. -/
def AuxRecsAt (m : ℕ → ℕ) (A : ℕ) (ax : List ztcf) : Prop :=
  ∀ i, i < ax.length →
    m ztjgj = (ax.getD i ztip).1 ∧
    m ztgzo = (ax.getD i ztip).2.1 ∧
    m ztnim = (ax.getD i ztip).2.2.1 ∧
    m ztnin = (ax.getD i ztip).2.2.2.1 ∧
    m ztnio = (ax.getD i ztip).2.2.2.2

/-- **The auxiliary data of a stop chord `e`**: `anc = 1` iff `e` is not a bracket (it has an
attachment with offset `< Lst`); then, unless `e` is a pocket (attached at offset `0`), the
`nl ≤ 2` labels `l₀, l₁` (region indices of `N₂`) are side labels of `e` (`EvSideLab`); `par` is
`k + 1` for the chord `k` of `N₂` containing `e`, if any (`0` if none). -/
def AuxOK (P : Polygon) (J : Merge.Junction) (N₂ : NF) (e : Set Point)
    (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  x.1 ≤ 1 ∧ (x.1 = 1 ↔ ¬ EvBrk J e) ∧ x.2.1 ≤ 2 ∧
    (0 < x.2.1 → x.2.2.1 < N₂.nRegions) ∧ (1 < x.2.1 → x.2.2.2.1 < N₂.nRegions) ∧
    (x.1 = 1 → ztwnd →
      EvSideLab J ztwis
        (labSet J zta N₂ x.2.1 x.2.2.1 x.2.2.2.1 0 0) e) ∧
    x.2.2.2.2 ≤ N₂.nChords ∧
    (∀ c ∈ N₂.F ztj zta, e ⊆ c →
      0 < x.2.2.2.2 ∧ (N₂.chord ztueg).toSet ztj zta = c) ∧
    (0 < x.2.2.2.2 → e ⊆ (N₂.chord ztueg).toSet ztj zta)

/-- **The post of stage 2** (from `c` to `c'`, normal forms `N₁`, `N₂`): the stop records `rs`
(`StopRecsAt` at `sB`, count `sC`) satisfy `StopsOK` (all attachments on the `C₁` part of the stop
chords, sorted by offset, without duplicates) and the word facts of `Out`; the auxiliary records
(`aB`, one per stop) satisfy `AuxOK`; at most `4 K₂ + 8` stops (each of the `≤ 2 K₂ + 4`
stop chords has at most two attachments); both arrays are fresh
(between the allocators of `c` and `c'`); the memory below the allocator of `c` and the registers
outside `S2R` (and the oracle bands, the allocator) are unchanged. -/
def StopOut (P : Polygon) (J : Merge.Junction) (_N₁ N₂ : NF) (c c' : Config) : Prop :=
  ∃ (rs : List ztcf) (ax : List ztcf),
    rs.length = c'.nreg sC ∧ ax.length = rs.length ∧
    StopRecsAt c'.nmem ztqhe rs ∧ AuxRecsAt c'.nmem ztvgs ax ∧
    StopsOK J ztwis ztwoy ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      zthkb) ∧
    (∀ i, i < rs.length → AuxOK P J N₂
      (stopSet J zta N₂ (rs.getD i ztip).2.2.1 (rs.getD i ztip).2.2.2.1
        (rs.getD i ztip).2.2.2.2) (ax.getD i (0, 0, 0, 0, 0))) ∧
    rs.length ≤ 4 * N₂.nChords + 8 ∧
    c.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * rs.length ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ c'.nreg aB ∧ c'.nreg aB + 5 * rs.length ≤ c'.nreg ALLOC ∧
    zth ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ S2R r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task B: stage 2**, for every shooter, at cost
`κS D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)`. -/
def StopTask : Prop :=
  ∃ (mk2 : Stmt → Stmt) (κS : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg ALLOC + κS zto * ztks *
          ztwwx ≤ W →
      IRS P W c₀ ztvzf c (κS zto * ztks *
          ztwwx)
        (StopOut P J N₁ N₂ c)

/-! ## D: faced regions of `N₂` and the start -/

/-- The input registers of `face`: a walk edge `fE` of `C₂` (vertex position `(fE, 0)`), the side
`fA` (`0` before, `1` after); the output `fR`. -/
def fE : ℕ := sw 2610
def fA : ℕ := sw 2611
def fR : ℕ := sw 2612

/-- The registers `face` may write (besides the oracle bands and the allocator). -/
def FR (r : ℕ) : Prop := ztgz ∨ r = fR ∨ ztcok

/-- **The post of `face`**: `fR` is the index of a region of `N₂` faced just before (`fA = 0`) or
just after (`fA = 1`) the vertex position `(fE, 0)` of the walk of `C₂`. -/
def FaceOut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  c'.nreg fR < N₂.nRegions ∧
    (c.nreg fA = 0 → BeforeFaces ztj ztjsg 0
      ztxhg) ∧
    (c.nreg fA = 1 → AfterFaces ztj ztjsg 0
      ztxhg) ∧
    zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ FR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task D2** (mathematics): **the invariant at the start** when every chord of `F₂⁺` attached
at the start key (offset `Lst`, the copy of the shared vertex on the `C₁` side) is a bracket: the
label set `{V}` of the region of `S₂` faced just before the end of the right stretch in the walk
of `C₂` (`valid_start`). -/
def StartTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set ztf), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q ztbi →
    (∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e
      ztwks 0 → EvBrk J e) →
    ∀ V ∈ (chainModel J.right).regions S₂,
      BeforeFaces ztj
        (ztwug %
          (chainModel J.right).W.n) 0 V →
      EvInv J S₂ ztmbm {V}

/-! ## C: the window of the event loop -/

/-- The window registers (outputs): the part-end flag `wX`, the window end `(wE, wH)` (a position
of the walk of `C`), the gathered arcs `(wGB, wGK)` (`SweepEvShot.lean`). -/
def wE : ℕ := sw 2423
def wH : ℕ := sw 2424
def wX : ℕ := sw 2425

/-- The registers the window computation may write (besides the oracle bands and the allocator). -/
def WR (r : ℕ) : Prop :=
  ztgz ∨ (sw 2420 ≤ r ∧ r ≤ sw 2425) ∨ ztcok

/-- **The post of the window computation** from the current key `(kE, kH)` (offset `oL`): the
arcs of at most two regions `rs` of `N₁` are gathered (`regArcs`, normalised `nArc`, fresh
array); the window ends at the part end (`wX = 1`) or at the position `(wE, wH)` beyond the key
(`wX = 0`), which is the gap start (offset `Lst + lL1`) or the image of a cut key of `N₁`; every
valid offset of the walk of `C₁` whose image lies in `(oL, end]` has its point on the gathered
arcs (`loSet`, no holes). -/
def WinOut (P : Polygon) (J : Merge.Junction) (N₁ : NF) (c c' : Config) : Prop :=
  ∃ rs : List ℕ, rs.length ≤ 2 ∧ (∀ r ∈ rs, r < N₁.nRegions) ∧
    c'.nreg wGK = (regArcs N₁ rs).length ∧ c.nreg ALLOC ≤ c'.nreg wGB ∧
    c'.nreg wGB + 4 * (regArcs N₁ rs).length ≤ c'.nreg ALLOC ∧
    (∀ k, k < (regArcs N₁ rs).length → ShotList.arcAt c'.nmem zthug k =
      nArc ztbw zta N₁ ((regArcs N₁ rs).getD k 0)) ∧
    c'.nreg wX ≤ 1 ∧
    (c'.nreg wX = 0 → PosW P J ztfgk ztfgl ∧
      offK P J ztwe ztbhr < offK P J ztfgk ztfgl ∧
      (offK P J ztfgk ztfgl = (Lst J : ℝ) + lL1 J ∨
        ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
          offK P J ztfgk ztfgl = (Lst J : ℝ) + ψ J d + t ∧
          (chainModel J.left).IsCut ztwjx
            ztwms)) ∧
    (∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J ztwe ztbhr < (Lst J : ℝ) + ψ J d + t →
      ztdmo →
      sidePt (chainModel J.left).W ztwjw t ∈
        ShotList.loSet ztbw zta c'.nmem zthug
          (regArcs N₁ rs).length []) ∧
    zth ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ WR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task C1: the window**, for a key `(kE, kH)` of the `C₁` part (`Lst ≤ oL < n`), at cost
`κW D · (TLR + 1)` (`TLR = c₀.nreg TLR`, the length of the power table of `locJ`). -/
def WinTask : Prop :=
  ∃ (win : Stmt) (κW : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      PosW P J ztwe ztbhr → (Lst J : ℝ) ≤ offK P J ztwe ztbhr →
      c.nreg ALLOC + κW zto * ztgf ≤ W →
      IRS P W c₀ win c ztzoe ztqdg

/-- **Task C2 (mathematics): the number of arcs** of a normal form of a chain model:
`arcs ≤ 3 K + 1` (`K + 1` regions, `arcsPerRegion`, each chord on two regions). -/
def ArcsTask : Prop :=
  ∀ (C : Chain) (Q : Polygon) (N : NF), C.P.Simple → IsNF ztc Q N →
    N.arcs.length ≤ 3 * N.nChords + 1
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)
def fSE : ℕ := sw 1200
def fSH : ℕ := sw 1201
def fEE : ℕ := sw 1202
def fEH : ℕ := sw 1203
def fO : ℕ := sw 1204

/-- Read the ends of the arc at the spine position `lJ`. -/
def faceRead : List Instr :=
  [.addN lX lSB lJ, .loadN lX lX, .addN lY lX lX, .addN lY lY lY, .addN lY lY lX,
    .addN lY lAB lY, .addN lY lY K1, .loadN fSE lY, .addN lY lY K1, .loadN fSH lY,
    .addN lY lY K1, .loadN fEE lY, .addN lY lY K1, .loadN fEH lY]

/-- **The prefix of `face`**: locate, header, neighbours, regions, the arc at `j`. -/
def faceLoc : Stmt :=
  .seq (locJ ztqm ztbz fE K0 lJ)
    (.seq ztyvk
      ztffb)

/-- The cost of the prefix. -/
def faceLocK (L : ℕ) : ℕ := 5500 * ztgt + 9 + 60
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The arc read -/
variable (m f : ℕ → ℕ)
theorem faceRead_val (hk1 : f K1 = 1) :
    regB m faceRead f fSE = m (f lAB + 5 * m ztdnk + 1) ∧
    regB m faceRead f fSH = m (f lAB + 5 * m ztdnk + 2) ∧
    regB m faceRead f fEE = m (f lAB + 5 * m ztdnk + 3) ∧
    regB m faceRead f fEH = m (f lAB + 5 * m ztdnk + 4) := by
  zubx
  simp only [faceRead, regB, regI, upd, lX, lY, lSB, lAB, lJ, fSE, fSH, fEE, fEH, K1, sw]
  grind
theorem faceRead_ok (hk1 : f K1 = 1) (hb1 : f lSB + f lJ ≤ W)
    (hb2 : f lAB + 5 * m ztdnk + 4 ≤ W) : okB W m faceRead f := by
  zubx
  have hb1' : ztpor := hb1
  have hb2' : f 241116 + 5 * m ztqmt + 4 ≤ W := hb2
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [faceRead, okB, okI, regI, upd, lX, lY, lSB, lAB, lJ, fSE, fSH, fEE, fEH, K1, sw]
  grind
theorem faceRead_other {q : ℕ} (h1 : q ≠ lX) (h2 : q ≠ lY) (h3 : q ≠ fSE)
    (h4 : q ≠ fSH) (h5 : q ≠ fEE) (h6 : q ≠ fEH) : regB m faceRead f q = f q :=
  regB_other m faceRead f (fun i hi => by
    simp only [faceRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all)

/-- A block writing only registers of `sw 1102 … 1203` keeps the others. -/
theorem regB_out (l : List Instr)
    (hl : ∀ i ∈ l, sw 1102 ≤ dstI i ∧ dstI i ≤ sw 1203) {q : ℕ} (hq : q < sw 1102 ∨ sw 1203 < q) :
    regB m l f q = f q :=
  regB_other m l f by_grind
theorem faceRead_dst : ∀ i ∈ faceRead, sw 1102 ≤ dstI i ∧ dstI i ≤ sw 1203 := by
  decide

/-! ## The environment at a run configuration -/

/-- A model descriptor survives a change of the memory above its bound. -/
theorem modelDesc_transport {m m' : ℕ → ℕ} {D E E' : ℕ} {M : Model}
    (hd : ModelDescAt m D zta M) (hwf : ModelDescWF P E m D)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D zta M ∧ ModelDescWF P E' m' D := by
  zucis
  · zudjf

  · zuclr
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The model descriptor of `C₂` (`sw 31`, stage 0) at a run configuration. -/
theorem EvEnv.md₂ (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    ModelDescAt c.nmem ztxgo zta ztj ∧
      ModelDescWF P ztm c.nmem ztxgo := by
  zubos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d31, w31⟩ := hst
  have e : c.nreg _ = c₀.nreg ztqm := hI.hin _ by_trivial
  zui
  exact modelDesc_transport d31 w31 hI.hm hI.hA

/-- The normal form `N₂` is protected below the power table. -/
theorem EvEnv.nt₂ (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    NFWithin c.nmem ztwrb ztvjh N₂ := by
  rw [hI.hin _ ztlta,
    hI.hin _ ztddj]
  zumaw
  exact Robust.transport E.hNT₂ zthgt

/-- The power table at a run configuration. -/
theorem EvEnv.tab (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    ztug ∧ N₂.arcs.length < 2 ^ c.nreg TLR ∧
      c.nreg TBR + c.nreg TLR ≤ c₀.nreg ALLOC ∧ c.nreg TLR = c₀.nreg TLR := by
  zucro

  refine ⟨fun j hj => ?_, by rw [eL]; exact E.hbig₂, by_omega, eL⟩
  zudfr

/-! ## The prefix -/

/-- **The post of the prefix**: the spine answer `j` of double identification for the vertex
`(fE, 0)`, the regions of the arcs at `j - 1`, `j`, `j + 1`, the ends of the arc at `j`. -/
def LocOut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  ∃ j, j < N₂.arcs.length ∧
    (¬ (chainModel J.right).IsCut ztwis ztjsg →
      N₂.F ztj zta = ∅ ∨
        sideInArc ztzhd ztzeo
          ztjsg) ∧
    ((chainModel J.right).IsCut ztwis ztjsg →
      sk ztj zta N₂ j = c.nreg fE ∨
        ek ztj zta N₂ j = c.nreg fE) ∧
    c'.nreg lR0 = (N₂.arc ztdih).reg ∧
    c'.nreg lR1 = (N₂.arc ztvt).reg ∧
    c'.nreg lR2 = (N₂.arc ztdii).reg ∧
    c'.nreg fSE = (N₂.arc ztvt).s.edge ∧ c'.nreg fSH = (N₂.arc ztvt).s.hgt ∧
    c'.nreg fEE = (N₂.arc ztvt).e.edge ∧ c'.nreg fEH = (N₂.arc ztvt).e.hgt ∧
    c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
    ∀ r, bandOf r ∉ oracleBands → ztbwb → c'.nreg r = c.nreg r
theorem out_ne {r q : ℕ} (hr : r < sw 1102 ∨ sw 1203 < r) (h1 : sw 1102 ≤ q) (h2 : q ≤ sw 1203) :
    r ≠ q := by
  omega
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The prefix of `face`.** -/
theorem faceLoc_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fE < (chainModel J.right).W.n)
    (hroom : c.nreg ALLOC + faceLocK ztdg ≤ W) :
    IRS P W c₀ faceLoc c ztbahv (LocOut P J N₂ c) := by
  zuiw
  zuch
  zubkh

  zufe

  zudni
  have hpp : ProperPos ztj zta P.n ⟨c.nreg fE, c.nreg K0⟩ := by
    zvnib; exact ztpfc
  -- 1. locate
  unfold faceLoc
  refine IRS.mono (K := ztwzf + ztgxg)
    (IRS.seq (locJ_irs hI E.hG E.hWh
      ⟨by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hmd hmwf hP₂ hNA hNF
      hfe hpp htab hbig by_omega by_omega by_omega by_omega
      ztiro) ?_)
    ztksu ztb
  zubyj

  rw [k0, key_vertex] at hl1 hl2
  zukid
  have e4 : ztzpo :=
    keep1 _ ztmr
      by_decide
  -- 2. copy the normal form register
  refine IRS.seq (IRS.block [.copyN lNF _] hI₁
    ⟨iscr_sw by_decide by_decide, trivial⟩) ?_
  zubib
  zufvm
  have c2NF : ztzpv := by
    zudua
  have c2r : ztkow := by
    zucni
    zubdg
  zudhh
  -- 3. the header
  refine IRS.seq (IRS.block nbrHead hI₂ (nbrHead_ok _ _ hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
    by_omega)) ?_
  zubsf

  have c3A : ztuso := by
    zuccb

  have c3SB : ztbaqq := by
    simp_all
  have c3AB : ztbaqp := by
    simp_all
  have c3r : ztezj := by
    zucsc
  have c3J : ztpnp := by
    rw [c3r _ by_decide by_decide
      by_decide by_decide,
      c2r _ by_decide]
  -- 4. the neighbouring positions
  zubps

  have c4SB : ztbaqs := by
    zuhmw
  have c4AB : ztbaqr := by
    zuhmu
  have c4J : ztpnv := by
    zuhmv
  zudor
  -- the table reads
  have hseqv : ztjbe :=
    fun p hp => hNA.2.2.2.2.2.2.2.2.1 p ztlgq
  have hsjl : ztkoh := fun p hp =>
    NFLoc.seq_lt hNF hp
  have harcv : ∀ a, a < N₂.arcs.length →
      c.nmem _ = (N₂.arc a).reg ∧
      c.nmem _ = (N₂.arc a).s.edge ∧
      c.nmem _ = (N₂.arc a).s.hgt ∧
      c.nmem _ = (N₂.arc a).e.edge ∧
      c.nmem _ = (N₂.arc a).e.hgt :=
    hNA.2.2.2.2.2.2.1
  zufub
  have hb1 : ∀ v, v < N₂.arcs.length → c.nmem ztwpb + v ≤ W ∧
      c.nmem ztwsm + 5 * c.nmem ztbaqc + 4 ≤ W := by
    zuml
    zugem
    have := b3 _ ztobg
    omega
  have hbound : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      c₄.nreg lSB + c₄.nreg p ≤ W ∧ c₄.nreg lAB + 5 * c₄.nmem ztqkq ≤ W := by
    zuda
    zuiha
    zubyb
    · zufoo
    · zufms
    · zufon
  -- 5. the three regions
  zuciu

  have c5R0 : ztyun := by
    zuzy

  have c5R1 : ztyuo := by
    zuzz

  have c5R2 : ztyup := by
    zubaa

  have c5r : ztdxu := by
    zuchh
  have hm5 : ztlaq := by rw [hc5]; omega
  have c5SB : ztbaqu := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4SB]
  have c5AB : ztbaqt := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4AB]
  have c5J : ztpny := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4J]
  zufto
  -- 6. the arc at `j`

  refine (IRS.block faceRead hI₅ (faceRead_ok _ _ hK₅.2.1 by_omega
    ztiig)).mono le_rfl ?_
  zubjs

  have c6r : ztygy := by
    zudqg
  have c6o : ∀ q, q ≠ lX → q ≠ lY → q ≠ fSE → q ≠ fSH → q ≠ fEE → q ≠ fEH →
      c₆.nreg q = c₅.nreg q := by
    zucbb
  have hothers : ∀ r, bandOf r ∉ oracleBands → ztbwb →
      c₆.nreg r = c.nreg r := by
    zubjg

    rw [c6r r hrr,
      c5r r ztpz
        ztpz
        ztpz
        ztpz
        ztpz,
      k4' r ztpz
        ztpz,
      c3r r ztpz
        ztpz
        ztpz
        ztpz,
      c2r r ztrty]
    zulfo
  have hR : ztfdu := by
    rintro q (rfl | rfl | rfl) <;> apply c6o <;>
      zuckm
  refine ⟨j, hj1, hl1, hl2, by zuobo,
    by zuobp, by zuobq,
    ?_, ?_, ?_, ?_, by zunsx; omega,
    hothers _ by_decide ztbuo, hothers⟩
  · zubly

  · zublz

  · zublw

  · zublx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
def faceChk (xe xh src : ℕ) : Stmt :=
  .ifLtN xe fE .skip (.ifLtN fE xe .skip (.ifLtN K0 xh .skip (block [.copyN fR src])))

/-- The selection of the answer. -/
def faceSel : Stmt :=
  .seq (block [.copyN fR lR1]) (.ifLtN fA K1 (faceChk fSE fSH lR0) (faceChk fEE fEH lR2))

/-- **The procedure `face`.** -/
def face : Stmt :=
  .seq faceLoc (.seq (normS zted fSE fSH fO) (.seq (normS zted fEE fEH fO) faceSel))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem iscr_fR : IScr fR := iscr_sw by_decide by_decide
theorem faceChk_irs {xe xh src : ℕ} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) :
    IRS P W c₀ (faceChk xe xh src) c 7 (fun c' =>
      c'.nreg fR = (if c.nreg xe = c.nreg fE ∧ c.nreg xh = 0 then c.nreg src else c.nreg fR) ∧
      ztivj ∧ c'.nmem = c.nmem) := by
  unfold faceChk
  by_cases h1 : c.nreg xe < c.nreg fE
  · refine (IRS.ifT h1 (IRS.skip (K := 0) hI ztcos)).mono by_omega
      ztb
    grind
  by_cases h2 : c.nreg fE < c.nreg xe
  · refine (IRS.ifF h1 (IRS.ifT h2 (IRS.skip (K := 0) hI ztcos))).mono
      by_omega ztb
    grind
  by_cases h3 : c.nreg K0 < c.nreg xh
  · refine (IRS.ifF h1 (IRS.ifF h2 (IRS.ifT h3 (IRS.skip (K := 0) hI ztcos))))
      |>.mono by_omega (fun _ h => h)
    grind
  · refine (IRS.ifF h1 (IRS.ifF h2 (IRS.ifF h3 (IRS.block [.copyN fR src] hI
      ⟨iscr_fR, trivial⟩)))).mono by_simp ?_
    zuu
    zuflx
    · zufpt

    · zubdg
theorem faceSel_irs (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0) :
    IRS P W c₀ faceSel c 10 (fun c' =>
      c'.nreg fR = (if c.nreg fA < c.nreg K1 then
          (if c.nreg fSE = c.nreg fE ∧ c.nreg fSH = 0 then c.nreg lR0 else c.nreg lR1)
        else (if c.nreg fEE = c.nreg fE ∧ c.nreg fEH = 0 then c.nreg lR2 else c.nreg lR1)) ∧
      ztivj ∧ c'.nmem = c.nmem) := by
  unfold faceSel
  refine (IRS.seq (IRS.block [.copyN fR lR1] hI ⟨iscr_fR, trivial⟩) ?_).mono (K := 1 + (7 + 2))
    by_norm_num ztb
  zugn
  have v1 : c₁.nreg fR = c.nreg lR1 := by
    zubuz
  have o1 : ∀ r, r ≠ fR → c₁.nreg r = c.nreg r := by
    intro r hr; zvmwl; zunnd
  zull
  have n : ∀ q, (q = fA ∨ q = K1 ∨ q = K0 ∨ q = fSE ∨ q = fSH ∨ q = fEE ∨ q = fEH ∨ q = fE ∨
      q = lR0 ∨ q = lR1 ∨ q = lR2) → c₁.nreg q = c.nreg q := by
    zuco
    apply o1
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fR, fA, K1, K0, fSE, fSH, fEE, fEH, fE, lR0, lR1, lR2, sw]
  have hk0' : zteib := by_simp_all
  by_cases hA : c₁.nreg fA < c₁.nreg K1
  · refine (IRS.ifT hA zttjy).mono le_rfl ?_
    grind
  · refine (IRS.ifF hA zttjy).mono le_rfl ?_
    grind

/-! ## The task -/
set_option maxRecDepth 20000 in
theorem face_cost (L : ℕ) : faceLocK L + (11015 + (11015 + 10)) ≤ 30000 * ztgt := by
  zumsq
set_option maxRecDepth 20000 in
theorem face_room1 {a L W : ℕ} (h : a + 30000 * ztgt ≤ W) : a + faceLocK L ≤ W := by
  zumsq
set_option maxRecDepth 20000 in
theorem face_room2 {a L W : ℕ} (h : a + 30000 * ztgt ≤ W) : a + 11015 ≤ W := by
  grind
set_option maxRecDepth 20000 in
theorem face_room3 {a b L W : ℕ} (h : a + 30000 * ztgt ≤ W) (hb : b ≤ a + 11015) :
    b + 11015 ≤ W := by
  grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed Sweep
@[expose] public section
variable (J : Merge.Junction)
/-- The right stretch is shorter than the walk of `C`. -/
theorem Lst_lt_n : Lst J < (chainModel J.whole).W.n := by
  zuhf
  zucz
  zudnh
  have hL : Lst J = rlen J := rL1_add_rL2 J
  rw [hn, hL, hm]
  unfold rlen
  grind

/-- The offset of the start key is `Lst`. -/
theorem oW_start (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    oW J (((ztit % (chainModel J.whole).W.n : ℕ) : ℝ) + 0) = (Lst J : ℝ) := by
  zuv
  have h := off_key (n := (chainModel J.whole).W.n) (g := gW J) (d := Lst J) hC.hg (Lst_lt_n J)
    (t := 0) le_rfl one_pos
  zumot
  simp_all

/-- **Task D2: the invariant at the start.** -/
theorem startTask : StartTask := by
  intro J Q S₂ hP hS₂ _hF hbrk V hV hW₂
  zuhxo

  zudbo
  have hn0 : ztcka := by have := Lst_lt_n J; omega
  set pK := ztit % n with hpKdef
  have hpK : pK < n := Nat.mod_lt _ hn0
  have hoK : oW J ztgwf = (Lst J : ℝ) := oW_start J hP hS₂a hS₂f
  zulin
  zueab

  · tauto
  zuloz

  obtain ⟨R, hR, hWR, q, u, hq, hu, hncq, hfq, h1, h2, hgap⟩ :=
    before_region_exists' hP hS₂a hS₂f hpK le_rfl one_pos by_simp_all hL0
  rw [hoK] at h1 h2 hgap
  -- the position before the start is not enclosed
  have hEq : ¬ EvEncl J S₂ (oW J ztzq) := by
    rintro ⟨e, -, pa, pb, ta, tb, -, -, -, hLa, hlt, -⟩
    linarith
  -- every chord attached between the two positions is a bracket
  have hbr' : ∀ e ∈ F₂plus J S₂, ∀ (q' : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q' s →
      oW J ztzq < oW J ztoff → oW J ztoff < oW J ztk → EvBrk J e := by
    intro e he q' s hA ha hb
    rcases lt_trichotomy (oW J ztoff) ztmbm with hlt | heq | hgt
    · zudja
      exact absurd ⟨ha, hlt⟩ (hgap _ ⟨e, he, q', s, hA, rfl⟩ k0 k1)
    · rw [← hoK] at heq
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hA.1 hpK hA.2.1 hA.2.2.1 le_rfl one_pos heq
      exact hbrk e he hA
    · exact hbr e he q' s hA hgt hb
  have hRG : R = G := evGL hP hS₂a hS₂f hq hp hu ht hncq hnc by_linarith hEq hEx hbr' hR hG hfq hf
  subst hRG
  refine ⟨V, Or.inl rfl, hV, ?_⟩
  exact valid_start J hP hS₂a hS₂f (by have := Lst_pos J; unfold Lst at this; exact_mod_cast this)
    hR hV hWR hW₂
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
@[expose] public section
def lB : ℕ := sw 2430
def lC : ℕ := sw 2431

/-- The finalisation block: the outputs to `sw 200, 201, 300, 301, 302`. -/
def finL : List Instr :=
  [.copyN ztcwm sB, .copyN ztsn sC, .copyN ztfx lB, .copyN ztex lC,
    .copyN ztps cTB]

/-- The finalisation. -/
def fin : Stmt := block finL

/-- The configuration after the finalisation (only registers change). -/
def finCfg (c : Config) : Config := { c with nreg := regB c.nmem finL c.nreg }

/-- **The post of the run steps** (from `c₀`, the start of the run steps, to `c'`): the outputs
`Out` read at the registers of `finCfg c'`; the three arrays lie at or above the allocator of
`c₀` and below that of `c'`; at most `16 (K₁ + K₂ + 1)` stops and log records. -/
def RunOut (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c₀ c' : Config) : Prop :=
  Out P J N₂ ztjvd ∧
    c₀.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * c'.nreg sC ≤ c'.nreg ALLOC ∧
    c₀.nreg ALLOC ≤ c'.nreg lB ∧ c'.nreg lB + 7 * c'.nreg lC ≤ c'.nreg ALLOC ∧
    c'.nreg cTB + 3 * ztbxu ≤ c'.nreg ALLOC ∧
    c'.nreg sC ≤ 16 * ztks ∧
    c'.nreg lC ≤ 16 * ztks

/-- **The run steps** (stage 3), for every shooter, at cost
`κR D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)` (`D = c₀.nreg (sw 6)`,
`γ = c₀.nreg (sw 5)`, `K₁ = N₁.nChords`, `K₂ = N₂.nChords`). -/
def RunTask : Prop :=
  ∃ (run : Stmt → Stmt) (κR : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → WordsBounded W c₀ →
      c₀.nreg ALLOC + κR zto * ztks *
          ztwwx ≤ W →
      IRS P W c₀ ztwcw c₀ (κR zto * ztks *
          ztwwx)
        (RunOut P J N₁ N₂ c₀)

/-! ## The initialisation -/

/-- The facts of the precondition `Pre` for given `H J N₁ N₂` (the body of its existential). -/
def PreAt (_X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (c : Config) (H : Host)
    (J : Merge.Junction) (N₁ N₂ : NF) : Prop :=
  JunctionAt c.nmem ztcds ztcdt ztcdu zta H J ∧
    J.P.Simple ∧
    Ok P ztbw ∧ Ok P ztj ∧
    NFWithin c.nmem ztwb ztm N₁ ∧
    NFWithin c.nmem ztrl ztm N₂ ∧
    IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
    (chainModel J.left).DegLe ztwjx ztbwd ∧
    (chainModel J.right).DegLe ztwis ztbwd ∧
    (chainModel J.left).Semigranular ztwjx ztbro ∧
    (chainModel J.right).Semigranular ztwis ztbro ∧
    St0S P c H J

/-- **Task I: the initialisation**, at cost `κI · (K₁ + K₂ + 1)` (`K₁ = c.nmem (rd c bSweep 3)`,
`K₂ = c.nmem (rd c bSweep 4)`): from `Pre` at `c` it reaches `c₀` with `EvEnv` for every
`H J N₁ N₂` of the precondition, writing only the bands of the sweep and the oracles, keeping the
registers `sw 0 … 199`, with `WordsBounded W c₀`. -/
def InitTask : Prop :=
  ∃ (init : Stmt) (κI : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands → ShooterOK sh Bs F X Ok →
    ∀ (P : Polygon) (W : ℕ) (c : Config), WordsBounded W c → Pre X Ok P W c →
      c.nreg ALLOC + κI * ztwou ≤ W →
      ∃ c₀ k, Exec P W init c c₀ k ∧ k ≤ κI * ztwou ∧
        Frame ztdwg c c₀ k ∧ WordsBounded W c₀ ∧
        (∀ j, j < 200 → c₀.nreg ztgc = c.nreg ztgc) ∧
        ∀ H J N₁ N₂, PreAt X Ok P c H J N₁ N₂ → EvEnv sh Bs F X Ok P W c₀ J N₁ N₂

/-! ## Valid origins (mathematics) -/

/-- **Task O (mathematics): the chord seen from a valid origin.**  For the endpoint query `j` of
`N₂` whose origin `a = endOrigin j` is a point of `C₂` other than the shared vertex and the top
of `C₂`, and whose first hit in `C` comes strictly before its first hit in `C₂` (direction
`σ = endDir j`):

1. the chord `e = shoot J.whole a σ` is not a stop chord (`StopChord2`), and it is attached at a
   position `(p, t)` of the walk of `C` (`p < n`, `0 ≤ t < 1`) whose point is the first hit
   `rayPt a σ (J.whole.hitParam a σ)`, on the `C₁` part strictly beyond the start
   (`Lst < oW (p + t)`), and not the shared vertex;
2. the chord determines the query: two such queries `j, j'` with the same chord are equal. -/
def OriginTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (N : NF), J.P.Simple → IsNF ztj Q N →
    (chainModel J.whole).ChordFamily Q ztbard →
    (∀ j, j < 2 * N.nChords → endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
      endOrigin J Q N j ≠ J.right.top →
      J.whole.hitParam zttr ztri <
        J.right.hitParam zttr ztri →
      ¬ StopChord2 J ztwzl
          ztxmy ∧
        ∃ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n ∧ 0 ≤ t ∧ t < 1 ∧
          SideAttach (chainModel J.whole).W
            ztxmy p t ∧
          sidePt (chainModel J.whole).W p t = rayPt zttr ztri
            ztztr ∧
          (Lst J : ℝ) < oW J ztk ∧ sidePt (chainModel J.whole).W p t ≠ J.shared) ∧
    (∀ j j', j < 2 * N.nChords → j' < 2 * N.nChords →
      endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
      endOrigin J Q N j ≠ J.right.top →
      J.whole.hitParam zttr ztri <
        J.right.hitParam zttr ztri →
      endOrigin J Q N j' ∈ J.right.set → endOrigin J Q N j' ≠ J.shared →
      endOrigin J Q N j' ≠ J.right.top →
      J.whole.hitParam ztjut ztdzt <
        J.right.hitParam ztjut ztdzt →
      Merge.shoot J.whole zttr ztri =
        Merge.shoot J.whole ztjut ztdzt → j = j')

/-! ## The assembly -/

/-- **Task Z: the assembly** of `sweepEvSpec` from the initialisation and the run steps
(program `init ; run sh ; fin`). -/
def AsmTask : Prop := InitTask → RunTask → SweepEvSpec
def okWI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN _ k => k ≤ W
  | .copyN _ _ => True
  | .addN _ a b => f a + f b ≤ W
  | .subN _ _ _ => True
  | .loadN _ _ => True
  | _ => False

/-- The side conditions of a register block along its run. -/
def okW (W : ℕ) (m : ℕ → ℕ) : List Instr → ztjx → Prop
  | [], _ => True
  | i :: l, f => okWI W f i ∧ okW W m l ztefz
variable {P : Polygon} {W : ℕ} {c : Config} (m f : ℕ → ℕ) (J : Merge.Junction)
theorem exec_regI (hw : WordsBounded W c) {i : Instr}
    (hi : okWI W c.nreg i) : Exec P W ztbgj c { c with nreg := regI c.nmem i c.nreg } 1 := by
  cases i with
  | constN r k => exact Exec.constN hw r k hi
  | copyN r a => exact Exec.copyN hw r a
  | addN r a b => exact Exec.addN hw r a b hi
  | subN r a b => exact Exec.subN hw r a b
  | loadN r a => exact Exec.loadN hw r a
  | _ => exact absurd hi by_tauto

/-- **A straight-line register block** runs to `regB`. -/
theorem exec_regB : ∀ (l : List Instr) {c : Config}, WordsBounded W c →
    okW W c.nmem l c.nreg → Exec P W ztgfk c { c with nreg := regB c.nmem l c.nreg } l.length
  | [], _, hw, _ => Exec.block_nil hw
  | i :: l, _, hw, ⟨hi, hl⟩ => by
    have e1 := exec_regI (P := P) hw hi
    exact Exec.block_cons e1 (exec_regB l e1.wb_right hl)

/-! ## The block `regA` -/
def iL : ℕ := sw 700
def iT : ℕ := sw 701
def iG : ℕ := sw 702
def iO : ℕ := sw 703
def iB : ℕ := sw 704

/-- The constants, the copies, `Lst`, `E₁`, `gW + Lst`, `sw 45 + n - gW`, and the words `m`,
`topIdx`, `sideBeta` of the descriptor of `C₂`. -/
def regA : List Instr :=
  [.constN K0 0, .constN K1 1, .constN K6 6, .constN K4 4, .constN K5 5, .constN K2 2,
    .constN K3 3, .copyN cGW ztfg, .copyN cN1 ztna, .copyN cNW zthg, .copyN cLL ztddn,
    .copyN cLD ztcdx, .addN cLE ztddn ztcdx, .subN c2m zthy ztcwo,
    .subN c2m6 zthy ztxr, .addN iL ztyl ztbsy, .subN iT zthg iL,
    .addN cE1 iT ztcdx, .addN iG ztfg iL, .addN iO ztbca zthg, .subN iO iO ztfg,
    .addN iT zted K2, .loadN cm iT, .addN iT zted K3, .loadN cTop iT,
    .addN iT zted K4, .loadN iB iT]
set_option maxRecDepth 20000 in
theorem regA_ok (hW : 6 ≤ W) (h1 : f ztddn + f ztcdx ≤ W)
    (h2 : f ztyl + f ztbsy ≤ W) (h3 : f zthg - ztwps + f ztcdx ≤ W)
    (h4 : f ztfg + ztwps ≤ W) (h5 : f ztbca + f zthg ≤ W)
    (h6 : f zted + 4 ≤ W) : okW W m regA f := by
  zvmyk at *
  simp only [regA, okW, okWI, regI, K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m,
    c2m6, iL, iT, cE1, iG, iO, cm, cTop, iB, sw, Machine.upd_same, ne_eq, Machine.upd_other,
    Nat.reduceAdd, Nat.reduceEqDiff, not_false_eq_true, and_true, true_and]
  omega
set_option maxRecDepth 20000 in
theorem regA_val :
    regB m regA f K0 = 0 ∧ regB m regA f K1 = 1 ∧ regB m regA f K6 = 6 ∧
    regB m regA f K4 = 4 ∧ regB m regA f K5 = 5 ∧ regB m regA f K2 = 2 ∧
    regB m regA f K3 = 3 ∧ regB m regA f cGW = f ztfg ∧ regB m regA f cN1 = f ztna ∧
    regB m regA f cNW = f zthg ∧ regB m regA f cLL = f ztddn ∧
    regB m regA f cLD = f ztcdx ∧ regB m regA f cLE = f ztddn + f ztcdx ∧
    regB m regA f c2m = f zthy - f ztcwo ∧ regB m regA f c2m6 = f zthy - f ztxr ∧
    regB m regA f iL = f ztyl + f ztbsy ∧
    regB m regA f cE1 = f zthg - ztwps + f ztcdx ∧
    regB m regA f iG = f ztfg + ztwps ∧
    regB m regA f iO = f ztbca + f zthg - f ztfg ∧
    regB m regA f cm = m ztzlp ∧ regB m regA f cTop = m ztxob ∧
    regB m regA f iB = m ztzlq := by
  trivial
theorem regA_other {r : ℕ} (hr : r < sw 610 ∨ sw 705 ≤ r) :
    regB m regA f r = f r := by
  apply regB_other
  zug
  simp only [regA, List.mem_cons, List.not_mem_nil, or_false] at hi
  simp only [sw] at hr
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [dstI, K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m, c2m6, iL, iT,
    cE1, iG, iO, cm, cTop, iB, sw] <;> omega

/-! ## The tests -/

/-- `cGL := (gW + Lst) mod n` (one conditional subtraction). -/
def glS : Stmt := .ifLtN iG zthg (.instr (.copyN cGL iG)) (.instr (.subN cGL iG zthg))

/-- `iO := lOff = (sw 45 + n - gW) mod n`. -/
def offS : Stmt := .ifLtN iO zthg .skip (.instr (.subN iO iO zthg))

/-- `cB1 := b₁`. -/
def b1S : Stmt := .ifLtN iL iO (.instr (.subN cB1 ztna ztxr)) (.instr (.copyN cB1 ztbuy))

/-- `cS := sideS` of `C₂` from the orientation bit. -/
def sideSS : Stmt :=
  .ifLtN iB K1 ztncf
    (.ifLtN K1 iB ztncf (.instr (.copyN cS cTop)))

/-- The tests. -/
def stmtB : Stmt := .seq glS (.seq offS (.seq b1S sideSS))

/-- **The first part of the initialisation.** -/
def initRA : Stmt := .seq (block regA) stmtB

/-- A conditional register update (two branches). -/
theorem exec_ite_upd {a b r : ℕ}
    {i j : Instr} {u v : ℕ}
    (hi : Exec P W ztbgj c { c with nreg := upd c.nreg r u } 1)
    (hj : Exec P W ztuvl c { c with nreg := upd c.nreg r v } 1) :
    Exec P W (.ifLtN a b ztbgj ztuvl) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg b then u else v) }
      (if c.nreg a < c.nreg b then 2 else 3) := by
  zubjy
  · zumzf; tauto
  · zumzf; exact .ifLtN_false h hj
theorem glS_exec (hw : WordsBounded W c) :
    ∃ k, Exec P W glS c { c with nreg := upd c.nreg cGL (if c.nreg iG < c.nreg (sw 35) then c.nreg iG else c.nreg iG - c.nreg (sw 35)) } k ∧
      k ≤ 3 := by
  refine ⟨_, exec_ite_upd ztbim ztbbq, by_grind⟩
theorem offS_exec (hw : WordsBounded W c) :
    ∃ k, Exec P W offS c { c with nreg := upd c.nreg iO (if c.nreg iO < c.nreg (sw 35) then c.nreg iO else c.nreg iO - c.nreg (sw 35)) } k ∧
      k ≤ 3 := by
  by_cases h : c.nreg iO < c.nreg zthg
  · refine ⟨1, ?_, by_omega⟩
    rw [ite_eq_left h, upd_eq_self]
    tauto
  · refine ⟨3, ?_, le_rfl⟩
    zubme
    exact .ifLtN_false h ztbbq
theorem b1S_exec (hw : WordsBounded W c) :
    ∃ k, Exec P W b1S c { c with nreg := upd c.nreg cB1 (if c.nreg iL < c.nreg iO then c.nreg (sw 33) - c.nreg (sw 91) else c.nreg (sw 46)) } k ∧
      k ≤ 3 :=
  ⟨_, exec_ite_upd ztbbq ztbim, by_grind⟩
theorem sideSS_exec (hw : WordsBounded W c) :
    ∃ k, Exec P W sideSS c { c with nreg := upd c.nreg cS (if c.nreg iB = c.nreg K1 then c.nreg cTop else c.nreg c2m - c.nreg cTop) } k ∧ k ≤ 5 := by
  unfold sideSS
  by_cases h1 : c.nreg iB < c.nreg K1
  · refine ⟨2, ?_, by_omega⟩
    zufa
    exact .ifLtN_true h1 ztbbq
  · by_cases h2 : c.nreg K1 < c.nreg iB
    · refine ⟨4, ?_, by_omega⟩
      zufa
      exact .ifLtN_false h1 (.ifLtN_true h2 ztbbq)
    · refine ⟨5, ?_, le_rfl⟩
      zubek
      exact .ifLtN_false h1 (.ifLtN_false h2 ztbim)

/-! ## The first part, at the register level -/

/-- The register values after `initRA`. -/
def fIA (m f : ℕ → ℕ) : ℕ → ℕ :=
  let R := regB m regA f
  let R₁ := upd R cGL (if R iG < R zthg then R iG else R iG - R zthg)
  let R₂ := upd R₁ iO (if R₁ iO < R₁ zthg then R₁ iO else R₁ iO - R₁ zthg)
  let R₃ := upd R₂ cB1 (if R₂ iL < R₂ iO then R₂ ztna - R₂ ztxr else R₂ ztbuy)
  upd R₃ cS (if R₃ iB = R₃ K1 then R₃ cTop else R₃ c2m - R₃ cTop)
theorem initRA_exec_regs (hw : WordsBounded W c)
    (hok : okW W c.nmem regA c.nreg) :
    ∃ k, Exec P W initRA c { c with nreg := fIA c.nmem c.nreg } k ∧ k ≤ 41 := by
  have e₀ := exec_regB (P := P) regA hw hok
  set c₁ : Config := { c with nreg := regB c.nmem regA c.nreg } with hc₁
  obtain ⟨k₁, e₁, hk₁⟩ := glS_exec (P := P) e₀.wb_right
  obtain ⟨k₂, e₂, hk₂⟩ := offS_exec (P := P) e₁.wb_right
  obtain ⟨k₃, e₃, hk₃⟩ := b1S_exec (P := P) e₂.wb_right
  obtain ⟨k₄, e₄, hk₄⟩ := sideSS_exec (P := P) e₃.wb_right
  exact ⟨_, .seq e₀ ztwri, by simp only [regA] at *; simp; omega⟩
set_option maxRecDepth 20000 in
/-- The values of `fIA`. -/
theorem fIA_val :
    fIA m f K0 = 0 ∧ fIA m f K1 = 1 ∧ fIA m f K6 = 6 ∧ fIA m f K4 = 4 ∧ fIA m f K5 = 5 ∧
    fIA m f K2 = 2 ∧ fIA m f K3 = 3 ∧ fIA m f cGW = f ztfg ∧ fIA m f cN1 = f ztna ∧
    fIA m f cNW = f zthg ∧ fIA m f cLL = f ztddn ∧ fIA m f cLD = f ztcdx ∧
    fIA m f cLE = f ztddn + f ztcdx ∧ fIA m f c2m = f zthy - f ztcwo ∧
    fIA m f c2m6 = f zthy - f ztxr ∧
    fIA m f cE1 = f zthg - ztwps + f ztcdx ∧
    fIA m f cGL = (if f ztfg + ztwps < f zthg
      then f ztfg + ztwps
      else f ztfg + ztwps - f zthg) ∧
    fIA m f cB1 = (if f ztyl + f ztbsy <
        (if f ztbca + f zthg - f ztfg < f zthg then f ztbca + f zthg - f ztfg
          else f ztbca + f zthg - f ztfg - f zthg)
      then f ztna - f ztxr else f ztbuy) ∧
    fIA m f cm = m ztzlp ∧ fIA m f cTop = m ztxob ∧
    fIA m f cS = (if m ztzlq = 1 then m ztxob
      else (f zthy - f ztcwo) - m ztxob) := by
  have hv := regA_val m f
  have o : ∀ q, q < sw 610 ∨ sw 705 ≤ q → regB m regA f q = f q := fun q hq => regA_other m f hq
  have o35 := o zthg by_decide
  have o33 := o ztna by_decide
  have o91 := o ztxr by_decide
  have o46 := o ztbuy by_decide
  obtain ⟨v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vL, vE, vG, vO', vm,
    vt, vB⟩ := hv
  zulsb
  simp only [K0, K1, K2, K3, K4, K5, K6, cGW, cN1, cNW, cLL, cLD, cLE, c2m, c2m6, iL, cE1, iG,
    iO, cm, cTop, iB, cGL, cB1, cS, sw, Nat.reduceAdd] at *
  simp only [Machine.upd_same, ne_eq, Machine.upd_other, Nat.reduceEqDiff, not_false_eq_true,
    o35, o33, o91, o46, v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vL, vE,
    vG, vO', vm, vt, vB, true_and]
  grind

/-! ## The first part, for the junction -/

/-- One conditional subtraction is the remainder below `2 n`. -/
theorem ite_sub_mod {x n : ℕ} (h : x < 2 * n) : ztkws = x % n := by
  zulsr
  · exact (Nat.mod_eq_of_lt h').symm
  · zul
theorem rlen_le : Lst J ≤ 2 * J.m₂ + 7 := by
  zupcc; unfold rlen; grind
theorem lL1_le : lL1 J ≤ 2 * J.m₁ + 7 := by
  have := tpos_lt J.left J.m₁
  have hm : ztcql := rfl
  zumth
theorem lδ_le : lδ J ≤ 7 := by
  unfold lδ; grind
set_option maxRecDepth 20000 in
/-- **The first part of the initialisation**: the constants, `MapK`, `cGW` and the constants of
the classification except the top of `C₁`, from the stage-0 state.  Only `sw 610 … 704` change. -/
theorem initRA_exec {H : Host} {J : Merge.Junction}
    (hw : WordsBounded W c) (h0 : St0S P c H J) (hWn : 2 * (chainModel J.whole).W.n ≤ W) :
    ∃ c' k, Exec P W initRA c c' k ∧ k ≤ 41 ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ r, (r < sw 610 ∨ sw 705 ≤ r) → c'.nreg r = c.nreg r) ∧
      Consts c' ∧ MapK J c' ∧ c'.nreg cGW = gW J ∧ c'.nreg c2m = 2 * J.right.m ∧
      c'.nreg cm = J.right.m ∧ c'.nreg cTop = J.right.topIdx ∧
      c'.nreg cS = J.right.sideS J.right.sideBeta ∧ c'.nreg c2m6 = 2 * J.right.m + 6 := by
  obtain ⟨h90, h91, h92, h93, -, -, -, -, d21, w21, -, -, hR, hL, h33, h34, h35, -⟩ := h0
  have r0 : ztxbt := by simpa [cstR] using hR 0 by_norm_num
  have r2 : c.nreg ztyl = rL1 J := by simpa [cstR] using hR 2 by_norm_num
  have r3 : c.nreg ztbsy = rL2 J := by simpa [cstR] using hR 3 by_norm_num
  have l0 : ztxbs := by
    simpa [cstL] using hL 0 by_norm_num
  have l1 : c.nreg ztbuy = 6 + tpos J.left J.m₁ := by simpa [cstL] using hL 1 by_norm_num
  have l2 : c.nreg ztddn = lL1 J := by simpa [cstL] using hL 2 by_norm_num
  have l4 : c.nreg ztcdx = lδ J := by simpa [cstL] using hL 4 by_norm_num
  have hn : ztlh := cm_n _
  have hn₁ : ztbvd := cm_n _
  zucz
  have hm₁ : ztcql := rfl
  have hm₂ : ztdjs := rfl
  have t0 := tpos_lt J.whole J.m₁
  have t1 := tpos_lt J.whole ztbv
  have hLst : Lst J = rL1 J + rL2 J := rfl
  have hLs := rlen_le J
  have hll := lL1_le J
  have hld := lδ_le J
  have one₁ := J.one_le_m₁
  have hd21 : c.nreg _ + 5 ≤ c.nreg ALLOC := w21.1
  zueqh
  have hok : okW W c.nmem regA c.nreg := regA_ok _ _ by_omega
    by_omega by_omega by_omega
    by_omega by_omega by_omega
  obtain ⟨k, ex, hk⟩ := initRA_exec_regs (P := P) hw hok
  obtain ⟨v0, v1, v6, v4, v5, v2, v3, vgw, vn1, vnw, vll, vld, vle, v2m, v2m6, vE, vG, vB1, vm,
    vt, vS⟩ := fIA_val c.nmem c.nreg
  have hHm : c.nmem _ = J.right.m := d21.2.2.2.1
  have hHt : c.nmem _ = J.right.topIdx := d21.2.2.2.2.1
  have hHb : c.nmem _ = 1 ↔ J.right.sideBeta = true := d21.2.2.2.2.2
  refine ⟨_, k, ex, hk, rfl, rfl, rfl, rfl, fun r hr => ?_, ⟨v0, v1, v6, v4, v5, v2, v3⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · zulsb
    simp only [cGL, iO, cB1, cS, sw] at hr ⊢
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      upd_other _ _ _ by_omega]
    exact regA_other _ _ ztdzc
  · -- b₁
    show fIA c.nmem c.nreg cB1 = b₁ J
    rw [vB1, r2, r3, l0, h35, r0, h33, h91, l1, ← hLst]
    unfold b₁
    have hO : (if 6 + tpos J.whole ztbv + ztcsi -
          ztve < 2 * J.whole.m + 7
        then 6 + tpos J.whole ztbv + ztcsi - ztve
        else 6 + tpos J.whole ztbv + ztcsi - ztve -
          ztcsi) = lOff J := by
      rw [ite_sub_mod by_omega]
      unfold lOff dOf
      zubdb
    grind
  · grind
  · show fIA c.nmem c.nreg cE1 = E₁ J
    rw [vE, h35, r2, r3, l4]
    unfold E₁
    omega
  · grind
  · grind
  · show fIA c.nmem c.nreg cGL = _
    rw [vG, r0, r2, r3, h35, ite_sub_mod by_omega, hn, hLst]
    rfl
  · grind
  · grind
  · show fIA c.nmem c.nreg cGW = _
    rw [vgw, r0]; rfl
  · grind
  · grind
  · grind
  · show fIA c.nmem c.nreg cS = _
    rw [vS, hHt, h34, h92]
    unfold Chain.sideS
    grind
  grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def iE : ℕ := sw 705
def iH : ℕ := sw 706
def iY : ℕ := sw 707
def iA : ℕ := sw 710
def iV : ℕ := sw 711
set_option hygiene false in
/-- Register arithmetic on the named registers of the initialisation. -/
macro "swoInit2" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only [iL, iT, iG, iE, iH, iY, iA, iV,
  iO, iB, MD₁, CD₁, K0, K1, K2, K3, K4, K5, K6, ALLOC, cT1, TBR, TLR, cTB, sw] at *; omega))

/-! ## Frames -/

/-- A run step from its own start is a frame of `ioBands`. -/
theorem frame_of_irs {W : ℕ} {c c' : Config} {k : ℕ} (hI : IInv W c c') (hf : IFr c c' k) :
    Frame ioBands c c' k :=
  ⟨hf.1, hf.2.1, hI.hm, hI.hrm, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

/-- A step changing only registers of `ioBands` (not the allocator) is a frame. -/
theorem frame_regs {c c' : Config} (k : ℕ) (hr : ∀ r, bandOf r ∉ ioBands → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : Frame ioBands c c' k := by
  have hA := hr ALLOC alloc_not_io
  exact ⟨by_simp_all, by_simp_all, by_simp_all,
    by simp_all, ho, by zvmze, by_omega⟩
theorem frame_ioB {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame (B ∪ B) c c' k) :
    Frame B c c' k := by
  simp_all

/-- Registers of the sweep's band are in `ioBands`. -/
theorem sw_io {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∈ ioBands := by
  zuecu

/-! ## The top of `C₁` -/

/-- The copy of the symbolic point. -/
def symCp : List Instr := [.copyN cT1 iY, .copyN (cT1 + 1) (iY + 1), .copyN (cT1 + 2) (iY + 2)]

/-- The symbolic point of the top of `C₁` into `cT1`. -/
def symS : Stmt :=
  .seq (block [.constN iE 6, .constN iH 0]) (.seq (callSym ztiw iE iH iY) (block symCp))
variable {P : Polygon}
set_option maxRecDepth 20000 in
/-- **The top of `C₁`**: a symbolic point in `cT1`; only the oracle bands, the allocator and
`sw 645 … 647`, `sw 705 … 709` change. -/
theorem symS_exec {W : ℕ} {c : Config} {J : Merge.Junction}
    (hw : WordsBounded W c) (hctx : ChainCtx P W c ztiw J.left)
    (hroom : c.nreg ALLOC + 31006 ≤ W) :
    ∃ c' k, Exec P W symS c c' k ∧ k ≤ 31011 ∧ Frame ioBands c c' k ∧
      (∃ s : SymPt, SymPtIn c' cT1 s ∧ s.Lt P.n ∧ s.eval zta = J.left.top) ∧
      ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ztfty →
        (r < sw 705 ∨ sw 709 < r) → c'.nreg r = c.nreg r := by
  zuhxu
  have e₁ := exec_regB (P := P) [.constN iE 6, .constN iH 0] hw
    (by simp only [okW, okWI]; simp_all)
  set c₁ : Config := { c with nreg := regB c.nmem [.constN iE 6, .constN iH 0] c.nreg } with hc₁
  zuka
  have q1 : ∀ r, r ≠ iE → r ≠ iH → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    zunwy; simp_all
  have qE : c₁.nreg iE = 6 := by
    rfl
  have qH : c₁.nreg iH = 0 := by_rfl
  have hI₁ : IInv W c₁ c₁ := ⟨hw₁, by_omega, le_rfl, by_omega, by_simp_all⟩
  have hctx₁ : ztrfk :=
    hctx.transport (q1 _ (by swoInit2) (by swoInit2)) by_simp_all
      by_rfl
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := q1 _ (by swoInit2)
    (by swoInit2)
  have hm1 := J.left.one_le
  have hpar : (chainModel J.left).param zta ztbcw = 0 := rfl
  obtain ⟨c₂, k₂, e₂, hk₂, hI₂, hf₂, ⟨s, hs, hsl, hse⟩, hk2, -, -⟩ :=
    callSym_irs (P := P) (re := iE) (rh := iH) (o := iY) hI₁ hctx₁
      (by swoInit2) (by swoInit2) (by rw [qE])
      by_omega (by rw [qE, qH]; exact ⟨by_simp, by_simp,
        Nat.zero_le _⟩)
      by_simp_all by_omega
  rw [qE, qH] at hse
  have hpos : (chainModel J.left).pos zta ztbcw = J.left.top := by
    show Chazelle.Chain.sidePt _ _ _ = _
    rw [hpar, Chazelle.Chain.sidePt_zero, walk_vtx_six]
  zvnbl at hse
  zuja
  have e₃ := exec_regB (P := P) symCp hw₂ (by
    trivial)
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem symCp c₂.nreg } with hc₃
  have q3 : ∀ r, ztfty → c₃.nreg r = c₂.nreg r := fun r hr => by
    simp only [hc₃, symCp, regB, regI, cT1, sw] at hr ⊢
    zucud
  refine ⟨c₃, 2 + ztocj, .seq e₁ ztcr, by_omega, ?_, ⟨s, ?_, hsl, hse⟩, ?_⟩
  · have f₁ := frame_regs 2 (fun r hr => q1 r
      ztwmm
      ztwmm)
      rfl rfl rfl rfl
    have f₂ := frame_of_irs hI₂ hf₂
    have f₃ := frame_regs 3 (fun r hr => q3 r (by
      zumv
      exact hr (sw_io (by swoInit2) (by swoInit2)))) rfl rfl rfl rfl
    exact frame_ioB (frame_ioB (f₁.trans (f₂.trans f₃)))
  · tauto
  · intro r hr hrA h1 h2
    rw [q3 r h1, hk2 r hr (by swoInit2) hrA]
    exact q1 r (by swoInit2) (by swoInit2)

/-! ## The model descriptor of `C₁` -/

/-- The head: `MD₁ := ALLOC`, `CD₁ := ALLOC + 1`, `0` at `MD₁`. -/
def mdHead : List Instr := [.copyN MD₁ ALLOC, .addN CD₁ ALLOC K1, .storeN MD₁ K0]

/-- Copy word `k` of the descriptor at `sw 20` to `CD₁ + k`. -/
def mdCpW (k : ℕ) : List Instr := [.addN iA ztiw k, .loadN iV iA, .addN iA CD₁ k, .storeN iA iV]

/-- **The model descriptor of `C₁`.** -/
def md1S : Stmt :=
  .seq ztvfg (.seq (block (mdCpW K0)) (.seq (block (mdCpW K1)) (.seq (block (mdCpW K2))
    (.seq (block (mdCpW K3)) (.seq (block (mdCpW K4)) (.instr (.addN ALLOC ALLOC K6)))))))

/-- The state during the copy: `j` words copied. -/
def MdInv (c : Config) (A S j : ℕ) (c' : Config) : Prop :=
  c'.nreg MD₁ = A ∧ c'.nreg CD₁ = A + 1 ∧ c'.nmem A = 0 ∧
    (∀ i, i < j → c'.nmem (A + 1 + i) = c.nmem ztbat) ∧
    zttp ∧
    (∀ r, r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
theorem mdCpW_step {W : ℕ} {c c₁ : Config} {A S j k : ℕ}
    (hw : WordsBounded W c₁) (hI : MdInv c A S j c₁) (hS : c.nreg ztiw = S)
    (hSA : S + 5 ≤ A) (hAW : A + 6 ≤ W) (hj : j < 5) (hk : c.nreg k = j)
    (hk1 : k ≠ MD₁) (hk2 : k ≠ CD₁) (hk3 : k ≠ iA) (hk4 : k ≠ iV) :
    ∃ c₂, Exec P W (block (mdCpW k)) c₁ c₂ 4 ∧ MdInv c A S ztl c₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  have n20 : c₁.nreg ztiw = S := by
    rw [h6 _ (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2), hS]
  have nk : c₁.nreg k = j := by_simp_all
  have e₁ := Exec.addN (P := P) hw iA ztiw k by_omega
  have e₂ := Exec.loadN (P := P) e₁.wb_right iV iA
  have e₃ := Exec.addN (P := P) e₂.wb_right iA CD₁ k (by
    zubi
    rw [upd_other _ _ _ (by swoInit2), upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ hk4, upd_other _ _ _ hk3, h2, nk]; omega)
  have e₄ := Exec.storeN (P := P) e₃.wb_right iA iV
  refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
    ztpxq))), ?_⟩
  have vA : ∀ v, upd ztwlb iA
      (ztwlb CD₁ +
        ztwlb k) iA = A + 1 + j := by
    zujbq
    rw [upd_same, upd_other _ _ _ (by swoInit2),
      upd_other _ _ _ (by swoInit2), upd_other _ _ _ hk4,
      upd_other _ _ _ hk3, h2, nk]
  have vV : ∀ v, upd ztwlb iA
      (ztwlb CD₁ +
        ztwlb k) iV = v := by
    zujbq
    rfl
  zubi
  rw [vA, vV, upd_same, n20, nk]
  have hsrc : c₁.nmem _ = c.nmem zthck := h5 _ by_omega
  refine ⟨?_, ?_, ?_, fun i hi => ?_, fun a ha => ?_, fun r r1 r2 r3 r4 => ?_, h7, h8, h9⟩ <;>
    zubi
  · tauto
  · tauto
  · rw [upd_other _ _ _ by_omega, h3]
  · rcases Nat.lt_or_ge i j with h | h
    · rw [upd_other _ _ _ by_omega, h4 i h]
    · rw [show i = j by omega, upd_same, hsrc]
  · rw [upd_other _ _ _ by_omega, h5 a ha]
  · rw [upd_other _ _ _ r3, upd_other _ _ _ r4, upd_other _ _ _ r3, h6 r r1 r2 r3 r4]
set_option maxRecDepth 20000 in
theorem mdHead_exec {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (k0 : c.nreg K0 = 0) (k1 : c.nreg K1 = 1) (hW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c₁ k, Exec P W ztvfg c c₁ k ∧ k = 3 ∧
      MdInv c ztm ztxwd 0 c₁ := by
  unfold mdHead MdInv
  simp only [MD₁, CD₁, K0, K1, ALLOC, iA, iV, sw, Nat.reduceAdd] at *
  exec_block
  · config_simp; omega
  · refine ⟨rfl, by config_simp, by_simp_all, by_simp_all,
      by omega, fun a ha => ?_, fun r h1 h2 _ _ => ?_,
      rfl, rfl, rfl⟩
    · config_simp; zumya
    simp_all
set_option maxRecDepth 20000 in
/-- **The model descriptor of `C₁`** at the allocator `A`: `0` at `A`, the five words of the
descriptor at `sw 20` at `A + 1 …`; `MD₁ = A`, `CD₁ = A + 1`, the allocator at `A + 6`. -/
theorem md1S_exec {W : ℕ} {c : Config} (hw : WordsBounded W c) (hK : Consts c)
    (hS : c.nreg ztiw + 5 ≤ c.nreg ALLOC) (hW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W md1S c c' k ∧ k = 24 ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      c'.nreg MD₁ = c.nreg ALLOC ∧ c'.nreg CD₁ = c.nreg ALLOC + 1 ∧ c'.nmem ztm = 0 ∧
      (∀ i, i < 5 → c'.nmem (c.nreg ALLOC + 1 + i) = c.nmem ztzkw) ∧
      zth ∧
      (∀ r, r ≠ ALLOC → r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuch
  zujq
  set S := c.nreg _ with hSd
  obtain ⟨c₁, kH, eH, hkH, I₁⟩ := mdHead_exec (P := P) hw k0 k1 hW
  have hSA := hS
  have nk : ∀ q, (q = K0 ∨ q = K1 ∨ q = K2 ∨ q = K3 ∨ q = K4) →
      q ≠ MD₁ ∧ q ≠ CD₁ ∧ q ≠ iA ∧ q ≠ iV := by
    rintro q (rfl | rfl | rfl | rfl | rfl) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> swoInit2
  obtain ⟨c₂, e₄, I₂⟩ := mdCpW_step (P := P) eH.wb_right I₁ rfl hSA by_omega by_norm_num k0
    (nk K0 by_simp).1 (nk K0 by_simp).2.1 (nk K0 by_simp).2.2.1 (nk K0 by_simp).2.2.2
  obtain ⟨c₃, e₅, I₃⟩ := mdCpW_step (P := P) e₄.wb_right I₂ rfl hSA by_omega by_norm_num k1
    (nk K1 by_simp).1 (nk K1 by_simp).2.1 (nk K1 by_simp).2.2.1 (nk K1 by_simp).2.2.2
  obtain ⟨c₄, e₆, I₄⟩ := mdCpW_step (P := P) e₅.wb_right I₃ rfl hSA by_omega by_norm_num k2
    (nk K2 by_simp).1 (nk K2 by_simp).2.1 (nk K2 by_simp).2.2.1 (nk K2 by_simp).2.2.2
  obtain ⟨c₅, e₇, I₅⟩ := mdCpW_step (P := P) e₆.wb_right I₄ rfl hSA by_omega by_norm_num k3
    (nk K3 by_simp).1 (nk K3 by_simp).2.1 (nk K3 by_simp).2.2.1 (nk K3 by_simp).2.2.2
  obtain ⟨c₆, e₈, I₆⟩ := mdCpW_step (P := P) e₇.wb_right I₅ rfl hSA by_omega by_norm_num k4
    (nk K4 by_simp).1 (nk K4 by_simp).2.1 (nk K4 by_simp).2.2.1 (nk K4 by_simp).2.2.2
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := I₆
  have gA : c₆.nreg ALLOC = A := g6 _ (by swoInit2)
    (by swoInit2) (by swoInit2) (by swoInit2)
  have g6' : c₆.nreg K6 = 6 := by
    rw [g6 _ (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2), k6]
  have e₉ := Exec.addN (P := P) e₈.wb_right ALLOC ALLOC K6 by_omega
  refine ⟨_, _, .seq eH (.seq e₄ (.seq e₅ (.seq e₆ ztncq))), by_omega, ?_, ?_, ?_,
    g3, g4, g5, fun r h0 h1 h2 h3 h4 => ?_, g7, g8, g9⟩
  · zucac
  · tauto
  · tauto
  · simp only; rw [upd_other _ _ _ h0, g6 r h1 h2 h3 h4]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def iX : ℕ := sw 712
def iN : ℕ := sw 713
def iP : ℕ := sw 714
set_option hygiene false in
/-- Register arithmetic on the named registers of the table. -/
macro "swoInit3" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only [iX, iN,
  iP, iA, iV, K1, ALLOC, TBR, TLR, sw] at *; omega))

/-- The head of the table: `TBR := ALLOC`, `TLR := 0`, `x := 1`, `N := a₁ + a₂ + 1`. -/
def tabHead : List Instr :=
  [.copyN TBR ALLOC, .constN TLR 0, .constN iX 1, .addN iA ztea K1, .loadN iN iA,
    .addN iA ztbz K1, .loadN iV iA, .addN iN iN iV, .addN iN iN K1]

/-- The body: `T[TLR] := x`, `x := 2 x`, `TLR := TLR + 1`. -/
def tabBodyI : List Instr :=
  [.addN iP TBR TLR, .storeN iP iX, .addN iX iX iX, .addN TLR TLR K1]

/-- **The table of powers.** -/
def tabS : Stmt :=
  .seq (block tabHead) (.seq (.whileLtN iX iN (block tabBodyI)) (.instr (.addN ALLOC ALLOC TLR)))
variable {P : Polygon} {W : ℕ}
/-- **A loop with an exact count**: an invariant indexed by the number `j` of iterations done,
the test true exactly while `j < L`, a body of cost exactly `B`. -/
theorem while_exact {a b : ℕ} {body : Stmt} (I : ℕ → Config → Prop)
    (L B : ℕ) (htest : ∀ j d, I j d → ztlmx)
    (hwb : ∀ j d, I j d → WordsBounded W d)
    (hbody : ∀ j d, I j d → j < L → ∃ d', Exec P W body d d' B ∧ I ztl d') :
    ∀ j d, I j d → j ≤ L →
      ∃ d', Exec P W ztpx d d' (zthb * ztnmd + 2) ∧ I L d' := by
  zulnb
  induction hn : L - j generalizing j d with
  | zero =>
    zugmm

    exact ⟨d, .whileLtN_false (fun h => absurd ((htest j d hI).1 h) ztkal) (hwb j d hI),
      hI⟩
  | succ n ih =>
    zukdh
    obtain ⟨d₁, e₁, hI₁⟩ := hbody j d hI hlt
    obtain ⟨d', e', hI'⟩ := ih ztl d₁ hI₁ by_omega by_omega
    refine ⟨d', (Exec.whileLtN_true ((htest j d hI).2 hlt) e₁ e').cast by_ring, hI'⟩
set_option maxRecDepth 20000 in
theorem tabHead_val (m f : ℕ → ℕ) :
    regB m tabHead f TBR = f ALLOC ∧ regB m tabHead f TLR = 0 ∧ regB m tabHead f iX = 1 ∧
      (f K1 = 1 → regB m tabHead f iN = m ztzlo + m (f ztbz + 1) + 1) ∧
      ∀ r, r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → regB m tabHead f r = f r := by
  refine ⟨?_, ?_, ?_, fun h1 => ?_, fun r a b d e g i => ?_⟩
  all_goals simp only [tabHead, regB, regI, TBR, TLR, iX, iA, iN, iV, K1, ALLOC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  · simp only [K1, sw, Nat.reduceAdd] at h1; zvmwp
  · simp only [TBR, TLR, iX, iA, iN, iV, sw, Nat.reduceAdd] at a b d e g i
    simp_all
set_option maxRecDepth 20000 in
/-- **The table of powers**: base `A₀` (the allocator), length `L = ⌈log₂ (a₁ + a₂ + 1)⌉`. -/
theorem tabS_exec {c : Config} (hw : WordsBounded W c)
    (hK1 : c.nreg K1 = 1) (h3 : c.nreg ztea + 1 ≤ W) (h4 : c.nreg ztbz + 1 ≤ W)
    (hroom : c.nreg ALLOC + 2 * ztwkd + 4
      ≤ W) :
    ∃ c' k, Exec P W tabS c c' k ∧
      k = 6 * Nat.clog 2 ztwkd + 12 ∧
      c'.nreg TBR = c.nreg ALLOC ∧
      c'.nreg TLR = Nat.clog 2 ztwkd ∧
      c'.nreg ALLOC = c.nreg ALLOC + c'.nreg TLR ∧
      (∀ j, j < c'.nreg TLR → c'.nmem (c.nreg ALLOC + j) = 2 ^ j) ∧
      zth ∧
      (∀ r, r ≠ ALLOC → r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → r ≠ iP →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set a₁ := c.nmem ztyej with ha₁
  set a₂ := c.nmem ztyei with ha₂
  zuce
  set Lf := Nat.clog 2 (a₁ + a₂ + 1) with hLf
  have hLpow : a₁ + a₂ + 1 ≤ 2 ^ Lf := Nat.le_pow_clog by_norm_num _
  have hLle : Lf ≤ a₁ + a₂ + 1 := by
    zufnd

  -- the head
  obtain ⟨vB, vL, vX, vN, vo⟩ := tabHead_val c.nmem c.nreg
  have e₁ := exec_regB (P := P) tabHead hw (by
    simp only [tabHead, okW, okWI, regI, TBR, TLR, iX, iA, iN, iV, K1, ALLOC, sw, Nat.reduceAdd,
      upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, true_and, and_true]
    simp only [K1, sw, Nat.reduceAdd] at hK1 h3 h4 ha₁ ha₂
    grind)
  set c₁ : Config := { c with nreg := regB c.nmem tabHead c.nreg } with hc₁
  have n₁ : ∀ r, r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → c₁.nreg r = c.nreg r :=
    vo
  have g11 : ztcpf := by_tauto
  have gA : ztpmy :=
    n₁ _ (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3)
  have gB : c₁.nreg TBR = A₀ := vB
  have gN : c₁.nreg iN = a₁ + a₂ + 1 := vN hK1
  -- the loop
  let I : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg TLR = j ∧
    d.nreg iX = 2 ^ j ∧ ztgno ∧
    (∀ r, r ≠ iX → r ≠ iP → r ≠ TLR → d.nreg r = c₁.nreg r) ∧
    ztiuh ∧ d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧
    d.output = c₁.output
  have I₁ : I 0 c₁ := ⟨e₁.wb_right, vL, vX.trans (pow_zero 2).symm,
    fun t ht => absurd ht zthrl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  have hN : ∀ j d, I j d → d.nreg iN = a₁ + a₂ + 1 := fun j d h => by
    rw [h.2.2.2.2.1 _ (by swoInit3) (by swoInit3) (by swoInit3), gN]
  obtain ⟨c₂, e₂, w₂, hj, hx, htab, hr₂, hm₂, rr₂, rm₂, o₂⟩ :=
    while_exact (P := P) (W := W) (a := iX) (b := iN) (body := block tabBodyI) I Lf 4
      (fun j d h => by
        rw [h.2.2.1, hN j d h, hLf, Nat.lt_clog_iff_pow_lt by_norm_num])
      (fun j d h => h.1)
      (fun j d ⟨hwd, hj, hx, htab, hr, hm, rr, rm, o⟩ hjl => by
        have dB : d.nreg TBR = A₀ := by rw [hr _ (by swoInit3) (by swoInit3) (by swoInit3), gB]
        have d11 : d.nreg K1 = 1 := by rw [hr _ (by swoInit3) (by swoInit3) (by swoInit3), g11]
        have ht : 2 ^ j < a₁ + a₂ + 1 := by
          rw [← Nat.lt_clog_iff_pow_lt by_norm_num]; omega
        have hjL : j ≤ Lf := hjl.le
        have e₁ := Exec.addN (P := P) hwd iP TBR TLR by_omega
        have e₂ := Exec.storeN (P := P) e₁.wb_right iP iX
        have e₃ := Exec.addN (P := P) e₂.wb_right iX iX iX (by
          zubi
          rw [upd_other _ _ _ (by swoInit3), hx]; omega)
        have e₄ := Exec.addN (P := P) e₃.wb_right TLR TLR K1 (by
          zubi
          rw [upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3),
            upd_other _ _ _ (by swoInit3), hj, d11]; omega)
        refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃
          (Exec.block_cons e₄ ztpxq))), e₄.wb_right, ?_, ?_,
          fun t ht' => ?_, fun r a b c' => ?_, fun a ha => ?_, rr, rm, o⟩
        · zufb
          rw [upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3),
            upd_other _ _ _ (by swoInit3), hj, d11]
        · zubi
          rw [upd_other _ _ _ (by swoInit3), upd_same, upd_other _ _ _ (by swoInit3), hx, pow_succ]; ring
        · zufb
          rw [upd_other _ _ _ (show iX ≠ iP by swoInit3), dB, hj]
          zuidr
          · zugxh
          · rw [show t = j by omega, upd_same, hx]
        · zubi
          rw [upd_other _ _ _ c', upd_other _ _ _ a, upd_other _ _ _ b]; grind
        · zubi
          rw [upd_other _ _ _ (by simp only [upd_same]; omega)]
          grind)
      0 c₁ I₁ ztbg
  -- the end of the loop
  have g9 : c₂.nreg ALLOC = A₀ := by rw [hr₂ _ (by swoInit3) (by swoInit3) (by swoInit3), gA]
  have e₃ := Exec.addN (P := P) w₂ ALLOC ALLOC TLR by_omega
  refine ⟨_, _, .seq e₁ ztcr, ?_, ?_, ?_, ?_, fun t ht => ?_, fun a ha => ?_,
    fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, by_omega, by_omega,
    by omega⟩
  · simp only [tabHead, List.length_cons, List.length_nil]; omega
  · simp only; rw [upd_other _ _ _ (by swoInit3), hr₂ _ (by swoInit3) (by swoInit3) (by swoInit3), gB]
  · tauto
  · simp only [upd_same]; rw [upd_other _ _ _ (by swoInit3), hj, g9]
  · zubi
    zumpt
    rw [upd_other _ _ _ (by swoInit3), hj] at ht
    grind
  · grind
  · zubi
    rw [upd_other _ _ _ h0, hr₂ r h3 h7 h2]
    grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
set_option hygiene false in
/-- Register arithmetic on all named registers of the initialisation. -/
macro "swoInit4" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [iX, iN, iP, iA, iV, iE, iH, iY,
                iL, iT, iG, iO, iB, MD₁, CD₁, K0, K1, K2, K3, K4, K5, K6, ALLOC, TBR, TLR, cTB,
                cT1, sw] at *; omega))

/-- **The initialisation of `sweepEvSpec`'s program.** -/
def initE : Stmt :=
  .seq initRA (.seq symS (.seq md1S (.seq tabS (.instr (.copyN cTB ALLOC)))))

/-- The facts established by the initialisation. -/
structure InitRes (P : Polygon) (J : Merge.Junction) (c c₀ : Config) : Prop where
  keep : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → (r < sw 600 ∨ sw 715 ≤ r) →
    c₀.nreg r = c.nreg r
  mem : ∀ a, a < c.nreg ALLOC → c₀.nmem a = c.nmem a
  hA : c.nreg ALLOC ≤ c₀.nreg MD₁
  hK : Consts c₀
  hM : MapK J c₀
  hO : OrgK P J c₀
  hgw : c₀.nreg cGW = gW J
  md0 : c₀.nmem ztmhy = 0
  mdc : ∀ i, i < 5 → c₀.nmem (c₀.nreg MD₁ + 1 + i) = c.nmem ztzkw
  hcd : c₀.nreg CD₁ = c₀.nreg MD₁ + 1
  hTBR : c₀.nreg TBR = c₀.nreg MD₁ + 6
  hTLR : c₀.nreg TLR =
    Nat.clog 2 ztwkd
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem zthwa = 2 ^ j
  hAl : c₀.nreg ALLOC = c₀.nreg TBR + c₀.nreg TLR
  hTA : c₀.nreg cTB = c₀.nreg ALLOC

/-- A normal form protected below `E` has its header below `E`. -/
theorem nfWithin_lt' {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) : B + 1 < E := by
  zukr
  have := (h (upd m ztvf (N.arcs.length + 1)) (fun a ha => by
    zumya)).2.1
  simp_all
variable {P : Polygon} {W : ℕ} {c : Config} {H : Host} {J : Merge.Junction}
/-- The number of edges of a chain with a well-formed descriptor. -/
theorem chain_m_le' {E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C) : 2 * C.m + 2 ≤ 128 * P.n := by
  zucxs

  have h2 := NFLoc.chain_n_le hC hl hHW
  omega

/-- The walk of `C` fits twice in the word bound. -/
theorem walk_two_le {W E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C) (hW : hostWords P.n ≤ W) :
    2 * (chainModel C).W.n ≤ W := by
  have := chain_m_le' hwf hC
  zvokr; unfold hostWords at hW; omega

/-- The chain context of a descriptor of a junction chain (host regular by `JunctionWF`). -/
theorem chainCtx_of
    {d : ℕ} {C : Chain} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hP : C.P.Simple)
    (hJ : JunctionAt c.nmem ztxcj ztxck ztwzq zta H J)
    (hJW : JunctionWF P ztm c.nmem ztxcj ztxck ztwzq)
    (hd : ChainDescAt c.nmem ztqir zta H C) (hw : ChainWF P ztm c.nmem ztqir) :
    ChainCtx P W c d C := by
  have := chain_m_le' hw hd
  zudwh
  exact ⟨hG, by_tauto, hw, ⟨H, hd, hJW.2.2.2 H hJ.2.2.1⟩, hP, by_omega⟩
set_option maxRecDepth 20000 in
/-- **The run of the initialisation** from the stage-0 state. -/
theorem initE_exec
    (hw : WordsBounded W c) (h0 : St0S P c H J) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hP : J.P.Simple) (h3 : c.nreg ztea + 1 < c.nreg ALLOC)
    (h4 : c.nreg ztbz + 1 < c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 31100 +
      2 * ztwkd ≤ W) :
    ∃ c₀ k, Exec P W initE c c₀ k ∧
      k ≤ 31100 + 6 * Nat.clog 2 ztwkd ∧
      Frame ioBands c c₀ k ∧ InitRes P J c c₀ := by
  set a₁ := c.nmem _ with ha₁
  set a₂ := c.nmem _ with ha₂
  have h0' := h0
  obtain ⟨h90, h91, h92, h93, hJ, hJW, d20, w20, d21, w21, -⟩ := h0'
  have hWn := walk_two_le hJW.2.2.1 hJ.2.2 hWh
  -- part A
  obtain ⟨c₁, kA, eA, hkA, mA, rrA, rmA, oA, keepA, KA, MA, gwA, o2m, om, otop, oS, o2m6⟩ :=
    initRA_exec (P := P) hw h0 hWn
  have hA₁ : ztdc := keepA _ by_decide
  have fA := frame_regs kA (fun r hr => keepA r (by
    by_contra h; exact hr (sw_io ztnwa ztnwa))) rrA mA rmA oA
  -- the top of `C₁`
  have k20 : c₁.nreg _ = c.nreg ztiw := keepA _ by_decide
  have hctx : ztrfk :=
    (chainCtx_of hG hWh hP hJ hJW d20 w20).transport k20 by_simp_all
      ztjqb
  obtain ⟨c₂, kS, eS, hkS, fS, ⟨s, hs, hsl, hse⟩, keepS⟩ :=
    symS_exec (P := P) eA.wb_right hctx by_omega
  have hA₂ := fS.2.2.2.2.2.2
  have hA₂' := fS.2.2.2.2.2.1
  have kS' := fun r h1 h2 h3 h4 =>
    keepS r ztsg ztu h3 h4
  -- the model descriptor
  have KS : Consts c₂ := by
    zuddx
    refine ztuv <;>
    [rw [← a]; rw [← b]; rw [← d]; zvmyr; rw [← f]; rw [← g]; rw [← i]] <;>
    exact kS' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)
  have k20' : c₂.nreg ztiw = c.nreg ztiw := by
    rw [kS' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2), k20]
  obtain ⟨c₃, kM, eM, hkM, aM, mdM, cdM, m0M, mcM, mlM, keepM, rrM, rmM, oM⟩ :=
    md1S_exec (P := P) eS.wb_right KS (by rw [k20']; have := w20.1; omega)
      by_omega
  have fM : Frame ioBands c₂ c₃ kM := ⟨fun r hb hr => by
      refine keepM r hr ?_ ?_ ?_ ?_ <;> rintro rfl <;> exact hb (sw_io (by swoInit2) (by swoInit2)),
    by grind, mlM, by_grind, oM, by_omega, by_omega⟩
  -- the table
  have kM' : ∀ r, 240000 ≤ r → r < 250000 → r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV →
      c₃.nreg r = c₂.nreg r := fun r h1 h2 a b d e => keepM r ztu a b d e
  have K1₃ : c₃.nreg K1 = 1 := by rw [kM' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)]; exact KS.2.1
  have s3 : c₃.nreg ztea = c.nreg ztea := by
    rw [kM' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2),
      kS' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2), keepA _ (by swoInit2)]
  have s4 : c₃.nreg ztbz = c.nreg ztbz := by
    rw [kM' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2),
      kS' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2), keepA _ (by swoInit2)]
  have mem₃ : ztblg := fun a ha => by
    rw [mlM a by_omega, fS.2.2.1 a by_omega, mA]
  have ea₁ : c₃.nmem (c₃.nreg ztea + 1) = a₁ := by_grind
  have ea₂ : c₃.nmem (c₃.nreg ztbz + 1) = a₂ := by_grind
  have hw₃ := eM.wb_right
  obtain ⟨c₄, kT, eT, hkT, tB, tL, tA, ttab, tmem, keepT, rrT, rmT, oT⟩ :=
    tabS_exec (P := P) hw₃ K1₃ by_omega
      by_omega by_omega
  rw [ea₁, ea₂] at hkT tL
  have fT : Frame ioBands c₃ c₄ kT := ⟨fun r hr hrA => by
      refine keepT r hrA ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rintro rfl <;>
        exact hr (sw_io (by swoInit4) (by swoInit4)),
    by grind, tmem, by_grind, oT, by_omega, by_omega⟩
  -- the table base
  have hw₄ := eT.wb_right
  have eC := Exec.copyN (P := P) hw₄ cTB ALLOC
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg cTB _ } with hc₅
  have fC : Frame ioBands c₄ c₅ 1 := frame_regs 1 (fun r hr => by
    zuotc; rw [upd_other _ _ _ (by rintro rfl; exact hr (sw_io (by swoInit2) (by swoInit2)))])
    rfl rfl rfl rfl
  have k5 : ∀ r, r ≠ cTB → c₅.nreg r = c₄.nreg r := fun r h => by
    zuotc; zuobr
  -- registers kept from part `A` on
  have keepR : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ztfty →
      (r < sw 700 ∨ sw 715 ≤ r) → r ≠ MD₁ → r ≠ CD₁ → r ≠ TBR → r ≠ TLR → r ≠ cTB →
      c₅.nreg r = c₁.nreg r := fun r ho hA h1 h2 a b d e f => by
    rw [k5 r f, keepT r hA d e (by rintro rfl; swoInit4) (by rintro rfl; swoInit4) (by rintro rfl; swoInit4)
      (by rintro rfl; swoInit4) (by rintro rfl; swoInit4), keepM r hA a b (by rintro rfl; swoInit2)
      (by rintro rfl; swoInit2), keepS r ho hA h1 (by swoInit2)]
  have kc : ∀ i, 610 ≤ i → i ≤ 660 → (i < 645 ∨ 647 < i) → i ≠ 650 → i ≠ 651 →
      c₅.nreg _ = c₁.nreg ztcdy := fun i h1 h2 h3 h4 h5 =>
    keepR _ (not_oracle_sw (by swoInit2) (by swoInit2)) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2) (by swoInit2) (by swoInit2)
  refine ⟨c₅, kA + (kS + (kM + (kT + 1))), .seq eA (.seq eS (.seq eM (.seq eT eC))), ?_,
    frame_ioB (fA.trans (frame_ioB (fS.trans (frame_ioB (fM.trans (frame_ioB (fT.trans fC))))))),
    ⟨fun r ho hA hr => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · omega
  · rw [keepR r ho hA (by swoInit2) (by swoInit2) (by rintro rfl; swoInit2) (by rintro rfl; swoInit2)
      (by rintro rfl; swoInit2) (by rintro rfl; swoInit2) (by rintro rfl; swoInit2)]
    exact keepA r (by swoInit2)
  · show c₄.nmem a = c.nmem a
    rw [tmem a by_omega, mem₃ a ha]
  · rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM]; omega
  · zuddx
    exact ⟨(kc 610 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans a,
      (kc 611 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans b,
      (kc 612 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans d,
      (kc 613 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans e,
      (kc 614 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans f,
      (kc 615 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans g,
      (kc 616 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans i⟩
  · obtain ⟨a, b, d, e, f, g, i, j⟩ := MA
    exact ⟨(kc 652 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans a,
      (kc 653 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans b,
      (kc 654 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans d,
      (kc 655 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans e,
      (kc 656 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans f,
      (kc 657 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans g,
      (kc 658 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans i,
      (kc 660 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans j⟩
  · refine ⟨(kc 640 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans o2m,
      (kc 641 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans om,
      (kc 642 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans otop,
      (kc 643 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans oS,
      (kc 644 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans o2m6,
      s, ?_, hsl, hse⟩
    have t : ∀ i, 645 ≤ i → i ≤ 647 → c₅.nreg _ = c₂.nreg _ := fun i h1 h2 => by
      rw [k5 (sw i) (by swoInit2), keepT (sw i) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
        (by swoInit4) (by swoInit4) (by swoInit4), keepM _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)]
    exact symPtIn_transport hs (t 645 by_norm_num by_norm_num)
      (t 646 by_norm_num by_norm_num) (t 647 by_norm_num by_norm_num)
  · exact (kc 659 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num).trans gwA
  · show c₄.nmem _ = 0
    rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM, tmem _ by_omega, m0M]
  · zug
    show c₄.nmem _ = _
    rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM, tmem _ by_omega, mcM i hi, k20', fS.2.2.1 _ (by
        have := w20.1; omega), mA]
  · rw [k5 CD₁ (by swoInit2), k5 MD₁ (by swoInit2), keepT CD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), mdM, cdM]
  · rw [k5 TBR (by swoInit2), k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), tB, aM, mdM]
  · rw [k5 TLR (by swoInit2), tL]
  · zun
    rw [k5 TLR (by swoInit2)] at hj
    rw [k5 TBR (by swoInit2), tB]
    exact ttab j hj
  · rw [k5 ALLOC (by swoInit2), k5 TBR (by swoInit2), k5 TLR (by swoInit2), tA, tB]
  rfl
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
@[expose] public section
def kN : ℕ := sw 2402
def kL : ℕ := sw 2403
/-- The gap regions: count `gN ≤ 2`, regions `gR`, `gR + 1`. -/
def gN : ℕ := sw 2440
def gR : ℕ := sw 2441
/-- The stop pointer (the first stop beyond the current key) and the done flag. -/
def sP : ℕ := sw 2450
def dF : ℕ := sw 2451

/-! ## E: the origins of one iteration -/

/-- The registers the enumeration writes besides those of `od`: `oK`, `oS` and the loop
registers `sw 2460 … 2479`. -/
def LR (r : ℕ) : Prop := r = oK ∨ r = oS ∨ (sw 2460 ≤ r ∧ r < sw 2480)

/-- The registers the enumeration reads (kept by `od`). -/
def ER (r : ℕ) : Prop :=
  r = kN ∨ ztdot ∨ r = gN ∨ r = gR ∨ r = gR + 1 ∨ r = sP ∨ r = sC ∨ r = aB

/-- The endpoint queries of the chords of region `r` of `N` (both ends). -/
def regO (N : NF) (r : ℕ) : Set ℕ :=
  {j | ∃ k ∈ (N.region r).chords, ∃ s, s ≤ 1 ∧ j = 2 * k + s}

/-- The parent field of the auxiliary record `i` (`k + 1` for the chord `k` of `N₂`, or `0`). -/
def parOf (c : Config) (i : ℕ) : ℕ := c.nmem (c.nreg aB + 5 * i + 4)

/-- The endpoint queries of the parents of the stops `sP` and `sP + 1` (both ends). -/
def parO (c : Config) : Set ℕ :=
  {j | ∃ i, (i = c.nreg sP ∨ i = c.nreg sP + 1) ∧ i < c.nreg sC ∧ 0 < parOf c i ∧
    ∃ s, s ≤ 1 ∧ j = 2 * (parOf c i - 1) + s}

/-- **The endpoint queries tried in one iteration**: the chords of the regions of the label list,
of the gap regions, and the parents of the next two stops. -/
def iterO (N : NF) (c : Config) : Set ℕ :=
  {j | ∃ i, i < min ztjsi 4 ∧ j ∈ regO N (c.nreg ztbuc)} ∪
    {j | ∃ i, i < min ztqiu 2 ∧ j ∈ regO N ztbagl} ∪ parO c

/-- **Task E: the origin enumeration**, generic in the per-origin statement `od` (cost `Kod`, run
with `oK = k`, `oS = s`, `k < K₂`, `s ≤ 1`) and the invariant `Inv O c` (`O` the processed
queries; stable under changes of the loop registers `LR`).  Cost
`(12 D + 8) (Kod + κO) + κO` (`D = c₀.nreg (sw 6)` bounds the chords of a region,
`GranSize`). -/
def OrgsTask : Prop :=
  ∃ (orgs : Stmt → Stmt) (κO : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    ∀ (od : Stmt) (Kod : ℕ) (Inv : Set ℕ → Config → Prop),
    (∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
      c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
      IRS P W c₀ od c Kod (fun c' => Inv ztxxm c' ∧
        ztwpx ∧
        ztvw)) →
    (∀ (O : Set ℕ) (c c' : Config), Inv O c → ztedk →
      c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output →
      Inv O c') →
    ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c →
      ztxrl →
      ztxrm →
      ztimp →
      c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c.nreg ALLOC + ztwqy ≤ W →
      IRS P W c₀ ztwbf c ztwqy
        ztmbh

/-! ## K: the next key -/

/-- The position of stop `i` (the stop records at `sB`, five words each). -/
def stopE (c : Config) (i : ℕ) : ℕ := c.nmem ztpaa
def stopH (c : Config) (i : ℕ) : ℕ := c.nmem ztmhc

/-- The labels of the auxiliary record `i` at `A` if it is anchored: `l₀, l₁` up to the count
`nl` (at most two). -/
def stopLabs (m : ℕ → ℕ) (A i : ℕ) : List ℕ :=
  if m ztjgj = 1 then (List.range (min (m ztgzo) 2)).map fun t => m (A + 5 * i + 2 + t)
  else []

/-- Appending a list of labels (`addL` each). -/
def addLs (l vs : List ℕ) : List ℕ := vs.foldl addL l

/-- The registers the next-key step may write (besides the oracle bands and the allocator). -/
def KR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = kN ∨ ztdot ∨ r = sP ∨ r = dF ∨ r = lC ∨
    ztfus ∨ ztgz ∨ ztcok

/-- **The post of the next-key step** from `c` to `c'`.  The candidates are the best candidate
`(bE, bH)` (if `bF = 1`), the stop `sP` (if `sP < sC`) and the window end `(wE, wH)` (if
`wX = 0`).  If there is none, `dF = 1` and only the scratch changes.  Otherwise `dF = 0`; the new
key `(kE, kH)` is a candidate of least offset `o'`; the stop pointer skips exactly the stops at
offset `o'`; the label list is the best candidate's (if at offset `o'`) followed by the labels of
the skipped anchored stops when one of these exists (`An`), and the old one otherwise; the log
record `(kE, kH, kN, kL … kL + 3)` is written at `lB + 7 lC` and `lC` is incremented. -/
def KeyOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ KR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧
  ((c.nreg bF ≠ 1 ∧ ¬ c.nreg sP < c.nreg sC ∧ c.nreg wX ≠ 0) →
    c'.nreg dF = 1 ∧ c'.nreg lC = c.nreg lC ∧ ztbgf) ∧
  ((c.nreg bF = 1 ∨ c.nreg sP < c.nreg sC ∨ c.nreg wX = 0) →
    c'.nreg dF = 0 ∧
    ((c.nreg bF = 1 ∧ c'.nreg kE = c.nreg bE ∧ c'.nreg kH = c.nreg bH) ∨
      (c.nreg sP < c.nreg sC ∧ c'.nreg kE = stopE c ztccy ∧
        c'.nreg kH = stopH c ztccy) ∨
      (c.nreg wX = 0 ∧ c'.nreg kE = c.nreg wE ∧ c'.nreg kH = c.nreg wH)) ∧
    (c.nreg bF = 1 →
      offK P J ztccp ztdco ≤ offK P J ztvo ztvp) ∧
    (c.nreg sP < c.nreg sC → offK P J ztccp ztdco ≤
      offK P J ztyrv ztyrw) ∧
    (c.nreg wX = 0 →
      offK P J ztccp ztdco ≤ offK P J ztmhd ztmhe) ∧
    c.nreg sP ≤ c'.nreg sP ∧ c'.nreg sP ≤ c.nreg sC ∧
    (∀ i, c.nreg sP ≤ i → i < c'.nreg sP →
      offK P J ztbjv ztbjw = offK P J ztccp ztdco) ∧
    (c'.nreg sP < c.nreg sC →
      offK P J (stopE c ztmfk) (stopH c ztmfk) ≠
        offK P J ztccp ztdco) ∧
    c'.nreg kN ≤ 4 ∧
    ((ztxig ∨
        ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧ c.nmem ztduc = 1) →
      lblOf c' kN kL = addLs
        (if c.nreg bF = 1 ∧ offK P J ztvo ztvp = offK P J ztccp ztdco
          then lblOf c bN bL else [])
        ((List.range' ztccy (c'.nreg sP - c.nreg sP)).flatMap
          ztzxz)) ∧
    (¬ (ztxig ∨
        ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧ c.nmem ztduc = 1) →
      lblOf c' kN kL = lblOf c kN kL ∧ c'.nreg kN = c.nreg kN) ∧
    c'.nreg lC = c.nreg lC + 1 ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC) = c'.nreg kE ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC + 1) = c'.nreg kH ∧
    c'.nmem (c.nreg lB + 7 * c.nreg lC + 2) = c'.nreg kN ∧
    (∀ i, i < 4 → c'.nmem (c.nreg lB + 7 * c.nreg lC + 3 + i) = c'.nreg ztbuc) ∧
    (∀ x, x < c.nreg ALLOC → ztfcr →
      c'.nmem x = c.nmem x))

/-- **Task K: the next key**, at a constant cost `κK`.  Hypotheses: the positions involved are
word-level (`PosW`), the stop records are sorted by offset with at most two at one offset, the
label lists have at most four labels, the stop and auxiliary arrays lie below the allocator, and
the log array has room for one more record (at or above the allocator of `c₀`). -/
def KeyTask : Prop :=
  ∃ (key : Stmt) (κK : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      PosW P J ztwe ztbhr →
      ztxbh →
      ztdav →
      ztwwt →
      (∀ i i', i ≤ i' → i' < c.nreg sC →
        offK P J ztbjv ztbjw ≤ offK P J ztkfo ztkfp) →
      (∀ i, i + 2 < c.nreg sC →
        offK P J ztbjv ztbjw < offK P J ztxyb ztxyc) →
      c.nreg sP ≤ c.nreg sC → c.nreg kN ≤ 4 → c.nreg bN ≤ 4 →
      c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC → c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c₀.nreg ALLOC ≤ c.nreg lB → c.nreg lB + 7 * ztllq ≤ c.nreg ALLOC →
      c.nreg ALLOC + κK ≤ W →
      IRS P W c₀ key c κK ztlew

/-! ## P: the table and the log array -/

/-- The registers the preparation may write (besides the oracle bands and the allocator). -/
def PR (r : ℕ) : Prop := r = lB ∨ r = lC ∨ ztfus

/-- **The post of the preparation**: the flags of the `2 K₂` table records at `cTB` are `0`, the
log array of `16 (K₁ + K₂ + 1)` records (count `lC = 0`) lies after the table, below the
allocator. -/
def PrepOut (N₁ N₂ : NF) (c c' : Config) : Prop :=
  (∀ j, j < 2 * N₂.nChords → c'.nmem ztbwv = 0) ∧
  c.nreg cTB + 6 * N₂.nChords ≤ c'.nreg lB ∧ c'.nreg lC = 0 ∧
  c'.nreg lB + 7 * (16 * ztks) ≤ c'.nreg ALLOC ∧
  ztbgf ∧
  (∀ r, bandOf r ∉ oracleBands → ¬ PR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task P: the preparation**, from a configuration whose allocator is the table base, at cost
`κP (K₁ + K₂ + 1)`. -/
def PrepTask : Prop :=
  ∃ (prep : Stmt) (κP : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg ALLOC = c.nreg cTB →
      c.nreg ALLOC + κP * ztks ≤ W →
      IRS P W c₀ prep c (κP * ztks) (PrepOut N₁ N₂ c)

/-! ## S: the start key (mathematics) -/

/-- **Task S (mathematics)**: the start key `((gW + Lst) % n, 0)` (offset `Lst`, the copy of the
shared vertex on the `C₁` side) is a word-level position, and every chord of `F₂⁺` attached at it
is a stop chord (a chord from a valid origin ending at the shared vertex is the shared chord seen
from the shared vertex). -/
def StartMathTask : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N : NF), J.P.Simple → IsNF ztj zta N →
    PosW P J ztwks 0 ∧
    oW J ((ztit % (chainModel J.whole).W.n : ℕ) + 0) = Lst J ∧
    ∀ e ∈ F₂plus J ztwrl,
      SideAttach (chainModel J.whole).W e ztwks 0 →
      StopChord2 J ztwrl e

/-! ## C: the number of keys (mathematics) -/

/-- The offsets of the cut keys of `F₂⁺` (in the walk of `C`). -/
def cutOffs (J : Merge.Junction) (S₂ : Set ztf) : Set ℝ :=
  {o | ∃ x : ℝ, (chainModel J.whole).IsCut ztbi x ∧ 0 ≤ x ∧
    x < (chainModel J.whole).W.n ∧ o = oW J x}

/-- The offsets of the possible window ends: the gap start and the images of the cut keys of
`N₁` (`WinOut`). -/
def winOffs (P : Polygon) (J : Merge.Junction) (N₁ : NF) : Set ℝ :=
  {(Lst J : ℝ) + lL1 J} ∪
    {o | ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (chainModel J.left).IsCut ztwjx
        ztwms ∧ o = (Lst J : ℝ) + ψ J d + t}

/-- **Task C (mathematics): the number of keys**: the offsets of the cut keys of `F₂⁺` and of the
window ends form a finite set of at most `4 K₂ + 2 K₁ + 9` offsets. -/
def CountTask : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF), J.P.Simple →
    IsNF ztbw zta N₁ → IsNF ztj zta N₂ →
    (cutOffs J ztwis ∪ winOffs P J N₁).Finite ∧
    (cutOffs J ztwis ∪ winOffs P J N₁).ncard ≤
      4 * N₂.nChords + 2 * N₁.nChords + 9
