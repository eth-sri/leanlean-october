module

public import Chazelle.Core.SweepEvEnv
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

/-!
# The sweep (WP-D), stage 3: one candidate (RAM), the composite

`evCand_irs`: soundness (`CandRes`) and completeness (`CandComp`) of one candidate.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **Completeness of a candidate**: a chord of `C` from `a` ending on the `C₁` part beyond the
start, before the far end of the chord of `C₂`, whose hit lies on the arcs `lo`, is accepted at
its attachment. -/
def CandComp (P : Polygon) (J : Merge.Junction) (S₂ : Set (Set Point)) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (lo : Set Point) (c c' : Config) : Prop :=
  ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t →
    sidePt (chainModel J.whole).W p t = rayPt a σ (J.whole.hitParam a σ) →
    (Lst J : ℝ) < oW J (p + t) → sidePt (chainModel J.whole).W p t ≠ J.shared →
    J.whole.hitParam a σ < J.right.hitParam a σ → rayPt a σ (J.whole.hitParam a σ) ∈ lo →
    ∃ h, (chainModel J.whole).param (Qof P) ⟨p, h⟩ = t ∧ AccAt P J S₂ T j u d a σ c c' p h

/-- The cost of a candidate. -/
def evCandK (Fg K KG : ℕ) : ℕ := evShotK Fg K + KG + 56500

/-- The preparation of completeness: the genuine hit, its arrival and its offset. -/
theorem cand_prep {J : Merge.Junction} (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {ch : Set Point} (hch : ch ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend ch) ∨ (σ = -1 ∧ a = Merge.rend ch)) (haR : a ∈ J.right.set)
    (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {p : ℕ} {t : ℝ}
    (h1 : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t)
    (h2 : sidePt (chainModel J.whole).W p t = rayPt a σ (J.whole.hitParam a σ))
    (h3 : (Lst J : ℝ) < oW J (p + t)) (h4 : sidePt (chainModel J.whole).W p t ≠ J.shared)
    (h5 : J.whole.hitParam a σ < J.right.hitParam a σ) :
    Genuine J.left a σ (J.whole.hitParam a σ) ∧
      J.whole.hitParam a σ < (Merge.rend ch).1 - (Merge.lend ch).1 ∧
      ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
          ((b₁ J + d) % (chainModel J.left).W.n) t := by
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨hfr, -, -, hR, -, -⟩ := right_hit_end (hS₂ hch) ha
  have hfree := whole_free_end hP haR hav hfr
  obtain ⟨hg, d, hd⟩ := map_complete hP ha₁ hσ hfree h1 h2 h3 h4
  exact ⟨hg, by rwx [← hR], d, hd⟩

theorem mod_back {n b d : ℕ} (hb : b < n) (hd : d < n) : ((b + d) % n + n - b) % n = d := by
  rcases Nat.lt_or_ge (b + d) n with h | h
  · rw [Nat.mod_eq_of_lt h, show b + d + n - b = d + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hd]
  · have e : (b + d) % n = b + d - n := by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [e, show b + d - n + n - b = d by omega, Nat.mod_eq_of_lt hd]

/-- Same key and best candidate. -/
def SameKB (c c' : Config) : Prop :=
  c'.nreg kE = c.nreg kE ∧ c'.nreg kH = c.nreg kH ∧ ∀ r, BestR r → c'.nreg r = c.nreg r

theorem bestSame_lift {c c₃ c' : Config} (hs : SameKB c c₃) (h : BestSame c₃ c') : BestSame c c' :=
  ⟨h.1.trans (hs.2.2 _ (Or.inl rfl)), h.2.1.trans (hs.2.2 _ (Or.inr (Or.inl rfl))),
    h.2.2.1.trans (hs.2.2 _ (Or.inr (Or.inr (Or.inl rfl)))),
    h.2.2.2.1.trans (lblOf_congr (fun q hq => hs.2.2 q (Or.inr (Or.inr (Or.inr hq))))),
    h.2.2.2.2.trans (hs.2.2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩

theorem offerRel_lift {P : Polygon} {J : Merge.Junction} {c c₃ c' : Config} {e h u d : ℕ}
    (hs : SameKB c c₃) (hO : OfferRel P J c₃ c' e h u d) : OfferRel P J c c' e h u d := by
  obtain ⟨eKE, eKH, hB⟩ := hs
  have eBF := hB _ (Or.inl rfl)
  have eBE := hB _ (Or.inr (Or.inl rfl))
  have eBH := hB _ (Or.inr (Or.inr (Or.inl rfl)))
  have eLb : lblOf c₃ bN bL = lblOf c bN bL :=
    lblOf_congr (fun q hq => hB q (Or.inr (Or.inr (Or.inr hq))))
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hO
  rw [eKE, eKH] at o3 o4 o5 o6
  rw [eBF, eBE, eBH] at o4 o5 o6
  rw [eLb] at o5
  exact ⟨o1, o2, fun h' => bestSame_lift ⟨eKE, eKH, hB⟩ (o3 h'), o4,
    o5,
    fun h1 h2 h3 => bestSame_lift ⟨eKE, eKH, hB⟩ (o6 h1 h2 h3)⟩

theorem tabUpd_congr {m m' : ℕ → ℕ} {T j e h x : ℕ}
    (hm : x ≠ T + 3 * j → x ≠ T + 3 * j + 1 → x ≠ T + 3 * j + 2 → m' x = m x) :
    tabUpd m' T j e h x = tabUpd m T j e h x := by
  unfold tabUpd upd
  split_ifs <;> first | rfl | exact hm (by omega) (by omega) (by omega)

theorem accAt_lift {P : Polygon} {J : Merge.Junction} {S₂ : Set (Set Point)} {T j u d : ℕ}
    {a : Point} {σ : ℝ} {c c₃ c' : Config} {e h : ℕ} (hs : SameKB c c₃)
    (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x)
    (hacc : AccAt P J S₂ T j u d a σ c₃ c' e h) : AccAt P J S₂ T j u d a σ c c' e h :=
  ⟨hacc.1, fun x hx => by
    rw [hacc.2.1 x (by omega)]
    exact tabUpd_congr (fun _ _ _ => hm x hx), offerRel_lift hs hacc.2.2⟩

theorem rejAt_lift {c c₃ c' : Config} (hs : SameKB c c₃) (hA : c.nreg ALLOC ≤ c₃.nreg ALLOC)
    (hm : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x) (hr : RejAt c₃ c') : RejAt c c' :=
  ⟨fun x hx => (hr.1 x (by omega)).trans (hm x hx), bestSame_lift hs hr.2⟩

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **One candidate.** -/
theorem evCand_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {L : List ℕ} (hL : ∀ a ∈ L, a < N₁.arcs.length)
    (hgK : c.nreg wGK = L.length) (hAB : c.nreg wGB + 4 * L.length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt c.nmem (c.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ (L.getD k 0))
    {ch : Set Point} (hch : ch ∈ N₂.F (chainModel J.right) (Qof P)) {a : Point}
    (hD : c.nreg oD ≤ 1)
    (ha : (dirOf (c.nreg oD) = 1 ∧ a = Merge.lend ch) ∨ (dirOf (c.nreg oD) = -1 ∧ a = Merge.rend ch))
    {s : SymPt} (hsym : SymPtIn c oSym s) (hsl : s.Lt P.n) (hse : s.eval (Qof P) = a)
    (habs : AbsRec P c oAbsA a.1 J.left.radius) (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (ha₁ : a.2 ≤ J.left.top.2)
    (hfe : c.nreg oFE < (chainModel J.right).W.n)
    (hfp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oFE, c.nreg oFC⟩)
    (hfar : (chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩ =
      if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch)
    (hj : 2 * c.nreg oK + c.nreg oS < 2 * N₂.nChords)
    (hk : PosW P J (c.nreg kE) (c.nreg kH)) (hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH))
    (hbF : c.nreg bF ≤ 1) (hbN : c.nreg bN ≤ 4)
    (hroom : c.nreg ALLOC + evCandK (F (c₀.nreg (sw 5))) L.length KG ≤ W) :
    IRS P W c₀ (evCand sh g) c (evCandK (F (c₀.nreg (sw 5))) L.length KG) (fun c' =>
      CandRes P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * c.nreg oK + c.nreg oS)
        (c.nreg oUp) (c.nreg oDn) a (dirOf (c.nreg oD)) c c' ∧
      CandComp P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * c.nreg oK + c.nreg oS)
        (c.nreg oUp) (c.nreg oDn) a (dirOf (c.nreg oD))
        (ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length []) c c' ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC) := by
  have hP := E.hP
  have hS₂ : N₂.F (chainModel J.right) (Qof P) ⊆ Merge.augChords J.right := E.hNF₂.1.2.1
  have hS₂f : (N₂.F (chainModel J.right) (Qof P)).Finite := E.hNF₂.1.1
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  set σ := dirOf (c.nreg oD) with hσd
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσd]; unfold dirOf; split_ifs <;> simp
  obtain ⟨hmd, hmwf, hm0, hcd⟩ := E.md hI
  subst hse
  set lo := ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length [] with hlo
  -- the rejection
  have rejQ : ∀ c' : Config,
      (∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c'.nreg r = c.nreg r) →
      c.nreg ALLOC ≤ c'.nreg ALLOC → (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x) →
      (∀ r, BestR r → c'.nreg r = c.nreg r) →
      (∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W (Merge.shoot J.whole (s.eval (Qof P)) σ) p t →
        sidePt (chainModel J.whole).W p t =
          rayPt (s.eval (Qof P)) σ (J.whole.hitParam (s.eval (Qof P)) σ) →
        (Lst J : ℝ) < oW J (p + t) → sidePt (chainModel J.whole).W p t ≠ J.shared →
        J.whole.hitParam (s.eval (Qof P)) σ < J.right.hitParam (s.eval (Qof P)) σ →
        rayPt (s.eval (Qof P)) σ (J.whole.hitParam (s.eval (Qof P)) σ) ∈ lo → False) →
      CandRes P J S₂ (c.nreg cTB) (2 * c.nreg oK + c.nreg oS) (c.nreg oUp) (c.nreg oDn)
        (s.eval (Qof P)) σ c c' ∧
      CandComp P J S₂ (c.nreg cTB) (2 * c.nreg oK + c.nreg oS) (c.nreg oUp) (c.nreg oDn)
        (s.eval (Qof P)) σ lo c c' ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC := by
    intro c' hr hA hm hB hno
    refine ⟨Or.inl ⟨hm, hB _ (Or.inl rfl), hB _ (Or.inr (Or.inl rfl)), hB _ (Or.inr (Or.inr (Or.inl rfl))),
      lblOf_congr (fun q hq => hB q (Or.inr (Or.inr (Or.inr hq)))),
      hB _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, fun p t h1 h2 h3 h4 h5 h6 =>
        absurd (hno p t h1 h2 h3 h4 h5 h6) id, hr, hA⟩
  -- 1. the shot
  have hroom1 : c.nreg ALLOC + evShotK (F (c₀.nreg (sw 5))) L.length ≤ W := by
    ufo evCandK at hroom
  refine IRS.mono (K := evShotK (F (c₀.nreg (sw 5))) L.length + (KG + 56500))
    (IRS.seq (K₁ := evShotK (F (c₀.nreg (sw 5))) L.length) (K₂ := KG + 56500)
    (evShot_irs E.hsh E.hBs E.hXl hI E.hK E.hG E.hWh hP E.hX E.hcap E.hOk₁ E.hNF₁ E.hsg₁ hmd hmwf
      hm0 (E.ctx1' hI) hcd hL hgK hAB harcs hsym hsl haR hav ha₁ hD hroom1) ?_)
    (by ufo evCandK) (fun _ => id)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨f1, f2, f3⟩, fr1⟩
  have k01 : c₁.nreg K0 = 0 := (E.hK.fix hI₁).1
  have keep1 : ∀ r, 240000 ≤ r → r < 250000 → ¬ ShW r → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1.1 r (not_oracle_sw h1 h2) h3 (by ufo ALLOC)
  have nShW : ∀ r, ShW r → CandR r := fun r hr => by
    unfold ShW RS eF eNo sw at hr; ufo CandR sw
  have best1 : ∀ r, BestR r → c₁.nreg r = c.nreg r := fun r hr => keep1 r
    (by ufo BestR LblR bF bE bH bN bL sw at hr)
    (by ufo BestR LblR bF bE bH bN bL sw at hr)
    (by unfold BestR LblR bF bE bH bN bL sw at hr; ufo ShW RS eF eNo sw)
  have frR1 : ∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r hr h1 h2 => fr1.1 r hr (fun h => h1 (nShW r h)) h2
  -- the completeness data
  have prep := fun (p : ℕ) (t : ℝ) h1 h2 h3 h4 h5 =>
    cand_prep (S₂ := S₂) hP hS₂ hch ha haR hav ha₁ (p := p) (t := t) h1 h2 h3 h4 h5
  by_cases hF : c₁.nreg K0 < c₁.nreg eF
  · rw [k01] at hF
    have hF1 : c₁.nreg eF = 1 := by omega
    obtain ⟨τ, hτ, huq, hAle, hA1, hA0⟩ := f3 hF1
    refine IRS.mono (K := KG + 56498 + 2) (IRS.ifT (by rwx [k01]) ?_) (by omega)
      (fun _ => id)
    by_cases hAr : c₁.nreg K0 < c₁.nreg eA
    · rw [k01] at hAr
      have hA11 : c₁.nreg eA = 1 := by omega
      obtain ⟨hpe, hppA, hArr, hnorm⟩ := hA1 hA11
      refine IRS.mono (K := KG + 56496 + 2) (IRS.ifT (by rwx [k01]) ?_) (by omega)
        (fun _ => id)
      -- 2. the genuineness check
      have eD1 : c₁.nreg oD = c.nreg oD := keep1 _ (by ufn oD sw) (by ufn oD sw)
        (by ufo ShW RS oD eF eNo sw)
      have habs1 : AbsRec P c₁ oAbsA (s.eval (Qof P)).1 J.left.radius := ShotList.absRec_copy habs
        (keep1 _ (by ufn oAbsA sw) (by ufn oAbsA sw)
          (by ufo ShW RS oAbsA eF eNo sw))
        (keep1 _ (by ufn oAbsA sw) (by ufn oAbsA sw)
          (by ufo ShW RS oAbsA eF eNo sw))
        (keep1 _ (by ufn oAbsA sw) (by ufn oAbsA sw)
          (by ufo ShW RS oAbsA eF eNo sw))
        (keep1 _ (by ufn oAbsA sw) (by ufn oAbsA sw)
          (by ufo ShW RS oAbsA eF eNo sw))
      have hroomG : c₁.nreg ALLOC + KG ≤ W := by ufo evCandK at hroom
      refine IRS.seq (K₁ := KG) (K₂ := 56496) (hgen c₁ (s.eval (Qof P)) σ τ hI₁ hroomG
        (by rwx [eD1]) (by rw [eD1]) habs1 haR hav ha₁ hτ hpe hppA hArr) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨hbG, frG⟩
      have k02 : c₂.nreg K0 = 0 := (E.hK.fix hI₂).1
      have keep2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ ShW r → ¬ GR r → c₂.nreg r = c.nreg r :=
        fun r h1 h2 h3 h4 => (frG.1 r (not_oracle_sw h1 h2) h4 (by ufo ALLOC)).trans
          (keep1 r h1 h2 h3)
      have keep2' : ∀ r, (sw 2200 ≤ r ∧ r < sw 2240) ∨ (sw 2283 < r ∧ r < sw 3000) →
          c₂.nreg r = c.nreg r := fun r hr => keep2 r (by ufo sw at hr)
        (by ufo sw at hr) (by ufo ShW RS eF eNo sw at *)
        (by ufo GR cG sw at *)
      have keepA2 : ∀ r, eA ≤ r → r ≤ eA + 2 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
        frG.1 r (not_oracle_sw (by ufo eA sw at h1) (by ufo eA sw at h2))
          (by ufo GR cG eA sw at *) (by ufo eA ALLOC sw at *)
      have nGR : ∀ r, GR r → CandR r := fun r hr => by unfold GR cG sw at hr; ufo CandR sw
      have frR2 : ∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
        fun r hr h1 h2 => (frG.1 r hr (fun h => h1 (nGR r h)) h2).trans (frR1 r hr h1 h2)
      have best2 : ∀ r, BestR r → c₂.nreg r = c.nreg r := fun r hr => by
        rw [← best1 r hr]
        exact frG.1 r (not_oracle_sw (by ufo BestR LblR bF bE bH bN bL sw at hr)
          (by ufo BestR LblR bF bE bH bN bL sw at hr))
          (by unfold BestR LblR bF bE bH bN bL at hr; ufo GR cG sw at *)
          (by ufo BestR LblR bF bE bH bN bL ALLOC sw at *)
      have hA2c : c.nreg ALLOC ≤ c₂.nreg ALLOC := hA₁.trans frG.2.1
      have hm2c : ∀ x, x < c.nreg ALLOC → c₂.nmem x = c.nmem x := fun x hx =>
        (frG.2.2 x (by omega)).trans (fr1.2.2 x hx)
      by_cases hGb : c₂.nreg K0 < c₂.nreg cG
      · rw [k02] at hGb
        have hgen1 : Genuine J.left (s.eval (Qof P)) σ τ := hbG.2.1 (by have := hbG.1; omega)
        refine IRS.mono (K := 56494 + 2) (IRS.ifT (by rwx [k02]) ?_) (by omega) (fun _ => id)
        -- 3. the far-end test
        have eE1 := keepA2 (eA + 1) (by omega) (by omega)
        have eE2 := keepA2 (eA + 2) (by omega) (by omega)
        have eFE : c₂.nreg oFE = c.nreg oFE := keep2' _ (Or.inl ⟨by ufo oFE sw,
          by ufo oFE sw⟩)
        have eFC : c₂.nreg oFC = c.nreg oFC := keep2' _ (Or.inl ⟨by ufo oFC sw,
          by ufo oFC sw⟩)
        have eD2 : c₂.nreg oD = c.nreg oD := keep2' _ (Or.inl ⟨by ufo oD sw,
          by ufo oD sw⟩)
        have hw : (chainModel J.left).pos (Qof P) ⟨c₁.nreg (eA + 1), c₁.nreg (eA + 2)⟩ =
            rayPt (s.eval (Qof P)) σ τ := hArr.2.2.2.1
        have hy1 : |((chainModel J.left).pos (Qof P) ⟨c₁.nreg (eA + 1), c₁.nreg (eA + 2)⟩).2| <
            J.left.radius := by
          rw [hw, Visibility.rayPt_snd]
          have hR₁ : J.left.radius = J.right.radius := rfl
          rw [hR₁]
          exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2
            J.right.coordBound_lt_radius
        have hy2 : |((chainModel J.right).pos (Qof P) ⟨c.nreg oFE, c.nreg oFC⟩).2| <
            J.right.radius := by
          rw [hfar]
          obtain ⟨-, -, -, -, hl2, hr2⟩ := right_hit_end (hS₂ hch) ha
          split_ifs <;> [rw [hr2]; rw [hl2]] <;>
          exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2
            J.right.coordBound_lt_radius
        have hroomF : c₂.nreg ALLOC + 34000 ≤ W := by
          have := frG.2.1; ufo evCandK at hroom
        refine IRS.seq (K₁ := 34000) (K₂ := 22494) (farChk_irs hI₂ E.hK (E.ctx1' hI₂) (E.ctx2' hI₂)
          (by rwx [eE1]) (by rwx [eE1, eE2]) (by rwx [eE1, eE2])
          (by rwx [eFE]) (by rwx [eFE, eFC]) (by rwx [eFE, eFC])
          (by rwx [eD2]) hroomF) ?_
        rintro c₃ hI₃ hA₃ hA₃' ⟨hbF', frF⟩
        rw [eE1, eE2, eFE, eFC, eD2, hw, hfar] at hbF'
        -- the bit is the far-end condition
        have hfarIff : (if c.nreg oD = 1 then (rayPt (s.eval (Qof P)) σ τ).1 <
              (if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch).1
            else (if c.nreg oD = 1 then Merge.rend ch else Merge.lend ch).1 <
              (rayPt (s.eval (Qof P)) σ τ).1) ↔ τ < (Merge.rend ch).1 - (Merge.lend ch).1 := by
          rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hd1 : c.nreg oD = 1 := by
              by_contra h; rw [hσd] at h1; unfold dirOf at h1; rw [ite_eq_right h] at h1; norm_num at h1
            rw [ite_eq_left hd1, ite_eq_left hd1, Visibility.rayPt_fst, h1, h2]
            constructor <;> intro h <;> linarith
          · have hd1 : c.nreg oD ≠ 1 := by
              intro h; rw [hσd] at h1; unfold dirOf at h1; rw [ite_eq_left h] at h1; norm_num at h1
            rw [ite_eq_right hd1, ite_eq_right hd1, Visibility.rayPt_fst, h1, h2]
            constructor <;> intro h <;> linarith
        have hbFr := hbF'.congr hfarIff
        have k03 : c₃.nreg K0 = 0 := (E.hK.fix hI₃).1
        have keep3 : ∀ r, ¬ (cAW ≤ r ∧ r ≤ cFr) → bandOf r ∉ oracleBands → r ≠ ALLOC →
            c₃.nreg r = c₂.nreg r := fun r h1 h2 h3 => frF.1 r h2 h1 h3
        have nF : ∀ r, cAW ≤ r ∧ r ≤ cFr → CandR r := fun r hr => by
          unfold cAW cFr sw at hr; ufo CandR sw
        have frR3 : ∀ r, bandOf r ∉ oracleBands → ¬ CandR r → r ≠ ALLOC → c₃.nreg r = c.nreg r :=
          fun r hr h1 h2 => (keep3 r (fun h => h1 (nF r h)) hr h2).trans (frR2 r hr h1 h2)
        have best3 : ∀ r, BestR r → c₃.nreg r = c.nreg r := fun r hr => by
          rw [← best2 r hr]
          exact keep3 r (by unfold BestR LblR bF bE bH bN bL at hr; ufo cAW cFr sw at *)
            (not_oracle_sw (by ufo BestR LblR bF bE bH bN bL sw at hr)
              (by ufo BestR LblR bF bE bH bN bL sw at hr))
            (by ufo BestR LblR bF bE bH bN bL ALLOC sw at *)
        have hA3c : c.nreg ALLOC ≤ c₃.nreg ALLOC := hA2c.trans frF.2.1
        have hm3c : ∀ x, x < c.nreg ALLOC → c₃.nmem x = c.nmem x := fun x hx =>
          (frF.2.2 x (by omega)).trans (hm2c x hx)
        by_cases hFr : c₃.nreg K0 < c₃.nreg cFr
        · rw [k03] at hFr
          have hlt : τ < (Merge.rend ch).1 - (Merge.lend ch).1 := hbFr.2.1 (by have := hbFr.1; omega)
          refine IRS.mono (K := 22300 + 2) (IRS.ifT (by rwx [k03]) ?_) (by omega)
            (fun _ => id)
          -- 4. the accepting tail
          have kc3 : ∀ r, (sw 2200 ≤ r ∧ r < sw 2240) ∨ (sw 2283 < r ∧ r < sw 3000) →
              c₃.nreg r = c.nreg r := fun r hr => by
            rw [keep3 r (by ufo cAW cFr sw at *)
              (not_oracle_sw (by ufo sw at hr) (by ufo sw at hr))
              (by ufo ALLOC sw at *)]
            exact keep2' r hr
          have kA3 : ∀ r, eA ≤ r → r ≤ eA + 2 → c₃.nreg r = c₁.nreg r := fun r h1 h2 => by
            rw [keep3 r (by ufo cAW cFr eA sw at *)
              (not_oracle_sw (by ufo eA sw at h1) (by ufo eA sw at h2))
              (by ufo ALLOC eA sw at *)]
            exact keepA2 r h1 h2
          have e31 := kA3 (eA + 1) (by omega) (by omega)
          have e32 := kA3 (eA + 2) (by omega) (by omega)
          have hs3 : SameKB c c₃ := ⟨kc3 _ (Or.inr ⟨by ufo kE sw, by ufo kE sw⟩),
            kc3 _ (Or.inr ⟨by ufo kH sw, by ufo kH sw⟩), best3⟩
          have eK3 : c₃.nreg oK = c.nreg oK := kc3 _ (Or.inl ⟨by ufo oK sw, by ufo oK sw⟩)
          have eS3 : c₃.nreg oS = c.nreg oS := kc3 _ (Or.inl ⟨by ufo oS sw, by ufo oS sw⟩)
          have eU3 : c₃.nreg oUp = c.nreg oUp := kc3 _ (Or.inl ⟨by ufo oUp sw, by ufo oUp sw⟩)
          have eN3 : c₃.nreg oDn = c.nreg oDn := kc3 _ (Or.inl ⟨by ufo oDn sw, by ufo oDn sw⟩)
          have eT3 : c₃.nreg cTB = c.nreg cTB := (E.tb' hI₃).trans (E.tb' hI).symm
          have hTW3 : c₃.nreg cTB + 3 * (2 * c₃.nreg oK + c₃.nreg oS) + 2 ≤ W := by
            rw [E.tb' hI₃, eK3, eS3]; have := E.hTW; omega
          have hroomA : c₃.nreg ALLOC + 22300 ≤ W := by
            have := frF.2.1; have := frG.2.1; ufo evCandK at hroom
          refine (evAccT_irs (S₂ := S₂) hI₃ E.hK E.hM hP hS₂ hS₂f hch ha haR hav ha₁ hgen1 hlt
            (by rwx [e31]) (by rwx [e31, e32]) (by rwx [e31, e32])
            (by rwx [e31, e32]) E.ctxW E.hgw (by rwx [hs3.1, hs3.2.1])
            (by rw [hs3.2.2 _ (Or.inl rfl), hs3.2.2 _ (Or.inr (Or.inl rfl)),
              hs3.2.2 _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hb)
            (by rwx [hs3.2.2 _ (Or.inl rfl)])
            (by rwx [hs3.2.2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))])
            (by rw [E.tb' hI₃]; exact E.hT) hTW3 E.hWn hroomA).mono le_rfl ?_
          rintro c' ⟨hacc, hrej, hfr4, hA4⟩
          rw [e31, e32, eT3, eK3, eS3, eU3, eN3] at hacc
          rw [e31, e32] at hrej
          refine ⟨?_, ?_, fun r hr h1 h2 => (hfr4 r hr h1 h2).trans (frR3 r hr h1 h2), hA3c.trans hA4⟩
          · by_cases hMV : SweepEv.MVal J ((c₁.nreg (eA + 1) + (chainModel J.left).W.n - b₁ J) %
                (chainModel J.left).W.n) (c₁.nreg (eA + 2))
            · exact Or.inr ⟨_, _, accAt_lift hs3 hA3c hm3c (hacc hMV)⟩
            · exact Or.inl (rejAt_lift hs3 hA3c hm3c (hrej hMV))
          · intro p t h1 h2 h3 h4 h5 h6
            obtain ⟨hg, -, d₀, hv₀, hpd, harr₀⟩ := prep p t h1 h2 h3 h4 h5
            have hτT := huq _ hg h6
            subst hτT
            have ha₁' : (s.eval (Qof P)).2 ≤ J.left.top.2 := ha₁
            obtain ⟨hpq, htq⟩ := arrival_unique hP ha₁' hσ hg hArr harr₀
            have hd₀ : d₀ < (chainModel J.left).W.n := lt_of_lt_of_le hv₀.1 (E₁_le hP)
            have hdd : (c₁.nreg (eA + 1) + (chainModel J.left).W.n - b₁ J) %
                (chainModel J.left).W.n = d₀ := by
              rw [hpq]
              exact mod_back (b₁_lt (J := J)) hd₀
            have hMV : SweepEv.MVal J ((c₁.nreg (eA + 1) + (chainModel J.left).W.n - b₁ J) %
                (chainModel J.left).W.n) (c₁.nreg (eA + 2)) := by
              rw [hdd]
              refine ⟨hv₀.1, hv₀.2.1, fun h => hv₀.2.2.1 ⟨h.1, h.2.1, fun ht0 => h.2.2 ?_⟩⟩
              exact hnorm.2 (by rwx [htq])
            have hacc' := accAt_lift hs3 hA3c hm3c (hacc hMV)
            rw [hdd, hpd] at hacc'
            refine ⟨_, ?_, hacc'⟩
            have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
            obtain ⟨-, hmem, hS, hpt, -⟩ := hacc'.1
            exact (hM.attach_unique (F₂plus_subset J hS₂ hmem) hS h1 (by rw [hpt, h2])).2
        · rw [k03] at hFr
          have hnlt : ¬ τ < (Merge.rend ch).1 - (Merge.lend ch).1 := fun h => by
            have := hbFr.2.2 h; omega
          refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwx [k03]) (IRS.skip hI₃ rfl)) (by omega) ?_
          rintro c' rfl
          refine rejQ c₃ frR3 hA3c hm3c best3 ?_
          intro p t h1 h2 h3 h4 h5 h6
          obtain ⟨hg, hlt', -⟩ := prep p t h1 h2 h3 h4 h5
          have := huq _ hg h6
          subst this
          exact hnlt hlt'
      · rw [k02] at hGb
        have hng : ¬ Genuine J.left (s.eval (Qof P)) σ τ := fun h => by have := hbG.2.2 h; omega
        refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwx [k02]) (IRS.skip hI₂ rfl)) (by omega) ?_
        rintro c' rfl
        refine rejQ c₂ frR2 hA2c hm2c best2 ?_
        intro p t h1 h2 h3 h4 h5 h6
        obtain ⟨hg, -⟩ := prep p t h1 h2 h3 h4 h5
        have := huq _ hg h6
        subst this
        exact hng hg
    · rw [k01] at hAr
      have hA0' : c₁.nreg eA ≠ 1 := by omega
      refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwx [k01]) (IRS.skip hI₁ rfl)) (by omega) ?_
      rintro c' rfl
      refine rejQ c₁ frR1 hA₁ (fr1.2.2) best1 ?_
      intro p t h1 h2 h3 h4 h5 h6
      obtain ⟨hg, -, d, -, -, harr⟩ := prep p t h1 h2 h3 h4 h5
      have := huq _ hg h6
      subst this
      exact hA0 hA0' _ _ harr
  · rw [k01] at hF
    have hF0 : c₁.nreg eF ≠ 1 := by omega
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwx [k01]) (IRS.skip hI₁ rfl)) (by omega) ?_
    rintro c' rfl
    refine rejQ c₁ frR1 hA₁ (fr1.2.2) best1 ?_
    intro p t h1 h2 h3 h4 h5 h6
    obtain ⟨hg, -⟩ := prep p t h1 h2 h3 h4 h5
    exact hF0 (f2 _ hg h6)

end

end SweepEv

end Chazelle.Core
