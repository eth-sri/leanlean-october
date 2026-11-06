module

public import Chazelle.Core.SweepEvBatch
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 3: one origin as a step of a batch (RAM)

`orgDo_batch`: `orgDo sh g` (`orgDo_irs`) keeps the invariant of the batch (`batch_step`) and the
registers and memory the origin enumeration reads — the hypothesis `od` of `OrgsTask`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- The regions of a chord record differ. -/
theorem up_ne_dn (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {k : ℕ} (hk : k < N₂.nChords) :
    (N₂.chord k).up ≠ (N₂.chord k).dn := by
  have hPr  := E.ctx2.2.2.2.2.1
  obtain ⟨hRC, hCS, -⟩ := regOf_spec E.hNF₂
  exact (Gran.touch_iff_side E.hNF₂ (FactsChain.walkAx J.right hPr) hRC hCS hk).1

theorem not_orgR {r : ℕ} (h : (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r) : ¬ OrgR r := by
  unfold OrgR CandR BestR LblR bF bE bH bN bL
  rcases h with ⟨h, h1, h2⟩ | h
  · simp [LR, oK, oS, sw] at h h1 h2; ufo sw
  · unfold ER kN kL gN gR sP sC aB sw at h; ufo sw

/-- **One origin as a step of a batch.** -/
theorem orgDo_batch (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {cs : Config} {L : List ℕ}
    (hL : ∀ a ∈ L, a < N₁.arcs.length) (hgK : cs.nreg wGK = L.length)
    (hAB : cs.nreg wGB + 4 * L.length ≤ cs.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt cs.nmem (cs.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ (L.getD k 0))
    (hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC)
    (hWT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg wGB)
    (hauxT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg aB)
    (haux : cs.nreg aB + 5 * cs.nreg sC ≤ cs.nreg ALLOC)
    (hkey : PosW P J (cs.nreg kE) (cs.nreg kH))
    (O : Set ℕ) (c : Config) (hI : IInv W c₀ c)
    (hInv : BatchInv P J N₂ cs
      (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) L.length []) O c)
    (hk : c.nreg oK < N₂.nChords) (hs : c.nreg oS ≤ 1)
    (hroom : c.nreg ALLOC + orgDoK (F (c₀.nreg (sw 5))) L.length KG ≤ W) :
    IRS P W c₀ (orgDo sh g) c (orgDoK (F (c₀.nreg (sw 5))) L.length KG) (fun c' =>
      BatchInv P J N₂ cs
        (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) L.length [])
        (insert (2 * c.nreg oK + c.nreg oS) O) c' ∧
      (∀ r, (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r → c'.nreg r = c.nreg r) ∧
      (∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x)) := by
  have hInv' := hInv
  obtain ⟨hreg, hAc, A, hB⟩ := hInv
  have keepS : ∀ r, 240000 ≤ r → r < 250000 → ¬ OrgR r → ¬ LR r → c.nreg r = cs.nreg r :=
    fun r h1 h2 h3 h4 => hreg r (band_sw_not ⟨h1, h2⟩) h3 h4 (by ufo ALLOC)
  have eGK : c.nreg wGK = cs.nreg wGK := keepS _ (by ufo wGK sw)
    (by ufo wGK sw) (by ufo OrgR CandR BestR LblR wGK bF bE bH bN bL sw)
    (by ufo LR wGK oK oS sw)
  have eGB : c.nreg wGB = cs.nreg wGB := keepS _ (by ufo wGB sw)
    (by ufo wGB sw) (by ufo OrgR CandR BestR LblR wGB bF bE bH bN bL sw)
    (by ufo LR wGB oK oS sw)
  have eKE : c.nreg kE = cs.nreg kE := keepS _ (by ufo kE sw)
    (by ufo kE sw) (by ufo OrgR CandR BestR LblR kE bF bE bH bN bL sw)
    (by ufo LR kE oK oS sw)
  have eKH : c.nreg kH = cs.nreg kH := keepS _ (by ufo kH sw)
    (by ufo kH sw) (by ufo OrgR CandR BestR LblR kH bF bE bH bN bL sw)
    (by ufo LR kH oK oS sw)
  have eTB : c.nreg cTB = cs.nreg cTB := keepS _ (by ufo cTB sw)
    (by ufo cTB sw) (by ufo OrgR CandR BestR LblR cTB bF bE bH bN bL sw)
    (by ufo LR cTB oK oS sw)
  have hmc : ∀ x, cs.nreg cTB + 6 * N₂.nChords ≤ x → x < cs.nreg ALLOC → c.nmem x = cs.nmem x :=
    fun x h1 h2 => hB.memT x h2 (Or.inr h1)
  have harcs' : ∀ k, k < L.length → ShotList.arcAt c.nmem (c.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ (L.getD k 0) := fun k hk' => by
    rw [eGB, ← harcs k hk']
    unfold ShotList.arcAt
    rw [hmc _ (by omega) (by omega), hmc _ (by omega) (by omega), hmc _ (by omega) (by omega),
      hmc _ (by omega) (by omega)]
  have hlo : ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length [] =
      ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) L.length [] := by
    rw [eGB]; exact loSet_congr (fun x h1 h2 => hmc x (by omega) (by omega))
  have hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH) := fun h => by
    obtain ⟨⟨j, hj⟩, -⟩ := hB.bAcc h
    exact (hB.acc _ hj).2.2.2.2.2.2.2.1
  refine (orgDo_irs E hI hgen hL (by rw [eGK, hgK]) (by rwo [eGB]) harcs' rfl rfl hk hs
    (by rwx [eKE, eKH]) hb hB.fF hB.fN hroom).mono le_rfl ?_
  rintro c' ⟨hres, hcomp, hrej, hfr, hA'⟩
  refine ⟨batch_step hInv' (by omega) hs (up_ne_dn E hk) hT hres
    (fun hv => hlo ▸ hcomp hv.1 hv.2.1 hv.2.2) hrej hfr hA', fun r hr => ?_, fun x h1 h2 => ?_⟩
  · refine hfr r (band_sw_not ?_) (not_orgR hr) (by
      rcases hr with ⟨h, -, -⟩ | h
      · unfold LR oK oS sw at h; ufo ALLOC
      · unfold ER kN kL gN gR sP sC aB sw at h; ufo ALLOC)
    rcases hr with ⟨h, -, -⟩ | h
    · ufo LR oK oS sw at h
    · ufo ER kN kL gN gR sP sC aB sw at h
  · have eaB : c.nreg aB = cs.nreg aB := keepS _ (by ufo aB sw)
      (by ufo aB sw) (by ufo OrgR CandR BestR LblR aB bF bE bH bN bL sw)
      (by ufo LR aB oK oS sw)
    have eC : c.nreg sC = cs.nreg sC := keepS _ (by ufo sC sw)
      (by ufo sC sw) (by ufo OrgR CandR BestR LblR sC bF bE bH bN bL sw)
      (by ufo LR sC oK oS sw)
    rw [eaB] at h1; rw [eaB, eC] at h2
    rcases hres with ⟨hm, -⟩ | ⟨e, h, -, hm, -⟩
    · exact hm x (by omega)
    · rw [hm x (by omega), tabUpd_o _ (by rwo [eTB]) (by rwo [eTB])
        (by rwo [eTB])]

end

end SweepEv

end Chazelle.Core
