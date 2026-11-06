module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvBatch

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
  have hPr : J.right.P.Simple := E.ctx2.2.2.2.2.1
  obtain ⟨hRC, hCS, -⟩ := regOf_spec E.hNF₂
  exact (Gran.touch_iff_side E.hNF₂ (FactsChain.walkAx J.right hPr) hRC hCS hk).1

theorem not_orgR {r : ℕ} (h : (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r) : ¬ OrgR r := by
  unfold OrgR CandR BestR LblR bF bE bH bN bL
  rcases h with ⟨h, h1, h2⟩ | h
  · ram_grind
  · unfold ER kN kL gN gR sP sC aB sw at h; unfold sw; omega

set_option maxHeartbeats 4000000 in
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
    fun r h1 h2 h3 h4 => hreg r (band_sw_not ⟨h1, h2⟩) h3 h4 (by omega_nf)
  have eGK : c.nreg wGK = cs.nreg wGK := keepS _ (by omega_nf)
    (by omega_nf) (by omega_nf)
    (by omega_nf)
  have eGB : c.nreg wGB = cs.nreg wGB := keepS _ (by omega_nf)
    (by omega_nf) (by omega_nf)
    (by omega_nf)
  have eKE : c.nreg kE = cs.nreg kE := keepS _ (by omega_nf)
    (by omega_nf) (by omega_nf)
    (by omega_nf)
  have eKH : c.nreg kH = cs.nreg kH := keepS _ (by omega_nf)
    (by omega_nf) (by omega_nf)
    (by omega_nf)
  have eTB : c.nreg cTB = cs.nreg cTB := keepS _ (by omega_nf)
    (by omega_nf) (by omega_nf)
    (by omega_nf)
  have hmc : ∀ x, cs.nreg cTB + 6 * N₂.nChords ≤ x → x < cs.nreg ALLOC → c.nmem x = cs.nmem x :=
    fun x h1 h2 => hB.memT x h2 (Or.inr h1)
  have harcs' : ∀ k, k < L.length → ShotList.arcAt c.nmem (c.nreg wGB) k =
      nArc (chainModel J.left) (Qof P) N₁ (L.getD k 0) := fun k hk' => by
    grind [ShotList.arcAt]
  have hlo : ShotList.loSet (chainModel J.left) (Qof P) c.nmem (c.nreg wGB) L.length [] =
      ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) L.length [] := by
    rw [eGB]; exact loSet_congr (fun x h1 h2 => hmc x (by omega) (by omega))
  have hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH) := fun h => by
    obtain ⟨⟨j, hj⟩, -⟩ := hB.bAcc h
    exact (hB.acc _ hj).2.2.2.2.2.2.2.1
  refine (orgDo_irs E hI hgen hL (by omega) (by omega) harcs' rfl rfl hk hs
    (by ram_grind) hb hB.fF hB.fN hroom).mono le_rfl ?_
  rintro c' ⟨hres, hcomp, hrej, hfr, hA'⟩
  refine ⟨batch_step hInv' (by omega) hs (up_ne_dn E hk) hT hres
    (fun hv => hlo ▸ hcomp hv.1 hv.2.1 hv.2.2) hrej hfr hA', fun r hr => ?_, fun x h1 h2 => ?_⟩
  · refine hfr r (band_sw_not ?_) (not_orgR hr) (by
      rcases hr with ⟨h, -, -⟩ | h
      · unfold LR oK oS sw at h; omega_nf
      · unfold ER kN kL gN gR sP sC aB sw at h; omega_nf)
    rcases hr with ⟨h, -, -⟩ | h
    · unfold LR oK oS sw at h; omega
    · unfold ER kN kL gN gR sP sC aB sw at h; omega
  · have eaB : c.nreg aB = cs.nreg aB := keepS _ (by omega_nf)
      (by omega_nf) (by omega_nf)
      (by omega_nf)
    have eC : c.nreg sC = cs.nreg sC := keepS _ (by omega_nf)
      (by omega_nf) (by omega_nf)
      (by omega_nf)
    rw [eaB] at h1; rw [eaB, eC] at h2
    rcases hres with ⟨hm, -⟩ | ⟨e, h, -, hm, -⟩
    · grind
    · rw [hm x (by omega), tabUpd_o _ (by omega) (by omega)
        (by omega)]

end

end SweepEv

end Chazelle.Core
