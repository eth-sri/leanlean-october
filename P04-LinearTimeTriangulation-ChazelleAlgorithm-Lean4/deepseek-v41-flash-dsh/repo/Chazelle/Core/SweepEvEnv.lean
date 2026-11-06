module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvCand4
public import Chazelle.Core.SweepEvSpec

/-!
# The sweep (WP-D), stage 3: the environment of the event loop

`EvEnv`: the facts fixed at the start configuration `c₀` of the run steps (the shooter, the
context, the chains and normal forms, the descriptors, the constants), and their transport to any
later configuration (`EvEnv.md`, `EvEnv.ctx1`, …).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- **The environment of the event loop** at `c₀` (the start of the run steps, after the
initialisation): the shooter and the context `X`, the junction and its stage-0 state, the normal
forms `N₁` (`sw 3`) and `N₂` (`sw 4`) with their facts, the model descriptor of `C₁` (`MD₁`,
`CD₁`), the constants (`Consts`, `OrgK`, `MapK`, `cGW`), the endpoint table base `cTB` (at the
allocator of `c₀`), and the answer stage's (`SweepIo`) power table (`TBR`, `TLR`) for `locJ`/local hits, with
`TLR ≤ ⌈log₂ (K₁ + K₂ + 1)⌉ + 3`; the table base `cTB` is the allocator of `c₀` (`hTA`). -/
structure EvEnv (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF) : Prop where
  hsh : ShooterOK sh Bs F X Ok
  hBs : Bs ⊆ oracleBands
  hXl : X.CapLocal
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hP : J.P.Simple
  hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC)
  hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10))
  hOk₁ : Ok P (chainModel J.left)
  hNF₁ : IsNF (chainModel J.left) (Qof P) N₁
  hsg₁ : (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (c₀.nreg (sw 5))
  hNW₁ : NFWithin c₀.nmem (c₀.nreg (sw 3)) (c₀.nreg ALLOC) N₁
  hNF₂ : IsNF (chainModel J.right) (Qof P) N₂
  hNW₂ : NFWithin c₀.nmem (c₀.nreg (sw 4)) (c₀.nreg ALLOC) N₂
  hmd : ModelDescAt c₀.nmem (c₀.nreg MD₁) (Qof P) (chainModel J.left)
  hmwf : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg MD₁)
  hm0 : c₀.nmem (c₀.nreg MD₁) = 0
  hcd : c₀.nreg CD₁ = c₀.nreg MD₁ + 1
  ctx1 : ChainCtx P W c₀ CD₁ J.left
  ctx2 : ChainCtx P W c₀ (sw 21) J.right
  ctxW : ChainCtx P W c₀ (sw 2) J.whole
  hK : Consts c₀
  hO : OrgK P J c₀
  hM : MapK J c₀
  hgw : c₀.nreg cGW = gW J
  hT : c₀.nreg ALLOC ≤ c₀.nreg cTB
  hTW : c₀.nreg cTB + 6 * N₂.nChords + 2 ≤ W
  hWn : 2 * (chainModel J.whole).W.n ≤ W
  hst : ∃ H, JunctionAt c₀.nmem (c₀.nreg (sw 0)) (c₀.nreg (sw 1)) (c₀.nreg (sw 2)) (Qof P) H J ∧
    St0S P c₀ H J
  hJWF : JunctionWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg (sw 0)) (c₀.nreg (sw 1)) (c₀.nreg (sw 2))
  hOk₂ : Ok P (chainModel J.right)
  hsg₂ : (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (c₀.nreg (sw 5))
  hdeg₁ : (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (c₀.nreg (sw 6))
  hdeg₂ : (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (c₀.nreg (sw 6))
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem (c₀.nreg TBR + j) = 2 ^ j
  hbig₁ : N₁.arcs.length < 2 ^ c₀.nreg TLR
  hbig₂ : N₂.arcs.length < 2 ^ c₀.nreg TLR
  hTBR : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC
  hNT₁ : NFWithin c₀.nmem (c₀.nreg (sw 3)) (c₀.nreg TBR) N₁
  hNT₂ : NFWithin c₀.nmem (c₀.nreg (sw 4)) (c₀.nreg TBR) N₂
  hTLR : c₀.nreg TLR ≤ Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 3
  hTA : c₀.nreg cTB = c₀.nreg ALLOC

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

namespace EvEnv

variable (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
include E hI

theorem md : ModelDescAt c.nmem (c.nreg MD₁) (Qof P) (chainModel J.left) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg MD₁) ∧ c.nmem (c.nreg MD₁) = 0 ∧
    c.nreg CD₁ = c.nreg MD₁ + 1 := by
  have eMD : c.nreg MD₁ = c₀.nreg MD₁ := hI.hin _ (by unfold IFix MD₁ sw; omega)
  have eCD : c.nreg CD₁ = c₀.nreg CD₁ := hI.hin _ (by unfold IFix CD₁ sw; omega)
  rcases E.hmd with ⟨-, H, C', hC', hMC⟩ | ⟨h1, -⟩
  swap
  · have := E.hm0; omega
  obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep E.hmwf E.hm0 hC' (fun a ha => hI.hm a ha) hI.hA
  Ξ eMD, eCD
  exact ⟨Or.inl ⟨w2, H, C', w3, hMC⟩, w1, w2, E.hcd⟩

theorem ctx1' : ChainCtx P W c CD₁ J.left :=
  E.ctx1.transport (hI.hin _ (by unfold IFix CD₁ sw; omega)) (fun a ha => hI.hm a ha) hI.hA

theorem ctx2' : ChainCtx P W c (sw 21) J.right :=
  E.ctx2.transport (hI.hin _ (by unfold IFix sw; omega)) (fun a ha => hI.hm a ha) hI.hA

theorem ctxW' : ChainCtx P W c (sw 2) J.whole :=
  E.ctxW.transport (hI.hin _ (by unfold IFix sw; omega)) (fun a ha => hI.hm a ha) hI.hA

theorem gw' : c.nreg cGW = gW J := (hI.hin _ (by unfold IFix cGW sw; omega)).trans E.hgw

omit E hI in
theorem tb' (_E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂)
    (hI : IInv W c₀ c) : c.nreg cTB = c₀.nreg cTB := hI.hin _ (by unfold IFix cTB sw; omega)

theorem nw₂' : NFWithin c.nmem (c.nreg (sw 4)) (c.nreg ALLOC) N₂ := by
  Ξ hI.hin _ (by unfold IFix sw; omega)
  exact (E.hNW₂.transport (fun a ha => hI.hm a ha)).mono hI.hA

end EvEnv

end

end SweepEv

end Chazelle.Core
