module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FuseAsmCapStage
public import Chazelle.Core.GranNFBounds

/-!
# WP-F fusion assembly, part 20: the context of the fusion driver

`FCtx P W J H N₁ N₂ A c`: the facts of the precondition of the fusion that the driver keeps
(the junction and normal-form descriptors in the input registers `70000 … 70004`, readable below
`A ≤ allocator`).  It survives every step that keeps these registers and the memory below `A`
(`FCtx.keep`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm

@[expose] public section

/-- The kept facts of the fusion's precondition. -/
structure FCtx (P : Polygon) (W : ℕ) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (A : ℕ)
    (c : Config) : Prop where
  good : GoodEnv P
  hw : hostWords P.n ≤ W
  jat : JunctionAt c.nmem (c.nreg 70000) (c.nreg 70001) (c.nreg 70002) (Qof P) H J
  jwf : JunctionWF P A c.nmem (c.nreg 70000) (c.nreg 70001) (c.nreg 70002)
  simple : J.P.Simple
  gen : SharedGeneric J
  nf₁ : NFWithin c.nmem (c.nreg 70003) A N₁
  nf₂ : NFWithin c.nmem (c.nreg 70004) A N₂
  is₁ : IsNF (chainModel J.left) (Qof P) N₁
  is₂ : IsNF (chainModel J.right) (Qof P) N₂
  le : A ≤ c.nreg ALLOC

theorem chainDesc_keep {P : Polygon} {A : ℕ} {m m' : ℕ → ℕ} {B : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P A m B) (hC : ChainDescAt m B (Qof P) H C) (he : ∀ a, a < A → m' a = m a) :
    ChainDescAt m' B (Qof P) H C ∧ ChainWF P A m' B := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hC
  have h5 := hwf.1
  exact ⟨chainDescAt_copy hC hEb he (fun j hj => he _ (by omega)),
    chainWF_copy hwf hC he (fun j hj => he _ (by omega)) h5 le_rfl⟩

section
variable {P : Polygon} {W : ℕ} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {A : ℕ}
theorem FCtx.keep
    {c c' : Config} (h : FCtx P W J H N₁ N₂ A c)
    (hr : ∀ r, 70000 ≤ r → r < 70005 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < A → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    FCtx P W J H N₁ N₂ A c' := by
  obtain ⟨hG, hW, ⟨hl, hr', hw⟩, ⟨wl, wr', ww, hreg⟩, hP, hgen, n₁, n₂, i₁, i₂, hle⟩ := h
  have e0 := hr 70000 (by norm_num) (by norm_num)
  have e1 := hr 70001 (by norm_num) (by norm_num)
  have e2 := hr 70002 (by norm_num) (by norm_num)
  rw [← e0] at hl wl
  rw [← e1] at hr' wr'
  rw [← e2] at hw ww hreg
  rw [← hr 70003 (by norm_num) (by norm_num)] at n₁
  rw [← hr 70004 (by norm_num) (by norm_num)] at n₂
  obtain ⟨kl, kwl⟩ := chainDesc_keep wl hl hm
  obtain ⟨kr, kwr⟩ := chainDesc_keep wr' hr' hm
  obtain ⟨kw, kww⟩ := chainDesc_keep ww hw hm
  refine ⟨hG, hW, ⟨kl, kr, kw⟩, ⟨kwl, kwr, kww, fun H' hH' => ?_⟩, hP, hgen,
    n₁.transport hm, n₂.transport hm, i₁, i₂, le_trans hle ha⟩
  obtain ⟨-, -, hEb, -⟩ := ww.2 H J.whole hw
  
  
  have hH : HostAt c'.nmem (c'.nmem (c'.nreg 70002)) H := by
    ram_grind
  have := NFLoc.hostAt_unique hH' hH
  subst this
  exact hreg H' hw.1

/-- The side chains in the input registers. -/
theorem FCtx.side
    {c : Config} (h : FCtx P W J H N₁ N₂ A c) :
    ChainDescAt c.nmem (c.nreg 70000) (Qof P) H (sideChain J 0) ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70000) ∧
      ChainDescAt c.nmem (c.nreg 70001) (Qof P) H (sideChain J 1) ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70001) ∧
      ChainDescAt c.nmem (c.nreg 70002) (Qof P) H J.whole ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70002) :=
  ⟨h.jat.1, h.jwf.1.mono h.le, h.jat.2.1, h.jwf.2.1.mono h.le, h.jat.2.2, h.jwf.2.2.1.mono h.le⟩


end

end

end FuseAsm

end Chazelle.Core
