module

public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Core.SweepIoBruteShot

/-!
# The sweep RAM (WP-D), answers: the brute-force shot (`BruteSpec`)

`bruteS sh`: copy the normalised arcs of `N₁` to fresh memory (`bLoop`), then shoot from the
symbolic point in `sO` at all of them in the model of `C₁` (model descriptor `sw 30`) and offer
the hit with tag `0` (`symShot`, chain descriptor `sw 20`).

**`bruteSpec : BruteSpec`.**  Soundness: the hit is a walk point at the height of `z`, not above
the top of `C₁`, hence a point of `C₁` or of the box (`walk_hit_onCB`).  Completeness: the arcs of
`N₁` cover the whole walk, so the exit point of a free ray lies on them (`exit_in_arcs`); the
arcs are off the domain, so the first hit of the shot is the first hit of `C₁`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- **The brute-force shot.** -/
def bruteS (sh : Stmt) : Stmt := .seq bLoop (symShot sh (sw 30) bBase bN (sw 20) K0)

/-- The cost constant. -/
def bruteK : ℕ := 600000

theorem brute_cost (A Fg : ℕ) : bLoopK A + symShotK Fg A ≤ bruteK * (A + 1) * (Fg + 1) := by
  unfold bLoopK symShotK ShotList.shotCost bArcK offerK bruteK
  have e1 : (A + 1) * (16 * Fg + 500000) = 16 * ((A + 1) * Fg) + 500000 * (A + 1) := by ring
  have e2 : 600000 * (A + 1) * (Fg + 1) = 600000 * ((A + 1) * Fg) + 600000 * (A + 1) := by ring
  rw [e1, e2]; omega

theorem sregOK_sw {j : ℕ} (h1 : j < 1300 ∨ 1600 ≤ j) (h2 : j < 2000 ∨ 2012 < j) (h3 : j < 10000) :
    SRegOK (sw j) := by
  unfold SRegOK sw; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The brute-force shot meets its contract.** -/
theorem bruteSpec : BruteSpec := by
  refine ⟨bruteS, bruteK, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L s z hA hI hs hsl hz hzC hz1 hz2 hzt
    hbL hacc hroom
  have hcost := brute_cost N₁.arcs.length (F (c₀.nreg (sw 5)))
  have hP : J.left.P.Simple := hA.hP
  have hNF := hA.hNF₁
  have hNW : NFWithin c.nmem (c₀.nreg (sw 3)) E N₁ :=
    hA.hN₁.transport (fun a ha => hI.hm a (by have := hA.hE; omega))
  have hroom' : c.nreg ALLOC + (bLoopK N₁.arcs.length + symShotK (F (c₀.nreg (sw 5))) N₁.arcs.length) ≤ W := by
    have := Nat.add_le_add_left hcost (c.nreg ALLOC)
    exact le_trans this hroom
  refine (IRS.seq (K₂ := symShotK (F (c₀.nreg (sw 5))) N₁.arcs.length) (bLoop_irs hI hA.hK (hA.ctxL hI) hP hNF hNW
    (hI.hin _ (by unfold IFix sw; omega)) (hA.hE.trans hI.hA) (le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) _) hroom')) ?_).mono
    hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' hBW
  obtain ⟨w1, w2, -, w4, -, w6, w7, w8, w9⟩ := hBW
  have nb : ∀ j, j < 10000 → bandOf (sw j) ∉ oracleBands := fun j hj => nob_sw hj
  have keep : ∀ j, j < 10000 → ¬ BSet (sw j) → c₁.nreg (sw j) = c.nreg (sw j) := fun j hj hb =>
    w9 _ (nb j hj) hb (by unfold ALLOC sw; omega)
  have a1 : ∀ j, j ≤ 12 → c₁.nreg (accA + j) = c.nreg (accA + j) := fun j hj => by
    have e : accA + j = sw (2000 + j) := by unfold accA sw; omega
    rw [e]; exact keep (2000 + j) (by omega) (by unfold BSet sw; omega)
  have d1 : c₁.nreg qD = c.nreg qD := keep 3212 (by norm_num) (by unfold BSet sw; omega)
  have hacc1 : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
      (dirOf (c₁.nreg qD)) L c₁ := by rw [d1]; exact hacc.transport a1
  have hs1 : SymPtIn c₁ sO s := symPtIn_copy hs (keep 3231 (by norm_num) (by unfold BSet sw; omega))
    (keep 3232 (by norm_num) (by unfold BSet sw; omega))
    (keep 3233 (by norm_num) (by unfold BSet sw; omega))
  have hK0 : c₁.nreg K0 = 0 := (hA.hK.fix hI₁).1
  have hMod : ModB J (c.nreg bL) (c.nreg bR) (c₁.nreg K0) = J.left := by
    rw [hK0, hbL]; simp [ModB]
  have hzD : z ∈ J.left.dom := mem_dom_of J.left hzt hz1 hz2 hzC
  have hN1 : c₁.nreg bN = N₁.arcs.length := w4
  have harcs : ∀ j, j < c₁.nreg bN →
      ShotList.PieceOK (chainModel J.left) (Qof P) P.n (ShotList.arcAt c₁.nmem (c₁.nreg bBase) j) ∧
      (chainModel J.left).arcWt
        ((chainModel J.left).key (Qof P) (ShotList.arcAt c₁.nmem (c₁.nreg bBase) j).1)
        ((chainModel J.left).key (Qof P) (ShotList.arcAt c₁.nmem (c₁.nreg bBase) j).2) ≤
        c₀.nreg (sw 5) := by
    intro j hj
    rw [hN1] at hj
    rw [w1, w7 j hj]
    exact nArc_piece hP hNF hA.hsg₁ hj
  refine (symShot_irs (C := J.left) (H := H) (md := sw 30) (base := bBase) (cnt := bN)
    (dsc := sw 20) (tg := K0) hsh hBs hXl hI₁ hA.hK hA.hG hA.hWh hA.hX hA.hcap hA.hOk₁
    (hA.mdL hI₁) hA.hostReg (hA.ctxL hI₁) harcs (by rw [w1, hN1, w6]) hs1 hsl hz hzD hz1 hz2 hzt
    hacc1 (by rw [hK0]; omega) hMod rfl
    ⟨sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num)⟩
    (by rw [hN1]; have := hA₁'; have := hroom'; omega)).mono (by rw [hN1]) ?_
  rintro c' ⟨L', hacc', hL', hcomp, k2, hA2, hm2⟩
  rw [d1] at hacc' hcomp hL'
  refine ⟨⟨L', hacc', ?_, fun τ hτ => ?_, fun hf => ?_⟩, ?_, ?_, fun a ha => ?_⟩
  · rcases hL' with rfl | ⟨τ, rfl, -⟩
    · exact le_rfl
    · exact Set.subset_insert _ _
  · rcases hL' with rfl | ⟨τ', rfl, hτ0, hon⟩
    · exact Or.inl hτ
    · rcases hτ with rfl | hτ
      · exact Or.inr ⟨hτ0, hon⟩
      · exact Or.inl hτ
  · refine hcomp hf ?_
    obtain ⟨p, t, hp, ht0, ht1, ⟨j, hj, hin⟩, hpt⟩ :=
      exit_in_arcs J.left hP hNF (Q := Qof P) (dirOf_cases _) hzt hf
    refine ⟨p, t, hp, ht0, ht1, ⟨j, by rwa [hN1], ?_⟩, fun g hg => absurd hg
      (List.not_mem_nil), hpt.symm⟩
    rw [w1, w7 j hj]
    obtain ⟨⟨hps, -, -⟩, ⟨hpe, -, -⟩⟩ := arc_end_facts hP hNF hj
    unfold nArc
    rwa [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1]
  · intro r hr h1 h2 h3 hrA
    rw [k2 r hr (fun h => h1 (by unfold RS at h; unfold sw; omega))
      (by unfold accA sw at *; omega) hrA]
    exact w9 r hr (fun h => by unfold BSet sw at h; unfold sw at h1 h3; omega) hrA
  · have := hA₁; have := hA2; omega
  · rw [hm2 a (by omega)]; exact w8 a ha

end

end SweepIo

end Chazelle.Core
