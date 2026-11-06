module

public import Chazelle.Core.SweepEvDone
public import Chazelle.Core.SweepEvStepL0

/-!
# The sweep (WP-D), stage 3: the last iteration (task L2), the outputs

`done_out`: from `EvEnv`, `LoopInv` at the start of the last iteration, `IterRel` and `dF = 1`,
given that no cut of `F₂⁺` lies after the last key (`hnc`, the shared step-1 fact), the outputs
`Out` and the size of the log.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

section done

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {J : Merge.Junction} {N₁ N₂ : NF} {c₀ c cw cs co c' : Config}

set_option maxHeartbeats 8000000 in
/-- **The outputs of the last iteration.** -/
theorem done_out (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hIt : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 1)
    (hnc : NoCutIn J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c)
      (chainModel J.whole).W.n) :
    Out P J N₂ (finCfg c') ∧ c'.nreg lC ≤ logCap N₁ N₂ := by
  set S₂ := N₂.F (chainModel J.right) (Qof P)
  have hIt' := hIt
  obtain ⟨⟨rs₀, -, -, -, -, -, -, -, -, -, hWm, hWr⟩, hAw, ⟨hRm, -, -, hRr⟩,
    ⟨hBfr, hBA, A, hB⟩, hK⟩ := hIt'
  -- the no-candidate case of the next key
  have hnone : co.nreg bF ≠ 1 ∧ ¬ co.nreg sP < co.nreg sC ∧ co.nreg wX ≠ 0 := by
    by_contra h
    have h' : co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0 := by tauto
    have := (hK.2.2.2 h').1
    omega
  obtain ⟨-, hlC, hmK⟩ := hK.2.2.1 hnone
  -- registers
  have keepK : ∀ r, 240000 ≤ r ∧ r < 250000 → ¬ KR r → c'.nreg r = co.nreg r := fun r hr hk =>
    hK.1 r (band_sw_not hr) hk (by unfold ALLOC; omega)
  have eSB : c'.nreg sB = c.nreg sB := by
    rw [keepK _ (by unfold sB sw; omega) (by unfold KR kE kH kN kL sP dF lC sB sw; omega)]
    exact done_iter_keep hIt (by unfold sB sw; omega) (by unfold WR sB sw; omega)
      ⟨by unfold sB bF sw; omega, by unfold sB bN sw; omega⟩
      (by unfold OrgR CandR BestR LblR sB bF bE bH bN bL sw; omega) (by unfold LR oK oS sB sw; omega)
  have eSC : c'.nreg sC = c.nreg sC := by
    rw [keepK _ (by unfold sC sw; omega) (by unfold KR kE kH kN kL sP dF lC sC sw; omega)]
    exact done_iter_keep hIt (by unfold sC sw; omega) (by unfold WR sC sw; omega)
      ⟨by unfold sC bF sw; omega, by unfold sC bN sw; omega⟩
      (by unfold OrgR CandR BestR LblR sC bF bE bH bN bL sw; omega) (by unfold LR oK oS sC sw; omega)
  have eLB : c'.nreg lB = c.nreg lB := by
    rw [keepK _ (by unfold lB sw; omega) (by unfold KR kE kH kN kL sP dF lC lB sw; omega)]
    exact done_iter_keep hIt (by unfold lB sw; omega) (by unfold WR lB sw; omega)
      ⟨by unfold lB bF sw; omega, by unfold lB bN sw; omega⟩
      (by unfold OrgR CandR BestR LblR lB bF bE bH bN bL sw; omega) (by unfold LR oK oS lB sw; omega)
  have eTB : c'.nreg cTB = c.nreg cTB := by
    rw [keepK _ (by unfold cTB sw; omega) (by unfold KR kE kH kN kL sP dF lC cTB sw; omega)]
    exact done_iter_keep hIt (by unfold cTB sw; omega) (by unfold WR cTB sw; omega)
      ⟨by unfold cTB bF sw; omega, by unfold cTB bN sw; omega⟩
      (by unfold OrgR CandR BestR LblR cTB bF bE bH bN bL sw; omega)
      (by unfold LR oK oS cTB sw; omega)
  have eLC : c'.nreg lC = c.nreg lC := by
    rw [hlC]
    exact done_iter_keep hIt (by unfold lC sw; omega) (by unfold WR lC sw; omega)
      ⟨by unfold lC bF sw; omega, by unfold lC bN sw; omega⟩
      (by unfold OrgR CandR BestR LblR lC bF bE bH bN bL sw; omega) (by unfold LR oK oS lC sw; omega)
  have eTBs : cs.nreg cTB = c.nreg cTB := by
    rw [hRr _ (by unfold cTB bF sw; omega) (by unfold cTB bN sw; omega),
      hWr _ (band_sw_not (by unfold cTB sw; omega)) (by unfold WR cTB sw; omega)
        (by unfold cTB ALLOC sw; omega)]
  have hT0 : c.nreg cTB = c₀.nreg cTB := by rw [hL.tab0, E.hTA]
  -- the allocators
  have hAs : cs.nreg ALLOC = cw.nreg ALLOC := hRr ALLOC (by unfold ALLOC bF sw; omega)
    (by unfold ALLOC bN sw; omega)
  have hAco : c.nreg ALLOC ≤ co.nreg ALLOC := by omega
  -- the memory outside the table
  have memC : ∀ x, x < c.nreg ALLOC → (x < c.nreg cTB ∨ c.nreg cTB + 6 * N₂.nChords ≤ x) →
      c'.nmem x = c.nmem x := fun x hx hxT => by
    rw [hmK x (by omega)]
    exact done_iter_mem hIt hT0 (by rw [eTBs, hT0]) hx hxT
  -- the layout
  have l1 := hL.lay1
  have l2 := hL.lay2
  have l4 := hL.lay4
  -- the size of the log
  obtain ⟨-, hcnt⟩ := countTask P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hmeas := hL.meas
  have hcap : c.nreg lC ≤ logCap N₁ N₂ := by
    have : (keyS P J N₁ N₂).ncard ≤ 4 * N₂.nChords + 2 * N₁.nChords + 9 := hcnt
    unfold logCap; omega
  -- the table
  set T := c.nreg cTB
  have tabF : ∀ j, j < 2 * N₂.nChords →
      c'.nmem (T + 3 * j) ≤ 1 ∧
      (c'.nmem (T + 3 * j) = 1 → CandOK P J S₂ (endOrigin J (Qof P) N₂ j) (endDir j)
        (c'.nmem (T + 3 * j + 1)) (c'.nmem (T + 3 * j + 2))) ∧
      (c.nmem (T + 3 * j) = 1 → c'.nmem (T + 3 * j) = 1) := by
    intro j hj
    have hTA : T + 3 * j + 2 < c.nreg ALLOC := by omega
    have mc : ∀ x, x ≤ T + 3 * j + 2 → c'.nmem x = co.nmem x := fun x hx => hmK x (by omega)
    have ms : ∀ x, x ≤ T + 3 * j + 2 → cs.nmem x = c.nmem x := fun x hx => by
      rw [hRm, hWm x (by omega)]
    obtain ⟨t0, t1, -⟩ := hL.tab j hj
    rcases hB.slot j hj with ⟨s0, s1, s2⟩ | ⟨e, h, hA, s0, s1, s2⟩
    · rw [eTBs] at s0 s1 s2
      rw [mc _ (by omega), s0, ms _ (by omega), mc _ (by omega), s1, ms _ (by omega),
        mc _ (by omega), s2, ms _ (by omega)]
      exact ⟨t0, t1, id⟩
    · rw [eTBs] at s0 s1 s2
      rw [mc _ (by omega), s0, mc _ (by omega), s1, mc _ (by omega), s2]
      exact ⟨le_rfl, fun _ => (hB.acc _ hA).2.2, fun _ => rfl⟩
  -- the parts of the output
  obtain ⟨rs, ax, hrl, -, hsr, -, hsok, hsw, -, -⟩ := hL.stops
  obtain ⟨ls, hll, hlr, hlw, hlp, hlast⟩ := hL.log
  obtain ⟨f200, f201, f300, f301, f302, fm⟩ := fin_rd c'
  refine ⟨⟨rs, ls, ?_, ?_, hsok, hsw, ?_, ?_, ?_, hlw, ?_, ?_⟩, by rwa [eLC]⟩
  · rwa [f201, eSC]
  · rw [fm, f200, eSB]
    intro i hi
    obtain ⟨a0, a1, a2, a3, a4⟩ := hsr i hi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
  · rwa [f301, eLC]
  · rw [fm, f300, eLB]
    intro i hi
    have hlog : c.nreg lB + 7 * c.nreg lC ≤ c.nreg ALLOC := by unfold logCap at l2 hcap; omega
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hlr i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
    · rwa [memC _ (by omega) (Or.inr (by omega))]
  · -- the log
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hlp
    refine ⟨p1, p2, p3, p4, p5, fun x hx => ?_, p6⟩
    unfold logOf at hx
    rw [List.getLast?_map, hlast] at hx
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
    subst hx
    exact hnc
  · -- the table
    rw [fm, f302, eTB]
    intro j hj haR hav hat
    obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Qof P) (N := N₂) hj
    have hS₂sub : S₂ ⊆ Merge.augChords J.right := E.hNF₂.1.2.1
    obtain ⟨hfr, ha₂, -, -, -, -⟩ := right_hit_end (hS₂sub hc) ha
    have hfree := whole_free_end E.hP haR hav hfr
    obtain ⟨g0, g1, g2⟩ := tabF j hj
    refine ⟨hfree, ?_⟩
    unfold tabOf
    split_ifs with hf
    · obtain ⟨-, -, hatt, hpt, hLst, -, -⟩ := g1 hf
      exact ⟨hatt, hpt, hLst⟩
    · have hσ : endDir j = 1 ∨ endDir j = -1 := by
        rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      have haw : (endOrigin J (Qof P) N₂ j).2 ≤ J.whole.top.2 := le_trans ha₂ J.right_top_le
      have hle : J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) ≤
          J.right.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) := by
        rw [whole_hitParam_eq_min J haw hσ, ← right_hitParam_eq J ha₂]
        exact min_le_right _ _
      refine le_antisymm hle (not_lt.1 fun hlt => ?_)
      obtain ⟨-, p, t, hp, ht0, ht1, hatt, hpt, hLst, -⟩ :=
        (originTask J (Qof P) N₂ E.hP E.hNF₂ (F₂plus_chordFamily E)).1 j hj haR hav hat hlt
      by_cases ho : oW J (p + t) ≤ keyOff P J c
      · exact hf (g2 ((hL.tab j hj).2.2 ⟨haR, hav, hat⟩ hlt p t hatt hpt hLst ho))
      · have hpn : (p : ℝ) + t < (chainModel J.whole).W.n := by
          have : (p : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hp
          linarith
        refine hnc (p + t) ⟨_, shoot_end_mem hc ha hfree, p, t, hatt, rfl⟩ (by positivity) hpn
          ⟨lt_of_not_ge ho, ?_⟩
        exact off_lt hpn (Nat.cast_nonneg _)
  · -- the table words
    rw [fm, f302, eTB]
    intro j hj
    obtain ⟨g0, g1, -⟩ := tabF j hj
    exact ⟨g0, fun h => (g1 h).2.2.2.2.2.1⟩

end done

end

end SweepEv

end Chazelle.Core
