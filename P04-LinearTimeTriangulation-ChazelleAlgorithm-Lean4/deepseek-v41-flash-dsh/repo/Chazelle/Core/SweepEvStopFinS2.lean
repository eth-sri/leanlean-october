module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStopFinS1
public import Chazelle.Core.SweepEvStopFace4
public import Chazelle.Core.SweepEvNoParCut

/-!
# The sweep (WP-D), stage 2: the faced regions at the counterpart of a stretch attachment

`slProg fr`: normalise the position `(slfSE, slfSH)` of the walk of `C` (`normS`), compute its
offset `d` from `gW` and the counterpart positions `cpA d` (and `cpB d` at a vertex) in the walk of
`C₂` (`slAr`), and run the faced-region procedure `fr` (`FaceRTask`) there; without a parent the
counterpart inside a walk edge is not a cut (`noParCut`).

**`strLabTask : StrLabTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-- **The stretch labels.** -/
def slProg (fr : Stmt) : Stmt := .seq (normS (sw 2) slfSE slfSH sflN) (.seq slAr fr)


theorem strLabTask : StrLabTask := by
  obtain ⟨fr, κF, HF⟩ := faceRTask
  refine ⟨slProg fr, fun D => 11041 + κF D, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hE hpp hy hex h0 hL hroom
  set T := c₀.nreg TLR with hT
  set D := c₀.nreg (sw 6) with hD
  have hP := E.hP
  have hfx := E.fx hI
  have hK := E.hK.fix hI
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have hmm : J.whole.m = J.left.m + J.right.m := rfl
  have hτw := tpos_lt J.whole J.m₁
  have hτ := tpos_lt J.right 0
  set x0 : WPos := ⟨c.nreg slfSE, c.nreg slfSH⟩ with hx0
  set t := (chainModel J.whole).param (Qof P) x0 with ht
  -- 1. the normalisation
  beta_reduce at hroom
  have hT1 : 11041 ≤ 11041 * (T + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos T)
  have hsplit : (11041 + κF D) * (T + 1) = 11041 * (T + 1) + κF D * (T + 1) := ⋆
  have hroom1 : c.nreg ALLOC + 11015 ≤ W := ⋄
  unfold slProg
  refine IRS.seq (K₁ := 11015) (K₂ := 26 + κF D * (T + 1)) (normS_irs (C := J.whole) hI hK
    hfx.ctxW ⟨by unfold sw; omega, by unfold sw; omega, by unfold slfSE sw; omega,
      by unfold slfSE sw; omega, by unfold slfSH sw; omega, by unfold slfSH sw; omega⟩
    ⟨by unfold sflN sw; omega, by unfold sflN sw; omega, by unfold sflN slfSE sw; omega,
      by unfold sflN slfSH sw; omega, by unfold sflN slfSE sw; omega, by unfold sflN slfSH sw; omega,
      by unfold slfSE slfSH sw; omega⟩ hE hpp (fun _ _ _ _ => hy) hroom1) ?_ |>.mono
    (by show 11015 + (26 + κF D * (T + 1)) ≤ (11041 + κF D) * (T + 1); omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨n1, n2, n3, n4, n5⟩
  set H := nhgt (chainModel J.whole) (Qof P) x0 with hH
  obtain ⟨hppH, hparH, -, hH0⟩ := nhgt_facts hpp
  Ξ' ← ht at hparH
  Ξ' hparH at hH0
  have c1E := n1
  have c1H := n2
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ slfSH → r ≠ sflN → r ≠ sflN + 1 → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 h6 => n3 r (not_oracle_sw h1 h2) h3 h4 h5 h6
  have hfx₁ := E.fx hI₁
  -- the offset
  have hgn : gW J < (chainModel J.whole).W.n := by unfold gW; rw [hn]; omega
  set d := dOf (chainModel J.whole).W.n (gW J) (c.nreg slfSE) with hd
  have hoff : oW J (c.nreg slfSE + t) = d + t := off_key' hgn hE hpp.1 hpp.2.1
  Ξ' hoff at h0 hL
  have hdL : d < Lst J := by
    have : (d : ℝ) < Lst J := by linarith [hpp.1]
    exact_mod_cast this
  have hd0 : t = 0 → d ≠ 0 := fun h0' hd0 => by rw [h0', hd0] at h0; simp at h0
  have hEd : c.nreg slfSE = (gW J + d) % (chainModel J.whole).W.n := (add_dOf hgn hE).symm
  have hC0 := corr_right0 J hP (S₂ := ∅) (empty_subset _) finite_empty
  have hq : dq (rL1 J) (rδ J) d < (chainModel J.right).W.n := hC0.dq_lt hdL
  have hq1 : dq (rL1 J) (rδ J) (d - 1) < (chainModel J.right).W.n := hC0.dq_lt (show d - 1 < Lst J by omega)
  -- 2. the counterpart positions
  have g0 := hfx₁.r40 1 (⊛)
  have g2 := hfx₁.r40 2 (⊛)
  have g4 := hfx₁.r40 4 (⊛)
  ϴ' cstR, List.getD_cons_zero, List.getD_cons_succ at g0 g2 g4
  have e41 := g0
  have e42 := g2
  have e44 := g4
  have hδ7 : rδ J ≤ 7 := by unfold rδ; split_ifs <;> omega
  have hK₁ := E.hK.fix hI₁
  refine IRS.seq (K₁ := 26) (K₂ := κF D * (T + 1)) (slAr_irs (n := (chainModel J.whole).W.n)
    (g := gW J) (g' := 6 + tpos J.right 0) (n₂ := (chainModel J.right).W.n) hI₁
    (by rw [c1E]; exact hE) (Ρ hfx₁.nw, hn) hfx₁.gw hgn e41 (Ρ hfx₁.n2, hn₂)
    (by rw [hn₂]; omega) hK₁.1 hK₁.2.1 (by rw [e42, e44, c1E]; exact hq)
    (by rw [e42, e44, c1E]; exact hq1) (by have := E.hWn; omega) (by rw [hn, hn₂]; omega)
    (by rw [e44, hn₂]; omega)) ?_
  rintro c₂ hI₂ - - ⟨v1, v2, v3, v4, kp⟩
  ϴ' e42, e44, c1E, c1H at v1 v2 v3 v4
  have hcpA : c₂.nreg fpE = cpA J d := v1
  have hv3 : c₂.nreg fqE = if H = 0 then cpB J d else cpA J d := v3
  have hpar : (chainModel J.right).param (Qof P) ⟨cpA J d, H⟩ = t := by
    Ξ ← str_param hP hdL, ← hEd, hparH
  have hppA : ProperPos (chainModel J.right) (Qof P) P.n ⟨cpA J d, H⟩ :=
    ⟨by rw [hpar, ← hparH]; exact hppH.1, by rw [hpar, ← hparH]; exact hppH.2.1, hppH.2.2⟩
  have hcpAn : cpA J d < (chainModel J.right).W.n := Nat.mod_lt _ (⋄)
  have hcpBn : cpB J d < (chainModel J.right).W.n := Nat.mod_lt _ (⋄)
  have hppB : ProperPos (chainModel J.right) (Qof P) P.n ⟨cpB J d, 0⟩ :=
    ⟨le_refl (0 : ℝ), by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩
  -- the non-cut
  obtain ⟨e, he, hno, heA⟩ := hex
  have hnc : 0 < t → ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
      ((chainModel J.right).key (Qof P) ⟨cpA J d, H⟩) := by
    intro htp
    Ξ fr_key, hpar
    refine noParCut J (Qof P) _ e hP E.hNF₂.1 he hno d t hdL htp hpp.2.1 ?_
    rw [← hEd]; exact heA
  have hcases : t = 0 ∨ 0 < t := hpp.1.eq_or_lt.imp (fun h => h.symm) id
  have hfp : (chainModel J.right).param (Qof P) ⟨c₂.nreg fpE, c₂.nreg fpH⟩ = 0 ∨
      ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
        ((chainModel J.right).key (Qof P) ⟨c₂.nreg fpE, c₂.nreg fpH⟩) := by
    Ξ hcpA, v2
    rcases hcases with h | h
    · exact Or.inl (Ρ hpar, h)
    · exact Or.inr (hnc h)
  have hq_pos : (c₂.nreg fqE < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c₂.nreg fqE, c₂.nreg fqH⟩ ∧
      ((chainModel J.right).param (Qof P) ⟨c₂.nreg fqE, c₂.nreg fqH⟩ = 0 ∨
        ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
          ((chainModel J.right).key (Qof P) ⟨c₂.nreg fqE, c₂.nreg fqH⟩))) := by
    Ξ v3, v4
    by_cases hH' : H = 0
    · Ξ ite_eq_left hH', ite_eq_left hH'
      exact ⟨hcpBn, hppB, Or.inl rfl⟩
    · Ξ ite_eq_right hH', ite_eq_right hH'
      have htp : 0 < t := by
        rcases hcases with h | h
        · exact absurd (hH0.2 (Ρ ← h)) hH'
        · exact h
      exact ⟨hcpAn, hppA, Or.inr (hnc htp)⟩
  have kA : c₂.nreg ALLOC = c₁.nreg ALLOC := kp.1 _ (by unfold SlArW ALLOC sw; omega)
  refine (HF sh Bs F X Ok P W c₀ c₂ J N₁ N₂ E hI₂ (by rw [hcpA]; exact hcpAn)
    (by rw [hcpA, v2]; exact hppA) hfp hq_pos.1 hq_pos.2.1 hq_pos.2.2 (by
      rw [kA]; show c₁.nreg ALLOC + κF D * (T + 1) ≤ W; omega)).mono le_rfl ?_
  rintro c' ⟨f1, f2, f3, f4, f5, f6, f7⟩
  refine ⟨f1, f2, ⟨d, hdL, hd0, hEd, ?_, fun htp => ?_, fun ht0 => ?_⟩, fun a ha => ?_, ?_,
    fun r hr hS hrA => ?_⟩
  · Ξ' hcpA, v2, hpar at f3; exact f3
  · have hH' : H ≠ 0 := fun h => htp.ne' (hH0.1 h)
    Ξ' hv3, v4, ite_eq_right hH', ite_eq_right hH', hpar at f4; exact f4
  · have hH' : H = 0 := hH0.2 ht0
    Ξ' hv3, v4, ite_eq_left hH', ite_eq_left hH' at f4; exact f4
  · Ξ f5 a (by rw [kA]; omega), kp.2, n5 a ha
  · Ξ' kA at f6; omega
  · have hS' : ¬ (FRR r ∨ (sw 4096 ≤ r ∧ r < sw 4100) ∨ (sw 4110 ≤ r ∧ r < sw 4200)) := hS
    have hband : 240000 ≤ r ∧ r < 250000 → True := fun _ => trivial
    Ξ f7 r hr (fun h => hS' (Or.inl h)) hrA
    by_cases hsw : 240000 ≤ r ∧ r < 250000
    · rw [kp.1 r (by unfold SlArW sw at *; omega),
        k1 r hsw.1 hsw.2 (by unfold slfSH sw at *; omega) (by unfold sflN sw at *; omega)
          (by unfold sflN sw at *; omega) hrA]
    · rw [kp.1 r (by unfold SlArW sw at *; omega),
        n3 r hr (by unfold slfSH sw at *; omega) (by unfold sflN sw at *; omega)
          (by unfold sflN sw at *; omega) hrA]

end

end SweepEv

end Chazelle.Core
