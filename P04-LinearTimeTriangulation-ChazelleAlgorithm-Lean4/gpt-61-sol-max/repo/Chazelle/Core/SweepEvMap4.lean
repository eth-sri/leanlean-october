module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvMap2

/-!
# The sweep (WP-D), stages 2–3: the walk edges of `M₁` and `M` along the `C₁` part

At a valid `b₁`-offset `d` with a positive parameter, the walk edge of `C₁` at `(b₁ + d) % n₁`
and the walk edge of `C` at `mEdge d` are the same segment (`edge_corr`); hence a height code has
the same parameter in both models (`param_corr`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

namespace Sweep

section EdgeCorr

variable {J : Merge.Junction}

section
variable (hP : J.P.Simple) {d : ℕ} {t : ℝ} (hv : MValid J d t) (htp : 0 < t)
include hP t hv htp
/-- **The walk edges agree** at a valid offset with a positive parameter. -/
theorem edge_corr (s : ℝ) :
    sidePt (chainModel J.whole).W (mEdge J d) s =
      sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) s := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hm1 : J.left.m = J.m₁ := rfl
  have h1 := J.one_le_m₁
  have hτ₁ := tpos_lt J.left J.m₁
  
  obtain ⟨hdE, hgap, hsplit, -⟩ := hv
  have ht0 : t ≠ 0 := htp.ne'
  have viaGen : ∀ d' : ℕ, d' < lL1 J + lL2 J →
      (b₁ J + d) % (chainModel J.left).W.n =
        (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d') % (chainModel J.left).W.n →
      lOff J + d' = Lst J + ψ J d →
      sidePt (chainModel J.whole).W (mEdge J d) s =
        sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) s := by
    intro d' hd' he hoff
    have hE : mEdge J d = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d') % (chainModel J.whole).W.n := by
      rw [mEdge_def, left_edge_eq, hoff]
    rw [hE, he]
    exact (corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty).sidePt_eq hd' s
  have viaBox : ∀ d'' : ℕ, (hv' : ¬ VNotTop J) → d'' < 7 →
      (b₁ J + d) % (chainModel J.left).W.n = (2 * J.left.m + 6 + d'') % (chainModel J.left).W.n →
      gW J + (Lst J + ψ J d) = 2 * J.whole.m + 6 + d'' →
      sidePt (chainModel J.whole).W (mEdge J d) s =
        sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) s := by
    intro d'' hv' hd'' he hidx
    have hE : mEdge J d = (2 * J.whole.m + 6 + d'') % (chainModel J.whole).W.n := by
      rw [mEdge_def, hidx]
    rw [hE, he]
    exact (box_agree J hv').sidePt_eq hd'' s
  by_cases hVNT : VNotTop J
  · have hlOff : lOff J = Lst J := by rw [lOff_of_vnt J hVNT, Lst_rlen]
    have hlen : Lst J + llen J = (chainModel J.whole).W.n := by
      rw [Lst_rlen]; exact rlen_add_llen J hVNT
    have hb : b₁ J = 6 + tpos J.left J.m₁ := by grind [b₁]
    have hE₁ : E₁ J = llen J + lδ J := by unfold E₁; omega
    have hL := lL1_add_lL2 J
    rw [hE₁] at hdE
    rw [hb] at viaGen ⊢
    by_cases hdl : d < lL1 J
    · have hψ : ψ J d = d := by grind [ψ]
      refine viaGen d (by omega) ?_ (by omega)
      unfold dq; rw [ite_eq_left hdl]
    · by_cases hδ : lδ J = 0
      · have := lL2_of_lδ hδ; omega
      · have hδ' : 0 < lδ J := by omega
        obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ'
        rw [h7] at hgap hsplit hdE
        have hd1 : d ≠ lL1 J := fun hd1 => hsplit ⟨by omega, hd1, ht0⟩
        have hd2 : lL1 J + 7 ≤ d := by
          omega
        have hψ : ψ J d = d - 7 := by
          grind [ψ]
        refine viaGen (d - 7) (by omega) ?_ (by omega)
        unfold dq; rw [ite_eq_right (by omega), h7, show d - 7 + 7 = d by omega]
  · obtain ⟨hτ0, hδ0, hl1, hl2, hll⟩ := nvt_left J hP hVNT
    have hψ : ψ J d = d := by grind [ψ]
    by_cases hbox : Lst J < lOff J
    · obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
      have hb : b₁ J = 2 * J.left.m + 6 := by grind [b₁]
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by grind [E₁]
      rw [hE₁] at hdE
      rw [hb] at viaGen ⊢
      by_cases hd7 : d < 7
      · have := viaBox d hVNT hd7 (by rw [hb]) (by grind [gW])
        rwa [hb] at this
      · refine viaGen (d - 7) (by omega) ?_ (by omega)
        unfold dq; rw [ite_eq_left (by omega), hτ0, hn₁]
        rw [show 2 * J.left.m + 6 + d = (6 + 0 + (d - 7)) + (2 * J.left.m + 7) by omega,
          Nat.add_mod_right]
    · obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
      have hb : b₁ J = 6 + tpos J.left J.m₁ := by grind [b₁]
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by grind [E₁]
      rw [hE₁] at hdE
      rw [hb, hτ0] at viaGen ⊢
      by_cases hd2 : d < 2 * J.m₁
      · refine viaGen d (by omega) ?_ (by rw [hψ, hlo])
        grind [dq]
      · have := viaBox (d - 2 * J.m₁) hVNT (by omega) (by
          rw [hb, hτ0]
          congr 1
          omega) (by grind [gW])
        rwa [hb, hτ0] at this

/-- **A height code has the same parameter** in `M` at `mEdge d` and in `M₁` at `(b₁ + d) % n₁`
(valid offset, positive parameter). -/
theorem param_corr
    (Q : Polygon) (h : ℕ) :
    (chainModel J.whole).param Q ⟨mEdge J d, h⟩ =
      (chainModel J.left).param Q ⟨(b₁ J + d) % (chainModel J.left).W.n, h⟩ := by
  have e0 := edge_corr hP hv htp 0
  have e1 := edge_corr hP hv htp 1
  simp only [Chazelle.Chain.sidePt_zero] at e0
  have hwa : (chainModel J.whole).wa (mEdge J d) =
      (chainModel J.left).wa ((b₁ J + d) % (chainModel J.left).W.n) := e0
  have hwb : (chainModel J.whole).wb (mEdge J d) =
      (chainModel J.left).wb ((b₁ J + d) % (chainModel J.left).W.n) := by
    simp_all [Model.wb, Nat.mod_add_mod, Chazelle.Chain.sidePt, Geometry.lerp_one] <;> omega_nf
  unfold Model.param
  simp_all


end

end EdgeCorr

end Sweep

end

end Chazelle.Core
