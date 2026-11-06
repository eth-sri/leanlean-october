module

public import Chazelle.Core.SweepEvCand
public import Chazelle.Core.SweepEvMap4
public import Chazelle.Core.SweepMachine5
public import Chazelle.Core.RestoreTShot
public import Chazelle.Core.SweepEvSpec
public import Chazelle.Core.SweepEvMapR

/-!
# The sweep (WP-D), stage 3: the facts of an accepted candidate (mathematics)

* `arrival_unique`: a genuine hit of `C₁` has one arrival position;
* `posW_of_inner`: a position of the walk of `C` strictly inside the box height band is a
  `PosW` position;
* `CandOK`: the accepted candidate data; `candOK_of`: from the checks of the RAM.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

variable {J : Merge.Junction}

/-- **A genuine hit has one arrival position.** -/
theorem arrival_unique {C : Chain} (hP : C.P.Simple) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine C a σ τ) {p p' : ℕ} {t t' : ℝ}
    (hA : Arrival (chainModel C).W (rayPt a σ τ) σ p t)
    (hA' : Arrival (chainModel C).W (rayPt a σ τ) σ p' t') : p = p' ∧ t = t' := by
  obtain ⟨hτ, hdom, hwD⟩ := hg
  set w := rayPt a σ τ with hw
  have hback : ∀ s, rayPt w (-σ) s = rayPt a σ (τ - s) := fun s => rayPt_back a σ τ s
  have hw2 : w.2 ≤ C.top.2 := by rw [hw, rayPt_snd]; exact ha
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hfree : FreeAt C w (-σ) := by
    filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
    rw [hback]; exact hdom _ (by linarith [hs.2]) (by linarith [hs.1])
  have he : Merge.shoot C w (-σ) ∈ Merge.augChords C :=
    Merge.shoot_mem_augChords C hw2 hwD hnσ hfree
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C hw2 hnσ hfree
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ Merge.shoot C w (-σ) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    unfold Merge.shoot
    rw [Geometry.mem_segment_iff_lerp]
    refine ⟨s / C.hitParam w (-σ), div_nonneg hs.1.le hT.le, (div_le_one hT).2 hs.2.le, ?_⟩
    apply point_ext
    · simp only [Geometry.lerp_fst, rayPt_fst]
      field_simp
      ring
    · simp only [Geometry.lerp_snd, rayPt_snd]; ring
  have att : ∀ {q : ℕ} {u : ℝ}, Arrival (chainModel C).W w σ q u →
      SideAttach (chainModel C).W (Merge.shoot C w (-σ)) q u := by
    intro q u h
    obtain ⟨hq, hu0, hu1, hpt, hsec⟩ := h
    have he' := he
    have hev' := hev
    rw [← hpt] at hsec hev' he'
    have := sideAttach_of_along C hP he' hq hu0 hu1 hnσ hsec hev'
    rwa [hpt] at this
  have hM : WalkAx (chainModel C) := FactsChain.walkAx C hP
  exact hM.attach_unique he (att hA) (att hA') (by rw [hA.2.2.2.1, hA'.2.2.2.1])

/-- **A walk position strictly inside the height band of the box** is a `PosW` position. -/
theorem posW_of_inner {P : Polygon} {e h : ℕ} (he : e < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨e, h⟩)
    (hy : |((chainModel J.whole).pos (Qof P) ⟨e, h⟩).2| < J.whole.radius) : SweepEv.PosW P J e h := by
  refine ⟨he, hpp, fun h0 => ?_⟩
  by_contra h6
  push Not at h6
  subst h0
  have hv : (chainModel J.whole).pos (Qof P) ⟨e, 0⟩ = (chainModel J.whole).W.vtx e := by
    show sidePt _ _ ((chainModel J.whole).param (Qof P) ⟨e, 0⟩) = _
    rw [show (chainModel J.whole).param (Qof P) ⟨e, 0⟩ = 0 from rfl, Chazelle.Chain.sidePt_zero]
  rw [hv, Restore.chain_box_vtx_abs J.whole h6] at hy
  exact lt_irrefl _ hy

/-- **An accepted candidate**: the chord of `C` seen from `a` in the direction `σ` belongs to
`F₂⁺`, ends at the position `(e, h)` of the `C₁` part, before the far end of the chord of `C₂`. -/
def CandOK (P : Polygon) (J : Merge.Junction) (S₂ : Set (Set Point)) (a : Point) (σ : ℝ)
    (e h : ℕ) : Prop :=
  FreeAt J.whole a σ ∧ Merge.shoot J.whole a σ ∈ F₂plus J S₂ ∧
    SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) e
      ((chainModel J.whole).param (Qof P) ⟨e, h⟩) ∧
    sidePt (chainModel J.whole).W e ((chainModel J.whole).param (Qof P) ⟨e, h⟩) =
      rayPt a σ (J.whole.hitParam a σ) ∧
    (Lst J : ℝ) ≤ oW J (e + (chainModel J.whole).param (Qof P) ⟨e, h⟩) ∧ SweepEv.PosW P J e h ∧
    J.whole.hitParam a σ < J.right.hitParam a σ

/-- `b₁ < n₁`. -/
theorem b₁_lt : b₁ J < (chainModel J.left).W.n := by
  have := tpos_lt J.left J.m₁
  have hn : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm1 : J.left.m = J.m₁ := rfl
  unfold b₁; split_ifs <;> omega

/-- **The checks of the RAM give an accepted candidate.** -/
theorem candOK_of {P : Polygon} (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point} (hc : c ∈ S₂)
    {a : Point} {σ : ℝ} (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ}
    (hg : Genuine J.left a σ τ) (hlt : τ < (Merge.rend c).1 - (Merge.lend c).1) {pA hN : ℕ}
    (hpA : pA < (chainModel J.left).W.n)
    (hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨pA, hN⟩)
    (hnorm : hN = 0 ↔ (chainModel J.left).param (Qof P) ⟨pA, hN⟩ = 0)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ pA
      ((chainModel J.left).param (Qof P) ⟨pA, hN⟩))
    (hMV : SweepEv.MVal J ((pA + (chainModel J.left).W.n - b₁ J) % (chainModel J.left).W.n) hN) :
    CandOK P J S₂ a σ (mEdge J ((pA + (chainModel J.left).W.n - b₁ J) % (chainModel J.left).W.n))
      hN := by
  set n₁ := (chainModel J.left).W.n with hn₁
  set d := (pA + n₁ - b₁ J) % n₁ with hd
  set t := (chainModel J.left).param (Qof P) ⟨pA, hN⟩ with ht
  have hb := (b₁_lt (J := J))
  have hpd : (b₁ J + d) % n₁ = pA := by
    rw [hd, Nat.add_mod_mod, show b₁ J + (pA + n₁ - b₁ J) = pA + n₁ by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hpA]
  obtain ⟨h1, h2, h3⟩ := hMV
  have hMV' : d < E₁ J ∧ ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J) ∧
      ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0) :=
    ⟨h1, h2, fun h => h3 ⟨h.1, h.2.1, fun h0 => h.2.2 (hnorm.1 h0)⟩⟩
  rw [← hpd] at hA
  obtain ⟨hfree, hhit, hmem, hS, hpt, hO⟩ := cand_sound hP hS₂ hS₂f hc ha haR hav ha₁ hg hlt hMV' hA
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨-, ha₂, -, hR, -, -⟩ := right_hit_end (hS₂ hc) ha
  have hpar : (chainModel J.whole).param (Qof P) ⟨mEdge J d, hN⟩ = t := by
    rcases hpp.1.lt_or_eq with htp | ht0
    · have hv : MValid J d t := ⟨h1, h2, fun h => h3 ⟨h.1, h.2.1, fun h0 => h.2.2 (hnorm.1 h0)⟩,
        fun h => absurd h htp.ne'⟩
      rw [param_corr hP hv htp, hpd]
    · have h0 : hN = 0 := hnorm.2 ht0.symm
      have ht0' : t = 0 := ht0.symm
      rw [ht0', h0]; rfl
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  rw [← hpar] at hS hpt hO
  have hlt' : mEdge J d < (chainModel J.whole).W.n := by
    unfold mEdge; exact Nat.mod_lt _ (by omega)
  refine ⟨hfree, hmem, hS, by rw [hpt, hhit], ?_, posW_of_inner hlt'
    ⟨by rw [hpar]; exact hpp.1, by rw [hpar]; exact hpp.2.1, hpp.2.2⟩ ?_, ?_⟩
  · rw [hO]
    have : (0 : ℝ) ≤ ψ J d := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (chainModel J.whole).param (Qof P) ⟨mEdge J d, hN⟩ := by rw [hpar]; exact hpp.1
    linarith
  · show |(sidePt (chainModel J.whole).W (mEdge J d)
      ((chainModel J.whole).param (Qof P) ⟨mEdge J d, hN⟩)).2| < J.whole.radius
    rw [hpt, rayPt_snd]
    have hRR : J.whole.radius = J.right.radius := rfl
    rw [hRR]
    exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2 J.right.coordBound_lt_radius
  · rw [hhit, hR]; exact hlt

/-- **The `C₁` part is read within one turn of the walk of `C₁`.** -/
theorem E₁_le (hP : J.P.Simple) : E₁ J ≤ (chainModel J.left).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm1 : J.left.m = J.m₁ := rfl
  by_cases hVNT : VNotTop J
  · have hlen : Lst J + llen J = (chainModel J.whole).W.n := by
      rw [Lst_rlen]; exact rlen_add_llen J hVNT
    unfold E₁
    have hll := lL1_add_lL2 J
    unfold llen lδ at *
    split_ifs at * <;> omega
  · obtain ⟨hτ0, hδ0, hl1, hl2, hll⟩ := nvt_left J hP hVNT
    unfold E₁
    by_cases hbox : Lst J < lOff J
    · obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
      have hm : J.whole.m = J.m₁ + J.m₂ := rfl
      omega
    · obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
      have hm : J.whole.m = J.m₁ + J.m₂ := rfl
      omega

end Sweep

end

end Chazelle.Core
