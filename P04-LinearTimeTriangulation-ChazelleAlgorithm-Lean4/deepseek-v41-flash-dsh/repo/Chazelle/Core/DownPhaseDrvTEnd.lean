module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvTShift

/-!
# Down-phase transition (D2), part 2: which chain positions see the interior

For the top chain `C` of `Q` and a chord `c` of the chain model attached at the chain walk
position `(p, t)`: if the points of `c` near the end are interior points of `Q`, then the
position lies on the inner run of the chain walk: `c₀ ≤ p ≤ c₀ + m`, and `t = 0` when
`p = c₀ + m` (`inner_of_interior`).  The proof finds the interior walk position `(j, s)` of the
end (a boundary point of `Q`), exhibits the matching chain walk position on the inner run
(`Trans.Shift.sec_eq` inside the run, `sideLeft_uturn` at its two ends, which are turns of the
walk unless they are the top vertex) and concludes by the uniqueness of attachment positions
of the chain model (`pos_eq_of_sector`, from the walk axiom `ends`).  The open last edge
`e_{n-1}` lies in the domain of the chain (`openLast_mem_dom`), so no chain walk position is
there.
-/

namespace Chazelle.Core

namespace DrvT

@[expose] public section

open Set Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)

/-- **Points of a horizontal segment near any of its points.** -/
theorem hseg_near {y a b : ℝ} (hab : a < b) {e : Point} (he : e ∈ hseg y a b) {r : ℝ}
    (hr : 0 < r) : ∃ x ∈ hseg y a b, x ≠ e ∧ dist x e < r := by
  obtain ⟨hy, hae, heb⟩ := he
  have hdist : ∀ δ : ℝ, dist ((e.1 + δ, y) : Point) e = |δ| := by
    intro δ
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy, sub_self, abs_zero,
      show e.1 + δ - e.1 = δ by ring]
    exact max_eq_left (abs_nonneg _)
  have hne : ∀ δ : ℝ, δ ≠ 0 → ((e.1 + δ, y) : Point) ≠ e := by
    intro δ hδ h
    have := congrArg Prod.fst h
    simp only at this
    exact hδ (⟡)
  rcases heb.lt_or_eq with h | h
  · set δ := min (r / 2) ((b - e.1) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (⟡) (⟡)
    have hδ1 : δ ≤ r / 2 := min_le_left _ _
    have hδ2 : δ ≤ (b - e.1) / 2 := min_le_right _ _
    refine ⟨(e.1 + δ, y), ⟨rfl, by simp only; linarith, by simp only; linarith⟩, hne δ hδ0.ne',
      ?_⟩
    rw [hdist, abs_of_pos hδ0]; linarith
  · set δ := min (r / 2) ((e.1 - a) / 2) with hδ
    have hea : a < e.1 := ⟡
    have hδ0 : 0 < δ := lt_min (⟡) (⟡)
    have hδ1 : δ ≤ r / 2 := min_le_left _ _
    have hδ2 : δ ≤ (e.1 - a) / 2 := min_le_right _ _
    refine ⟨(e.1 + -δ, y), ⟨rfl, by simp only; linarith, by simp only; linarith⟩,
      hne (-δ) (⟡), ?_⟩
    rw [hdist, abs_neg, abs_of_pos hδ0]; linarith

/-- **Uniqueness of attachment positions** in a model with the walk axioms: a position with the
same point whose left sector contains the points of the chord near it is the attachment
position. -/
theorem pos_eq_of_sector {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach M.W c p t) (hp' : p' < M.W.n) (ht' : 0 ≤ t')
    (ht1' : t' < 1) (hpt : sidePt M.W p' t' = sidePt M.W p t)
    (hsec : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt M.W p t → dist x (sidePt M.W p t) < r →
      sideLeft M.W p' t' x)
    (hnear : ∀ r > 0, ∃ x ∈ c, x ≠ sidePt M.W p t ∧ dist x (sidePt M.W p t) < r) :
    p' = p ∧ t' = t := by
  obtain ⟨hp, ht0, ht1, hmem, rA, hrA, hsA⟩ := hA
  obtain ⟨rS, hrS, hS⟩ := hsec
  obtain ⟨a, b, hab, hcab, -, hopen, hEa, hEb⟩ := hM.ends c hc
  set e := sidePt M.W p t with he
  have heD : e ∉ M.D := hM.trace p hp t ht0 ht1.le
  have hend : WalkEnd M.W c e := by
    Ξ' hcab at hmem
    obtain ⟨s, hs0, hs1, hs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hmem
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exact absurd (hs ▸ hopen s ⟨h0, h1⟩) heD
      · Ξ' h1, Chazelle.Geometry.lerp_one at hs; rw [hs]; exact hEb
    · Ξ' ← h0, Chazelle.Geometry.lerp_zero at hs; rw [hs]; exact hEa
  by_contra hne
  have hne' : p = p' → t ≠ t' := fun h1 h2 => hne ⟨h1.symm, h2.symm⟩
  obtain ⟨r, hr, hdis⟩ := hend.2 p p' t t' hp ht0 ht1 hp' ht' ht1' hne' rfl hpt
  obtain ⟨x, hx, hxe, hxd⟩ := hnear (min r (min rA rS)) (lt_min hr (lt_min hrA hrS))
  have h1 : dist x e < r := lt_of_lt_of_le hxd (min_le_left _ _)
  have h2 : dist x e < rA := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : dist x e < rS := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
  exact hdis x (mem_ball.2 h1) (hsA x hx hxe h2) (hS x hx hxe h3)

variable {Q : Polygon} {C : Chain}

/-- **Interior points lie strictly below the top vertex.** -/
theorem int_lt_top (hQ : Q.Simple) (T : Trans.Top Q C) {x : Point}
    (hx : x ∈ Q.filled \ Q.boundary) : x.2 < C.top.2 := by
  have hO := Chazelle.Jordan.isOpen_filled_sdiff_boundary hQ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x hx
  have hmem : ((x.1, x.2 + ε / 2) : Point) ∈ Q.filled \ Q.boundary := hball (by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show x.2 + ε / 2 - x.2 = ε / 2 by ring, abs_of_pos (⟡)]
    exact max_lt hε (⟡))
  have := T.filled_below_top hQ hmem.1
  simp only at this
  linarith

/-- A point strictly inside a segment with ends at distinct heights has neither end's
height. -/
theorem lerp_snd_ne {A B : Point} (h : A.2 ≠ B.2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (lerp A B s).2 ≠ A.2 ∧ (lerp A B s).2 ≠ B.2 ∧
      (lerp A B s).2 < max A.2 B.2 := by
  Ξ Chazelle.Geometry.lerp_snd
  obtain ⟨h0, h1⟩ := hs
  have hd : B.2 - A.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  refine ⟨fun e => hd ?_, fun e => hd ?_, ?_⟩
  · have : s * (B.2 - A.2) = 0 := ⟡
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · have : (s - 1) * (B.2 - A.2) = 0 := ⟡
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rcases lt_or_gt_of_ne h with h' | h'
    · rw [max_eq_right h'.le]; nlinarith
    · rw [max_eq_left h'.le]; nlinarith

variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

omit hQ T hD hli in
/-- Distinct interior walk vertices have distinct heights. -/
theorem iw_snd_ne (_hQ : Q.Simple) (_T : Trans.Top Q C) (hD : Trans.DistinctH Q)
    (hli : li = true ↔ Mountain.LeftInside Q) {j k : ℕ} (hj : j < Q.n) (hk : k < Q.n)
    (hjk : j ≠ k) :
    ((interiorWalk Q).vtx j).2 ≠ ((interiorWalk Q).vtx k).2 := by
  Ξ iw_vtx_idx hli hj, iw_vtx_idx hli hk
  refine hD _ _ (idxI_lt hj) (idxI_lt hk) ?_
  unfold idxI; split_ifs <;> omega

omit hli in
/-- **The open last edge lies in the domain of the top chain.** -/
theorem openLast_mem_dom {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lerp (Q.vtx C.m) (Q.vtx 0) s ∈ C.dom := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
  obtain ⟨hne1, hne2, hlt⟩ := lerp_snd_ne hh hs
  set e := lerp (Q.vtx C.m) (Q.vtx 0) s with he
  have heE : e ∈ Q.edge C.m := by
    rw [T.last_edge]; exact Chazelle.Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
  have hefill : e ∈ Q.filled := Or.inl ⟨C.m, by omega, heE⟩
  refine C.mem_dom_iff.2 ⟨?_, ?_, ?_⟩
  · have hsq := Chazelle.Jordan.filled_subset_square Q hefill
    have := C.coordBound_lt_radius
    rw [T.hP] at this
    exact ⟨lt_of_le_of_lt hsq.1 this, lt_of_le_of_lt hsq.2 this⟩
  · rintro ⟨k, hk, hek⟩
    rw [T.chainEdge_eq' hk] at hek
    have hint := hQ.2.2 k C.m (by omega) (by omega) (by omega)
    have hc : e ∈ Q.commonEndpoints k C.m := by rw [← hint]; exact ⟨hek, heE⟩
    rcases hc.2 with h | h
    · exact hne1 (by rw [h])
    · rw [show (C.m + 1) % Q.n = 0 by rw [hmn, Nat.mod_self]] at h
      exact hne2 (by rw [h])
  · intro hsl
    have h2 := (C.mem_slit_iff.1 hsl).2.1
    have hv1 := T.vtx_le_top (show C.m < Q.n by omega)
    have hv2 := T.vtx_le_top (show 0 < Q.n by omega)
    have : max (Q.vtx C.m).2 (Q.vtx 0).2 ≤ C.top.2 := max_le hv1 hv2
    linarith

/-- **A chord of the chain model whose points near its end are interior is attached on the
inner run.** -/
theorem inner_of_interior {c : Set Point} (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach (C.sideWalk C.sideBeta) c p t)
    (hnear : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt (C.sideWalk C.sideBeta) p t →
      dist x (sidePt (C.sideWalk C.sideBeta) p t) < r → x ∈ Q.filled \ Q.boundary) :
    c0 C li ≤ p ∧ p ≤ c0 C li + C.m ∧ (p = c0 C li + C.m → t = 0) := by
  have hP : C.P.Simple := by rw [T.hP]; exact hQ
  have hMC := walkAx_chainModel hP
  have hmn := T.hm
  have hm1 := C.one_le
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have H := shift_c0 hQ T hD hli
  have hle := i0_le hQ T hD hli
  have hWn : (C.sideWalk C.sideBeta).n = 2 * C.m + 7 := Chain.sideWalk_n _ _
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  set W := C.sideWalk C.sideBeta with hW
  set e := sidePt W p t with he
  have hc' := hc
  obtain ⟨y, a, b, hch, -, rfl⟩ := hc'
  have hA' := hA
  obtain ⟨hp, ht0, ht1, hemem, -⟩ := hA'
  obtain ⟨rN, hrN, hN⟩ := hnear
  have hnearc : ∀ r > 0, ∃ x ∈ hseg y a b, x ≠ e ∧ dist x e < r :=
    fun r hr => hseg_near hch.lt hemem hr
  -- the end is a boundary point of `Q`
  have heD : e ∉ C.dom := hMC.trace p hp t ht0 ht1.le
  have hefill : e ∈ Q.filled := by
    have : e ∈ closure (Q.filled \ Q.boundary) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨x, hx, hxe, hxd⟩ := hnearc _ (lt_min hε hrN)
      exact ⟨x, hN x hx hxe (lt_of_lt_of_le hxd (min_le_right _ _)), by
        rw [dist_comm]; exact lt_of_lt_of_le hxd (min_le_left _ _)⟩
    exact closure_minimal (fun z hz => hz.1) (Chazelle.Jordan.isClosed_filled Q) this
  have hebd : e ∈ Q.boundary := by
    by_contra h
    exact heD (T.interior_sub_dom hQ ⟨hefill, h⟩)
  -- its interior walk position
  obtain ⟨j, hj, s, hs0, hs1, hjs⟩ :=
    FactsInterior.exists_pos_of_mem_boundary (W := interiorWalk Q) (by rw [hWb]; exact hebd)
  rw [hIn] at hj
  obtain ⟨rI, hrI, hI⟩ := FactsInterior.interior_left hWs hWo (by rw [hIn]; exact hj) hs0 hs1
  -- the points of the chord near the end are in the interior walk's sector
  have hsecI : ∃ r > 0, ∀ x ∈ hseg y a b, x ≠ e → dist x e < r →
      sideLeft (interiorWalk Q) j s x := by
    refine ⟨min rN rI, lt_min hrN hrI, fun x hx hxe hxd => ?_⟩
    refine hI x ?_ ?_
    · rw [mem_ball, hjs]; exact lt_of_lt_of_le hxd (min_le_right _ _)
    · rw [hWf, hWb]; exact hN x hx hxe (lt_of_lt_of_le hxd (min_le_left _ _))
  obtain ⟨rS, hrS, hS⟩ := hsecI
  -- points of the chord have the height of the end
  have hey := hemem.1
  have hxy : ∀ x ∈ hseg y a b, x.2 = e.2 := fun x hx => by rw [hey]; exact hx.1
  -- an interior point near the end, for the top cases
  have htopc : e ≠ C.top := by
    intro het
    obtain ⟨x, hx, hxe, hxd⟩ := hnearc rN hrN
    have h1 := int_lt_top hQ T (hN x hx hxe hxd)
    rw [hxy x hx, het] at h1
    exact lt_irrefl _ h1
  rcases (show j < C.m ∨ j = C.m by omega) with hjm | rfl
  · by_cases hj0 : j = 0 ∧ s = 0
    · -- the first vertex of the run
      obtain ⟨rfl, rfl⟩ := hj0
      have hev : e = (interiorWalk Q).vtx 0 := by rw [← hjs, Chazelle.Chain.sidePt_zero]
      obtain ⟨hi1, hprev⟩ := uturn_zero hQ T hD hli (by rw [← hev]; exact htopc)
      have hv0 : W.vtx (c0 C li) = (interiorWalk Q).vtx 0 := by
        have := vtx_c0 hQ T hD hli (j := 0) (by omega); rwa [zero_add] at this
      have hv1 : W.vtx (c0 C li + 1) = (interiorWalk Q).vtx 1 := by
        have := vtx_c0 hQ T hD hli (j := 1) hm1; rwa [add_comm] at this
      have hc0 : 7 ≤ c0 C li := by unfold c0; omega
      have hpt : sidePt W (c0 C li) 0 = e := by rw [Chazelle.Chain.sidePt_zero, hv0, hev]
      have hpos := pos_eq_of_sector hMC hc hA (p' := c0 C li) (t' := 0) (by
          show c0 C li < W.n; rw [hWn]; unfold c0; omega) le_rfl one_pos hpt
        ⟨1, one_pos, fun x hx hxe _ => sideLeft_uturn (W := W) (a := (interiorWalk Q).vtx 1)
          (by rw [hWn, show c0 C li + (2 * C.m + 7) - 1 = (c0 C li - 1) + (2 * C.m + 7) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold c0; omega)]; exact hprev)
          (by rw [hWn, Nat.mod_eq_of_lt (by unfold c0; omega)]; exact hv1)
          (by rw [hv0]; exact iw_snd_ne hQ T hD hli (by omega) (by omega) (by omega))
          (by rw [hv0, ← hev]; exact hxy x hx) (by rw [hv0, ← hev]; exact hxe)⟩ hnearc
      obtain ⟨hp', -⟩ := hpos
      refine ⟨by omega, by omega, fun h => ?_⟩
      omega
    · -- inside the run
      have hsj : s = 0 → 1 ≤ j := fun h0 => by
        by_contra h1; exact hj0 ⟨by omega, h0⟩
      have hpt : sidePt W (j + c0 C li) s = e := by rw [H.pt_eq T hjm s, hjs]
      have hpos := pos_eq_of_sector hMC hc hA (p' := j + c0 C li) (t' := s) (by
          show j + c0 C li < W.n; rw [hWn]; unfold c0; omega) hs0 hs1 hpt
        ⟨rS, hrS, fun x hx hxe hxd =>
          (H.sec_eq T hQ hjm hs0 hs1 hsj x).2 (hS x hx hxe hxd)⟩ hnearc
      obtain ⟨hp', -⟩ := hpos
      refine ⟨by omega, by omega, fun h => ?_⟩
      omega
  · rcases hs0.lt_or_eq with hs | hs
    · -- the open last edge: impossible
      exfalso
      apply heD
      have hlast : sidePt (interiorWalk Q) C.m s = lerp (Q.vtx C.m) (Q.vtx 0) s ∨
          sidePt (interiorWalk Q) C.m s = lerp (Q.vtx 0) (Q.vtx C.m) s := by
        unfold sidePt
        rw [hIn, show (C.m + 1) % Q.n = 0 by rw [hmn, Nat.mod_self],
          iw_vtx_idx hli (by omega), iw_vtx_idx hli (by omega)]
        unfold idxI
        by_cases h : li = true
        · left; rw [ite_eq_left h, ite_eq_left h]
        · right; rw [ite_eq_right h, ite_eq_right h, show Q.n - 1 - C.m = 0 by omega,
            show Q.n - 1 - 0 = C.m by omega]
      rw [← hjs]
      rcases hlast with h | h
      · rw [h]; exact openLast_mem_dom hQ T hD ⟨hs, hs1⟩
      · rw [h, show lerp (Q.vtx 0) (Q.vtx C.m) s = lerp (Q.vtx C.m) (Q.vtx 0) (1 - s) by
          apply Prod.ext <;> simp [Chazelle.Geometry.lerp] <;> ring]
        exact openLast_mem_dom hQ T hD ⟨by linarith, by linarith⟩
    · -- the last vertex of the run
      subst hs
      have hev : e = (interiorWalk Q).vtx C.m := by rw [← hjs, Chazelle.Chain.sidePt_zero]
      obtain ⟨hi1, hnext⟩ := uturn_last hQ T hD hli (by rw [← hev]; exact htopc)
      have hvm : W.vtx (c0 C li + C.m) = (interiorWalk Q).vtx C.m := by
        have := vtx_c0 hQ T hD hli (j := C.m) le_rfl; rwa [add_comm] at this
      have hvm1 : W.vtx (c0 C li + C.m - 1) = (interiorWalk Q).vtx (C.m - 1) := by
        have := vtx_c0 hQ T hD hli (j := C.m - 1) (by omega)
        rwa [show C.m - 1 + c0 C li = c0 C li + C.m - 1 by omega] at this
      have hpt : sidePt W (c0 C li + C.m) 0 = e := by rw [Chazelle.Chain.sidePt_zero, hvm, hev]
      have hpos := pos_eq_of_sector hMC hc hA (p' := c0 C li + C.m) (t' := 0) (by
          show c0 C li + C.m < W.n; rw [hWn]; unfold c0; omega) le_rfl one_pos hpt
        ⟨1, one_pos, fun x hx hxe _ => sideLeft_uturn (W := W) (a := (interiorWalk Q).vtx (C.m - 1))
          (by rw [hWn, show c0 C li + C.m + (2 * C.m + 7) - 1 =
              (c0 C li + C.m - 1) + (2 * C.m + 7) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold c0; omega)]; exact hvm1)
          (by rw [hWn, Nat.mod_eq_of_lt (by unfold c0; omega)]; exact hnext)
          (by rw [hvm]; exact iw_snd_ne hQ T hD hli (by omega) (by omega) (by omega))
          (by rw [hvm, ← hev]; exact hxy x hx) (by rw [hvm, ← hev]; exact hxe)⟩ hnearc
      obtain ⟨hp', ht'⟩ := hpos
      exact ⟨by omega, by omega, fun _ => ht'.symm⟩

end

end DrvT

end Chazelle.Core
