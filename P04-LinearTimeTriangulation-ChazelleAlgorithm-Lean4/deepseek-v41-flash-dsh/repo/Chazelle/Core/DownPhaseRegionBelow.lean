module

public import Chazelle.Core.DownPhaseHostChain
public import Chazelle.Core.DownPhaseLocal

/-!
# WP-M (X, part 8): a region lies below its highest host point

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, every point of `R` is
at most as high as the highest walk point of a host key of `R` (`region_below`).

Proof: a point `z` of `R` above that level is moved slightly up to a height that is no vertex
height.  The walk axiom `reach` then gives a horizontal segment from it to a walk position `x`.
The segment avoids all chords (they are at vertex heights), so it lies in `R`.  So `x` is not a
cut and lies inside an arc of `R` (`Loc.near_sub_region`).  Its walk point lies on a piece of that
arc between two consecutive host keys (`arc_piece`), so it is at most as high as one of their
walk points, a contradiction.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt freeIn regionsIn)
open Chazelle.Visibility (hseg)
open ArcT (wrapK)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **A region lies below its highest host point.** -/
theorem region_below (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {Y : ℝ}
    (hY : ∀ i, i < nk (interiorModel Q) S R →
      (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).2 ≤ Y) :
    ∀ z ∈ R, z.2 ≤ Y := by
  set M := interiorModel Q with hMdef
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hsys := hM.sys S hF hfin
  intro z hzR
  by_contra hzY
  push Not at hzY
  -- a small ball in `R`
  have hRo : IsOpen R := hsys.regionsIn_open subset_rfl hR
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hRo z hzR
  -- a height avoiding all vertex heights
  set V : Finset ℝ := (Finset.range Q.n).image (fun i => (Q.vtx i).2) ∪
    (Finset.range M.W.n).image (fun i => (M.W.vtx i).2)
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ∃ η ∈ Ioo (0 : ℝ) ρ, η ∉ (V.image (· - z.2) : Set ℝ) :=
    ((Set.Ioo_infinite hρ).sdiff (Finset.finite_toSet _)).nonempty
  have hVy : ∀ y ∈ V, z.2 + η ≠ y := by
    intro y hy e
    apply hηV
    rw [Finset.coe_image]
    exact ⟨y, hy, by simp only; linarith⟩
  set z' : Point := (z.1, z.2 + η)
  have hz'R : z' ∈ R := hball (by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [z', Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη0]
    exact max_lt hρ hηρ)
  have hz'free := Chazelle.Chain.regionsIn_subset hR hz'R
  have hz'Y : Y < z'.2 := by show Y < z.2 + η; linarith
  have hvW : ∀ i, i < M.W.n → z'.2 ≠ (M.W.vtx i).2 := fun i hi =>
    hVy _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hvQ : ∀ i, i < Q.n → z'.2 ≠ (Q.vtx i).2 := fun i hi =>
    hVy _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  -- the chords are at vertex heights
  have hch : ∀ c ∈ S, ∀ w ∈ c, w.2 ≠ z'.2 := by
    intro c hc w hw e
    obtain ⟨h, hh, a, b, rfl⟩ := hFam.2.2 c hc
    exact hvQ h hh (e.symm.trans hw.1)
  -- the segment to the walk
  obtain ⟨s, hs, hseg, p, hp, t, ht, hpt, -⟩ := hM.reach z' hz'free.1 hvW
  have hsegR : ∀ s' ∈ Ico (0 : ℝ) s, ((z'.1 + s', z'.2) : Point) ∈ R := by
    have hT : IsPreconnected ((fun s' : ℝ => ((z'.1 + s', z'.2) : Point)) '' Ico 0 s) :=
      isPreconnected_Ico.image _ (by fun_prop)
    have hTfree : (fun s' : ℝ => ((z'.1 + s', z'.2) : Point)) '' Ico 0 s ⊆ freeIn M.D S := by
      rintro _ ⟨s', hs', rfl⟩
      exact ⟨hseg s' hs', fun ⟨c, hc, hmem⟩ => hch c hc _ hmem rfl⟩
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR hT hTfree
      ⟨z', ⟨0, ⟨le_rfl, hs⟩, by simp [z']⟩, hz'R⟩
    exact fun s' hs' => hsub ⟨s', hs', rfl⟩
  -- the walk position is not a cut
  have hncut : ¬ M.IsCut S (p + t) := by
    rintro ⟨c, hc, q, u, hA, e⟩
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA.2.1 hA.2.2.1 ht.1.le ht.2 e.symm
    exact hch c hc _ hA.2.2.2.1 (by rw [hpt])
  obtain ⟨X, hX, a, b, harc, hin⟩ := hM.arc_around hF hfin hne hncut
  -- the region faced there is `R`
  have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t + s * (1 - t)) X := by
    have h1 := (Loc.tendsto_mul_const_nhdsGT (show 0 < 1 - t by linarith [ht.2])).eventually
      (cyc_open hin)
    filter_upwards [h1, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s h1 hs1
    have hs0 : 0 < s := hs1.1
    refine harc.2.2.2.2.2.2 p _ hp (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2, hs1.2]) ?_
    rw [← add_assoc]; exact h1
  obtain ⟨r0, hr0, hnear⟩ := Loc.near_sub_region hQ hF hfin hp ht.1.le ht.2 hncut hX hfX
  have hXR : X = R := by
    set s' := s - min s r0 / 2 with hs'd
    have hs'0 : 0 ≤ s' := by rw [hs'd]; have := min_le_left s r0; linarith
    have hs's : s' < s := by rw [hs'd]; have := lt_min hs hr0; linarith
    have hmem := hsegR s' ⟨hs'0, hs's⟩
    have hdist : ((z'.1 + s', z'.2) : Point) ∈ ball (sidePt M.W p t) r0 := by
      rw [hpt, Metric.mem_ball, Prod.dist_eq]
      simp only [Real.dist_eq, sub_self, abs_zero]
      rw [max_eq_left (abs_nonneg _)]
      rw [show z'.1 + s' - (z'.1 + s) = -(min s r0 / 2) by rw [hs'd]; ring, abs_neg,
        abs_of_pos (by have := lt_min hs hr0; linarith)]
      have := min_le_right s r0; have := lt_min hs hr0; linarith
    have hX' := hnear _ hdist (Chazelle.Chain.regionsIn_subset hR hmem).1
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
    · exact h
    · exact absurd (h.le_bot ⟨hX', hmem⟩) (fun h => h)
  subst hXR
  -- the walk point lies on a piece of the arc
  obtain ⟨i_l, d, hA⟩ := arc_keys hM hF hfin hne hX harc
  set N := nk M S X
  set n : ℝ := (M.W.n : ℝ)
  have hb : ∀ i, i < N → 0 ≤ hk M S X i ∧ hk M S X i < n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  have hab := (WalkAx.arc_cuts hne harc).2.2
  have hlb : 0 ≤ a ∧ a < n := hA.hl ▸ hb _ hA.hil
  have hrb : 0 ≤ b ∧ b < n := hA.hr ▸ hb _ (Nat.mod_lt _ (by have := hA.hdN; omega))
  have hxb : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n := by
    refine ⟨add_nonneg (Nat.cast_nonneg p) ht.1.le, ?_⟩
    have : ((p + 1 : ℕ) : ℝ) ≤ (M.W.n : ℝ) := by exact_mod_cast hp
    push_cast at this
    linarith [ht.2]
  have hu0 : ukey M S X i_l 0 = a := by rw [ukey_zero hA.hil, hA.hl]
  have hab' : unwrapK n a a < unwrapK n a b := by
    rw [unwrapK_self, ← hA.hud, ← hu0]
    exact ukey_mono hM hF hfin hA.hil hA.hd0 hA.hdN
  have hxu := (cyc_unwrap hlb hlb hrb hxb hab').1 hin
  rw [unwrapK_self] at hxu
  set xx := unwrapK n a ((p : ℝ) + t) with hxx
  have hxa : ukey M S X i_l 0 < xx := by rw [hu0]; exact hxu.1
  have hxd : xx < ukey M S X i_l d := by rw [hA.hud]; exact hxu.2
  have hd0 := hA.hd0
  -- the piece containing `xx`
  have hex : ∃ j, xx < ukey M S X i_l (j + 1) := ⟨d - 1, by
    rw [Nat.sub_add_cancel hA.hd0]; exact hxd⟩
  classical
  set j := Nat.find hex
  have hj1 : xx < ukey M S X i_l (j + 1) := Nat.find_spec hex
  have hjd : j < d := by
    by_contra h; push Not at h
    have := Nat.find_min' hex (show xx < ukey M S X i_l (d - 1 + 1) by
      rw [Nat.sub_add_cancel hA.hd0]; exact hxd)
    omega
  have hj0 : ukey M S X i_l j ≤ xx := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; exact hxa.le
    · have := Nat.find_min hex (show j - 1 < j by omega)
      push Not at this
      rwa [Nat.sub_add_cancel h0] at this
  obtain ⟨q, -, -, -, hq⟩ := arc_piece hM hF hfin hA hjd
  have hw : hostPt M.W (wrapK n xx) = sidePt M.W p t := by
    rw [wrapK_unwrapK hxb, hostPt_eq M.W ht.1.le ht.2]
  have e1 := hq xx hj0 hj1.le
  have e2 := hq _ le_rfl (ukey_mono hM hF hfin hA.hil (Nat.lt_succ_self j) (by
    have := hA.hdN; omega)).le
  have e3 := hq _ (ukey_mono hM hF hfin hA.hil (Nat.lt_succ_self j) (by
    have := hA.hdN; omega)).le le_rfl
  rw [wrapK_ukey hM hF hfin hA.hil (by have := hA.hdN; omega)] at e2
  rw [wrapK_ukey hM hF hfin hA.hil (by have := hA.hdN; omega)] at e3
  have hY1 := hY _ (Nat.mod_lt (i_l + j) (show 0 < N by have := hA.hdN; omega))
  have hY2 := hY _ (Nat.mod_lt (i_l + (j + 1)) (show 0 < N by have := hA.hdN; omega))
  rw [e2] at hY1
  rw [e3] at hY2
  rw [hw, hpt] at e1
  have hy : z'.2 = (Chazelle.Geometry.lerp (M.W.vtx (q % M.W.n))
      (M.W.vtx ((q % M.W.n + 1) % M.W.n)) (xx - q)).2 := by rw [← e1]
  simp only [Chazelle.Geometry.lerp_snd] at hy hY1 hY2
  set u := (M.W.vtx (q % M.W.n)).2
  set v := (M.W.vtx ((q % M.W.n + 1) % M.W.n)).2
  have hj1' := hj1.le
  rcases le_total u v with huv | huv
  · have : (xx - q) * (v - u) ≤ (ukey M S X i_l (j + 1) - q) * (v - u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · have : (xx - q) * (v - u) ≤ (ukey M S X i_l j - q) * (v - u) :=
      mul_le_mul_of_nonpos_right (by linarith) (by linarith)
    linarith

end

end DownHost

end Chazelle.Core
