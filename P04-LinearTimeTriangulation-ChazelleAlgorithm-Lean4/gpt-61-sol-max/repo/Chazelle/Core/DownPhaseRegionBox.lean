module

public import Chazelle.Core.DownPhaseRegionBelow
public import Chazelle.Core.FactsChain

/-!
# WP-M (X, part 9): a region lies in the box of its host points

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, a horizontal ray
from a point of `R` at a non-vertex height, going right or left, leaves `R` at a point of a piece
of an arc of `R`.  That point is a convex combination of two host points (`ray_hit`).  Hence
every point of `R` lies within any bound of the coordinates of its host points (`region_abs_le`).
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt freeIn regionsIn)
open Chazelle.Geometry (lerp)
open ArcT (wrapK)
open Chazelle.Jordan (coordBound filled_subset_square isClosed_filled
  exists_openEdge_of_mem_boundary)

/-- **The first exit along a horizontal ray** to the right (`σ = 1`) or to the left (`σ = -1`)
from a point of a bounded open set. -/
theorem exists_first_exit_dir {D : Set Point} (hD : IsOpen D) {z : Point} (hz : z ∈ D) {B : ℝ}
    (hB : ∀ x ∈ D, |x.1| < B) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + σ * s', z.2) : Point) ∈ D) ∧
      ((z.1 + σ * s, z.2) : Point) ∉ D := by
  rcases hσ with rfl | rfl
  · obtain ⟨s, hs, h1, h2⟩ := exists_first_exit hD hz (R := B) (fun x hx => (abs_lt.1 (hB x hx)).2)
    grind
  · set f : Point → Point := fun p => (-p.1, p.2)
    have hf : Continuous f := by fun_prop
    set D' := f ⁻¹' D
    have hD' : IsOpen D' := hD.preimage hf
    have hz' : ((-z.1, z.2) : Point) ∈ D' := by grind
    obtain ⟨s, hs, h1, h2⟩ := exists_first_exit hD' hz' (R := B) (fun x hx => by
      grind)
    grind

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
/-- **A horizontal ray leaves the region on an arc piece.** -/
theorem ray_hit {z : Point} (hzR : z ∈ R)
    (hvQ : ∀ i, i < Q.n → z.2 ≠ (Q.vtx i).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ s > (0 : ℝ), ∃ i i' : ℕ, i < nk (interiorModel Q) S R ∧ i' < nk (interiorModel Q) S R ∧
      i' = (i + 1) % nk (interiorModel Q) S R ∧
      ∃ lam ∈ Icc (0 : ℝ) 1, ((z.1 + σ * s, z.2) : Point) =
        lerp (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i))
          (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i')) lam ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball ((z.1 + σ * s, z.2) : Point) r, x ∈ (interiorModel Q).D →
        x ∈ R := by
  set M := interiorModel Q with hMdef
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have hzfree := Chazelle.Chain.regionsIn_subset hR hzR
  have hDo : IsOpen M.D := hM.isOpen
  -- the chords are at vertex heights
  have hch : ∀ c ∈ S, ∀ w ∈ c, w.2 ≠ z.2 := by
    intro c hc w hw e
    obtain ⟨h, hh, a, b, rfl⟩ := hFam.2.2 c hc
    exact hvQ h hh (e.symm.trans hw.1)
  -- the exit point
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit_dir hDo hzfree.1 (B := coordBound Q + 1)
    (fun x hx => by
      have := (filled_subset_square Q hx.1).1; linarith) hσ
  set q : Point := (z.1 + σ * s, z.2) with hqdef
  have hσ2 : σ * σ = 1 := by grind
  have hqf : q ∈ Q.filled := by
    by_contra hnf
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_filled Q).isOpen_compl _ hnf
    set ε := min r s / 2 with hε
    have hε0 : 0 < ε := by grind
    have hεr : ε < r := by grind
    have hεs : ε < s := by grind
    apply hball (show ((z.1 + σ * (s - ε), z.2) : Point) ∈ ball q r by
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hqdef, sub_self, abs_zero]
      rw [show z.1 + σ * (s - ε) - (z.1 + σ * s) = -(σ * ε) by ring, abs_neg, abs_mul]
      have : |σ| = 1 := by grind
      rw [this, one_mul, abs_of_pos hε0]
      grind)
    exact (hseg (s - ε) ⟨by linarith, by linarith⟩).1
  have hqb : q ∈ M.W.boundary := by
    show q ∈ (interiorWalk Q).boundary
    rw [hWb]; by_contra hb; exact hq ⟨hqf, hb⟩
  have hWn : M.W.n = Q.n := by
    show (interiorWalk Q).n = Q.n
    unfold interiorWalk; split_ifs
    · rfl
    · exact FactsInterior.rev_n Q
  have hqv : ∀ j, j < M.W.n → q ≠ M.W.vtx j := by
    intro j hj h
    have hj' : j < Q.n := hWn ▸ hj
    obtain ⟨k, hk, hkv⟩ : ∃ k, k < Q.n ∧ M.W.vtx j = Q.vtx k := by
      show ∃ k, k < Q.n ∧ (interiorWalk Q).vtx j = Q.vtx k
      unfold interiorWalk
      split_ifs
      · grind
      · exact ⟨Q.n - 1 - j, by omega, FactsInterior.rev_vtx Q j hj'⟩
    grind
  obtain ⟨p, hp, t, ht, hqe⟩ := exists_openEdge_of_mem_boundary M.W hqb hqv
  have hpt : sidePt M.W p t = q := hqe.symm
  -- the segment lies in `R`
  have hsegR : ∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + σ * s', z.2) : Point) ∈ R := by
    have hT : IsPreconnected ((fun s' : ℝ => ((z.1 + σ * s', z.2) : Point)) '' Ico 0 s) :=
      isPreconnected_Ico.image _ (by fun_prop)
    have hTfree : (fun s' : ℝ => ((z.1 + σ * s', z.2) : Point)) '' Ico 0 s ⊆ freeIn M.D S := by
      rintro _ ⟨s', hs', rfl⟩
      exact ⟨hseg s' hs', fun ⟨c, hc, hmem⟩ => hch c hc _ hmem rfl⟩
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR hT hTfree
      ⟨z, ⟨0, ⟨le_rfl, hs⟩, by simp⟩, hzR⟩
    exact fun s' hs' => hsub ⟨s', hs', rfl⟩
  -- not a cut
  have hncut : ¬ M.IsCut S (p + t) := by
    rintro ⟨c, hc, q', u, hA, e⟩
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA.2.1 hA.2.2.1 ht.1.le ht.2 e.symm
    exact hch c hc _ hA.2.2.2.1 (by rw [hpt])
  obtain ⟨X, hX, a, b, harc, hin⟩ := hM.arc_around hF hfin hne hncut
  have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t + s * (1 - t)) X := by
    have h1 := (Loc.tendsto_mul_const_nhdsGT (show 0 < 1 - t by grind)).eventually
      (cyc_open hin)
    filter_upwards [h1, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s h1 hs1
    have hs0 : 0 < s := hs1.1
    refine harc.2.2.2.2.2.2 p _ hp (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2, hs1.2]) ?_
    grind
  obtain ⟨r0, hr0, hnear0⟩ := Loc.near_sub_region hQ hF hfin hp ht.1.le ht.2 hncut hX hfX
  have hXR : X = R := by
    set ε := min s r0 / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hεs : ε < s := by rw [hε]; have := min_le_left s r0; linarith
    have hεr : ε < r0 := by rw [hε]; have := min_le_right s r0; linarith
    have hmem := hsegR (s - ε) ⟨by linarith, by linarith⟩
    have hdist : ((z.1 + σ * (s - ε), z.2) : Point) ∈ ball (sidePt M.W p t) r0 := by
      rw [hpt, mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hqdef, sub_self, abs_zero]
      rw [show z.1 + σ * (s - ε) - (z.1 + σ * s) = -(σ * ε) by ring, abs_neg, abs_mul]
      have : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [this, one_mul, abs_of_pos hε0]
      exact max_lt hεr hr0
    have hX' := hnear0 _ hdist (Chazelle.Chain.regionsIn_subset hR hmem).1
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
    · exact h
    · exact absurd (h.le_bot ⟨hX', hmem⟩) (fun h => h)
  subst hXR
  -- the arc piece
  obtain ⟨i_l, d, hA⟩ := arc_keys hM hF hfin hne hX harc
  set N := nk M S X
  set n : ℝ := (M.W.n : ℝ)
  have hb : ∀ i, i < N → 0 ≤ hk M S X i ∧ hk M S X i < n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
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
  
  have hxd : xx < ukey M S X i_l d := by rw [hA.hud]; exact hxu.2
  have hd0 := hA.hd0
  have hdN := hA.hdN
  have hex : ∃ j, xx < ukey M S X i_l (j + 1) := ⟨d - 1, by
    grind⟩
  classical
  set j := Nat.find hex
  have hj1 : xx < ukey M S X i_l (j + 1) := Nat.find_spec hex
  have hjd : j < d := by
    by_contra h; push Not at h
    have := Nat.find_min' hex (show xx < ukey M S X i_l (d - 1 + 1) by
      grind)
    omega
  have hj0 : ukey M S X i_l j ≤ xx := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · grind
    · have := Nat.find_min hex (show j - 1 < j by omega)
      grind
  have hjj : ukey M S X i_l j < ukey M S X i_l (j + 1) :=
    ukey_mono hM hF hfin hA.hil (Nat.lt_succ_self j) (by omega)
  obtain ⟨q', -, -, -, hq'⟩ := arc_piece hM hF hfin hA hjd
  have hw : hostPt M.W (wrapK n xx) = q := by
    rw [wrapK_unwrapK hxb, hostPt_eq M.W ht.1.le ht.2, hpt]
  have e1 := hq' xx hj0 hj1.le
  have e2 := hq' _ le_rfl hjj.le
  have e3 := hq' _ hjj.le le_rfl
  rw [wrapK_ukey hM hF hfin hA.hil (by omega)] at e2 e3
  refine ⟨s, hs, (i_l + j) % N, (i_l + (j + 1)) % N, Nat.mod_lt _ (by omega),
    Nat.mod_lt _ (by omega), by grind,
    (xx - ukey M S X i_l j) / (ukey M S X i_l (j + 1) - ukey M S X i_l j),
    ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩, ?_,
    r0, hr0, fun x hx hxD => hnear0 x (by grind) hxD⟩
  rw [e2, e3, lerp_lerp]
  calc q = hostPt M.W (wrapK n xx) := hw.symm
    _ = _ := e1
    _ = _ := by
      have hne : ukey M S X i_l (j + 1) - ukey M S X i_l j ≠ 0 := sub_ne_zero.2 hjj.ne'
      grind

/-- **A region lies within the coordinate bound of its host points.** -/
theorem region_abs_le {B : ℝ}
    (hB : ∀ i, i < nk (interiorModel Q) S R →
      |(hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).1| ≤ B ∧
      |(hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).2| ≤ B) :
    ∀ z ∈ R, |z.1| < B + 1 ∧ |z.2| < B + 1 := by
  set M := interiorModel Q
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hsys := hM.sys S hFam.2.1 hFam.1
  intro z hzR
  have hRo : IsOpen R := hsys.regionsIn_open subset_rfl hR
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hRo z hzR
  set V : Finset ℝ := (Finset.range Q.n).image (fun i => (Q.vtx i).2)
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ∃ η ∈ Ioo (0 : ℝ) (min ρ 1),
      η ∉ (V.image (· - z.2) : Set ℝ) :=
    ((Set.Ioo_infinite (lt_min hρ one_pos)).sdiff (Finset.finite_toSet _)).nonempty
  have hηρ' : η < ρ := lt_of_lt_of_le hηρ (min_le_left _ _)
  have hη1 : η < 1 := lt_of_lt_of_le hηρ (min_le_right _ _)
  set z' : Point := (z.1, z.2 + η)
  have hz'R : z' ∈ R := hball (by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [z', Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη0]
    simp_all)
  have hvQ : ∀ i, i < Q.n → z'.2 ≠ (Q.vtx i).2 := by
    intro i hi e
    apply hηV
    rw [Finset.coe_image]
    exact ⟨(Q.vtx i).2, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩, by
      linarith⟩
  -- the coordinates of a convex combination of host points
  have hcomb : ∀ i i', i < nk M S R → i' < nk M S R → ∀ lam ∈ Icc (0 : ℝ) 1,
      |(lerp (hostPt M.W (hk M S R i)) (hostPt M.W (hk M S R i')) lam).1| ≤ B ∧
      |(lerp (hostPt M.W (hk M S R i)) (hostPt M.W (hk M S R i')) lam).2| ≤ B := by
    intro i i' hi hi' lam hlam
    obtain ⟨a1, a2⟩ := hB i hi
    obtain ⟨b1, b2⟩ := hB i' hi'
    have key : ∀ u v : ℝ, |u| ≤ B → |v| ≤ B → |u + lam * (v - u)| ≤ B := by
      intro u v hu hv
      rw [abs_le] at *
      constructor <;> nlinarith [hlam.1, hlam.2, hu.1, hu.2, hv.1, hv.2]
    exact ⟨key _ _ a1 b1, key _ _ a2 b2⟩
  obtain ⟨s, hs, i, i', hi, hi', -, lam, hlam, he, -⟩ :=
    ray_hit hQ hFam hne hR hz'R hvQ (Or.inl rfl)
  obtain ⟨s₂, hs₂, j, j', hj, hj', -, lam₂, hlam₂, he₂, -⟩ :=
    ray_hit hQ hFam hne hR hz'R hvQ (Or.inr rfl)
  have c1 := hcomb i i' hi hi' lam hlam
  have c2 := hcomb j j' hj hj' lam₂ hlam₂
  rw [← he] at c1
  rw [← he₂] at c2
  simp only [z'] at c1 c2
  simp only [abs_le] at c1 c2
  refine ⟨abs_lt.2 ⟨by linarith, by linarith⟩,
    abs_lt.2 ⟨by linarith, by linarith⟩⟩


end

end

end DownHost

end Chazelle.Core
