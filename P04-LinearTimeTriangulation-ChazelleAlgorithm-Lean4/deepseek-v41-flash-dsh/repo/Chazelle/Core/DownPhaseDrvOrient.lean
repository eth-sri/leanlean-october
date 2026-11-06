module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvKept
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.DownPhaseExtractMain
public import Chazelle.Core.DownPhaseExtractGeom

/-!
# Down-phase driver, X-R1 (part 2): the host polygon is counterclockwise

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, the host polygon
`H = hostPoly Q S R` (host points in increasing walk key order) has its interior on the left:
`orient H = 1` (`hostPoly_orient`), so the walk of the interior of `H` is `H` itself
(`interiorWalk_hostPoly`).

Proof: a horizontal ray from a point of `R` off the vertex heights leaves `R` on a host edge `i`
(`ray_hit`) that is an arc gap (a chord gap is at a vertex height), hence a piece of a walk edge
`p` of the interior walk of `Q`, traversed in the walk direction (`arcEdge_pair`); the offsets to
the left of walk edge `p` are interior to `Q` (`eventually_offset_orient`, `orient = 1`), near
the exit point they lie in `R ⊆ H.filled`, and they are offsets to the left of host edge `i`
(`ExtG.offset_lerp_pair`); `orient_eq_of_eventually` concludes.
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)
open DownHost

/-- **An arc edge lies on one walk edge, in the walk direction.** -/
theorem arcEdge_pair (W : Polygon) {a b : ℝ} (ha0 : 0 ≤ a) (han : a < W.n) (hb0 : 0 ≤ b)
    (hbn : b < W.n) (_hab : a ≠ b) (hnv : ∀ k : ℕ, k < W.n → ¬ sideInArc a b k) :
    ∃ p, p < W.n ∧ ∃ t'' : ℝ, a - p < t'' ∧ t'' ≤ 1 ∧ 0 ≤ a - p ∧
      hostPt W a = sidePt W p (a - p) ∧ hostPt W b = sidePt W p t'' := by
  set p := ⌊a⌋₊ with hpdef
  have hp : (p : ℝ) ≤ a := Nat.floor_le ha0
  have hp1 : a < p + 1 := Nat.lt_floor_add_one a
  have hpn : p < W.n := by
    have : (p : ℝ) < W.n := lt_of_le_of_lt hp han
    exact_mod_cast this
  have hA : hostPt W a = sidePt W p (a - p) := rfl
  refine ⟨p, hpn, ?_⟩
  by_cases hlt : a < b
  · have hbp : b ≤ p + 1 := by
      by_contra h
      push Not at h
      have hk : p + 1 < W.n := by
        have : ((p + 1 : ℕ) : ℝ) < W.n := by push_cast; linarith
        exact_mod_cast this
      apply hnv (p + 1) hk
      unfold sideInArc; rw [ite_eq_left hlt]; push_cast; exact ⟨hp1, h⟩
    refine ⟨b - p, by linarith, by linarith, by linarith, hA, ?_⟩
    rcases hbp.lt_or_eq with hbp | hbp
    · have := hostPt_eq W (p := p) (t := b - p) (by linarith) (by linarith)
      rwa [show (p : ℝ) + (b - p) = b by ring] at this
    · have hk : p + 1 < W.n := by
        have : ((p + 1 : ℕ) : ℝ) < W.n := by push_cast; linarith
        exact_mod_cast this
      have e : b = ((p + 1 : ℕ) : ℝ) + 0 := by push_cast; linarith
      rw [e, hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
        show ((p + 1 : ℕ) : ℝ) + 0 - p = 1 by push_cast; ring, sidePt_one,
        Nat.mod_eq_of_lt hk]
  · have hb0' : b = 0 := by
      by_contra h
      have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm h)
      apply hnv 0 (by omega)
      unfold sideInArc; rw [ite_eq_right hlt]; right; simpa using hbpos
    have hpn1 : p + 1 = W.n := by
      by_contra h
      have hk : p + 1 < W.n := by omega
      apply hnv (p + 1) hk
      unfold sideInArc; rw [ite_eq_right hlt]; left; push_cast; exact hp1
    refine ⟨1, by linarith, le_rfl, by linarith, hA, ?_⟩
    rw [hb0', show (0 : ℝ) = ((0 : ℕ) : ℝ) + 0 by simp, hostPt_eq W le_rfl one_pos,
      Chazelle.Chain.sidePt_zero, sidePt_one, hpn1, Nat.mod_self]

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The host polygon is counterclockwise.** -/
theorem hostPoly_orient (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    Mountain.orient (hostPoly Q S R) = 1 := by
  set M := interiorModel Q with hMdef
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hsys := hM.sys S hF hfin
  have hRo : IsOpen R := hsys.regionsIn_open subset_rfl hR
  have hH : (hostPoly Q S R).Simple := hostPts_simple hQ hFam hne hR
  have X : Extract.Ctx Q S R := ⟨hQ, hFam, hne, hR⟩
  have h3 := X.three
  have hN2 : 2 ≤ nk M S R := le_trans (⊛) h3
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  obtain ⟨z, hzR, hzV⟩ := exists_mem_off_heights hRo (Chazelle.Chain.regionsIn_nonempty hR)
    ((Finset.range Q.n).image (fun i => (Q.vtx i).2))
  have hvQ : ∀ i, i < Q.n → z.2 ≠ (Q.vtx i).2 := fun i hi e =>
    hzV (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e.symm⟩)
  obtain ⟨s, -, i, i', hi, hi', rfl, lam, hlam, he, r, hr, hnear⟩ :=
    ray_hit hQ hFam hne hR hzR hvQ (Or.inl rfl)
  set P : Point := ((z.1 + 1 * s, z.2) : Point) with hPdef
  set A := hostPt M.W (hk M S R i) with hAdef
  set B := hostPt M.W (hk M S R ((i + 1) % nk M S R)) with hBdef
  -- the ends are at vertex heights, the exit point is not
  obtain ⟨ha, hha, hAy⟩ := Extract.host_height X hi
  obtain ⟨hb, hhb, hBy⟩ := Extract.host_height X hi'
  have hPy : P.2 = A.2 + lam * (B.2 - A.2) := by
    have := congrArg Prod.snd he; simpa [lerp] using this
  have hlam0 : lam ≠ 0 := by
    intro h0; rw [h0] at hPy
    exact hvQ ha hha (by rw [← hAy]; simpa [hPdef] using hPy)
  have hlam1 : lam ≠ 1 := by
    intro h1; rw [h1] at hPy
    exact hvQ hb hhb (by rw [← hBy]; simp [hPdef] at hPy ⊢; linarith)
  have hlam' : lam ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hlam.1 (Ne.symm hlam0), lt_of_le_of_ne hlam.2 hlam1⟩
  -- the gap is an arc gap
  have hsi : (i + 1) % nk M S R < nk M S R := Nat.mod_lt _ (⋄)
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
      hB, hka, hkb, -⟩
  swap
  · exfalso
    obtain ⟨h, hh, x₁, x₂, rfl⟩ := hFam.2.2 c hc
    have hA' : A = sidePt M.W p t := Ρ hAdef, hka, hostPt_eq M.W hA.2.1 hA.2.2.1
    have hB' : B = sidePt M.W p' t' := Ρ hBdef, hkb, hostPt_eq M.W hB.2.1 hB.2.2.1
    have e1 : A.2 = (Q.vtx h).2 := by rw [hA']; exact hA.2.2.2.1.1
    have e2 : B.2 = (Q.vtx h).2 := by rw [hB']; exact hB.2.2.2.1.1
    rw [e1, e2, sub_self, mul_zero, add_zero] at hPy
    exact hvQ h hh hPy
  have hb1 := hostKeys_bounds (hk_mem hM hF hfin hi)
  have hb2 := hostKeys_bounds (hk_mem hM hF hfin hsi)
  have hnv : ∀ k : ℕ, k < M.W.n →
      ¬ sideInArc (hk M S R i) (hk M S R ((i + 1) % nk M S R)) k := by
    intro k hk hkin
    exact hk_gap hM hF hfin hN2 hi
      (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k (Nat.cast_nonneg k) (by exact_mod_cast hk) hkin⟩)
      hkin
  obtain ⟨p, hp, t'', ht1, ht2, ht0, hAe, hBe⟩ := arcEdge_pair M.W hb1.1 hb1.2 hb2.1 hb2.2
    (hk_succ_ne hM hF hfin hN2 hi) hnv
  set τ₀ := hk M S R i - p with hτ₀
  -- the host edge as a piece of the walk edge
  have hHn : (hostPoly Q S R).n = nk M S R := hostPoly_n
  have hvi : (hostPoly Q S R).vtx i = A := hostPoly_vtx hi
  have hvi' : (hostPoly Q S R).vtx ((i + 1) % (hostPoly Q S R).n) = B := by
    rw [hHn]; exact hostPoly_vtx hsi
  have hiH : i < (hostPoly Q S R).n := by rw [hHn]; exact hi
  have hcpos : 0 < t'' - τ₀ := ⟡
  set t' := τ₀ + lam * (t'' - τ₀) with ht'
  have ht'I : t' ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have : 0 < lam * (t'' - τ₀) := mul_pos hlam'.1 hcpos; linarith
    · have : lam * (t'' - τ₀) < 1 * (t'' - τ₀) := mul_lt_mul_of_pos_right hlam'.2 hcpos
      linarith
  have hWn : (interiorWalk Q).n = M.W.n := rfl
  have hpW := hp
  have hoff : ∀ δ : ℝ, Chazelle.Jordan.offset ((hostPoly Q S R).vtx i)
      ((hostPoly Q S R).vtx ((i + 1) % (hostPoly Q S R).n)) lam δ =
      Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
        ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' (δ * (t'' - τ₀)) := by
    intro δ
    Ξ hvi, hvi', show A = sidePt M.W p τ₀ from hAe, show B = sidePt M.W p t'' from hBe
    exact ExtG.offset_lerp_pair _ _ _ _ _ _
  -- the exit point
  have hP' : Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
      ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' 0 = P := by
    Ξ ← zero_mul (t'' - τ₀), ← hoff 0, Chazelle.Jordan.offset_zero, hvi, hvi', he
  refine Mountain.orient_eq_of_eventually hH hiH hlam' (Or.inl rfl) ?_
  have hev := Mountain.eventually_offset_orient hWs hpW ht'I
  rw [hWo] at hev
  have hev' := (Loc.tendsto_mul_const_nhdsGT hcpos).eventually hev
  have hnearev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
      ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' (1 * (δ * (t'' - τ₀))) ∈
        ball P r := by
    have hcont : Continuous fun δ : ℝ => Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
        ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' (1 * (δ * (t'' - τ₀))) :=
      (Chazelle.Jordan.continuous_offset _ _ _).comp (by fun_prop)
    have h0 : Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
        ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' (1 * (0 * (t'' - τ₀))) = P := by
      simp only [zero_mul, mul_zero]; exact hP'
    have := hcont.tendsto 0
    rw [h0] at this
    exact (this.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hev', hnearev] with δ hδ hball
  Ξ one_mul, hoff
  have hD : Chazelle.Jordan.offset ((interiorWalk Q).vtx p)
      ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n)) t' (δ * (t'' - τ₀)) ∈ M.D := by
    have h1 := hδ.1
    rw [one_mul, hWf, hWb] at h1
    exact h1
  rw [one_mul] at hball
  exact (region_sub_intHost hQ hFam hne hR (hnear _ hball hD)).1

/-- **The walk of the interior of the host polygon is the host polygon.** -/
theorem interiorWalk_hostPoly (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    interiorWalk (hostPoly Q S R) = hostPoly Q S R := by
  have h := hostPoly_orient hQ hFam hne hR
  have hL : Mountain.LeftInside (hostPoly Q S R) := by
    by_contra hL
    unfold Mountain.orient at h
    rw [ite_eq_right hL] at h
    norm_num at h
  unfold interiorWalk
  Ξ ite_eq_left hL

end

end DownDrv

end Chazelle.Core
