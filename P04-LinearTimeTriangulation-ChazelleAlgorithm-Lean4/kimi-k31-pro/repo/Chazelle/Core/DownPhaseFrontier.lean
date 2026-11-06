module

public import Chazelle.Core.DownPhaseExitEdge
public import Chazelle.Core.DownPhaseHostDom
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# WP-M (X, part 16): the frontier of a region, and the kept chords

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, with host polygon
`H = hostPoly Q S R` (simple, H1):
* every edge of `H` is an arc piece on the walk or a chord of `S` (`hostEdge_cases`), so
  `H.filled ⊆ Q.filled` (`hostFilled_sub`, Jordan) and the interior of `H` lies in the interior of
  `Q` (`intHost_sub`);
* `R` lies in the interior of `H` (`region_sub_intHost`): a horizontal ray from `R` exits at an arc
  piece, next to which the domain lies in `R`;
* **the frontier of `R` lies on `∂H`** (`frontier_sub_hostBd`): a frontier point inside `Q` lies
  on an exit chord, which is an edge of `H` (`exit_chordGap`).

For a chord gap `g` and the host chain `C = hostChain Q S R g`, a horizontal chord of `C.dom`
meeting `R` has its open part in `R` and its endpoints off the interior of `Q` (`kept_chord`):
its open part misses `∂H` (it misses the chain, and it cannot run along the gap chord), so it
stays in `R`; an endpoint inside `Q` would lie on a chord of `S` running along the open part.
Hence the kept chords are admissible in the interior model, and meet its domain only in `R`
(`kept_adm`).
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Metric
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn freeIn regionsIn IsHChordIn)
open Chazelle.Geometry (lerp lerp_mem_segment)
open Chazelle.Jordan (coordBound)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- The boundary of the host polygon is the union of the host edges. -/
theorem mem_hostPoly_boundary {z : Point} :
    z ∈ (hostPoly Q S R).boundary ↔ ∃ i, i < nk (interiorModel Q) S R ∧
      z ∈ Chazelle.segment (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i))
        (hostPt (interiorModel Q).W
          (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R))) := by
  have hn := hostPoly_n (Q := Q) (S := S) (R := R)
  constructor
  · rintro ⟨i, hi, hz⟩
    rw [hn] at hi
    unfold Polygon.edge at hz
    rw [hn, hostPoly_vtx hi, hostPoly_vtx (Nat.mod_lt _ (by omega))] at hz
    exact ⟨i, hi, hz⟩
  · rintro ⟨i, hi, hz⟩
    refine ⟨i, by rwx [hn], ?_⟩
    unfold Polygon.edge
    rw [hn, hostPoly_vtx hi, hostPoly_vtx (Nat.mod_lt _ (by omega))]
    exact hz

/-- **A host edge** consists of walk points and of points of chords of `S` in the domain. -/
theorem hostEdge_cases (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    {i : ℕ} (hi : i < nk (interiorModel Q) S R) {z : Point}
    (hz : z ∈ Chazelle.segment (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i))
      (hostPt (interiorModel Q).W
        (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)))) :
    (∃ p, p < (interiorModel Q).W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      z = sidePt (interiorModel Q).W p t) ∨ (z ∈ (interiorModel Q).D ∧ ∃ c ∈ S, z ∈ c) := by
  set M := interiorModel Q
  have hM  := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3  := three_le_nk hQ hFam hne hR
  have hN2 : 2 ≤ nk M S R := le_trans (by norm_num) h3
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
    hB, ha, hb, hAB⟩
  · left
    have hsi : (i + 1) % nk M S R < nk M S R := Nat.mod_lt _ (by omega)
    have hb1 := hostKeys_bounds (hk_mem hM hF hfin hi)
    have hb2 := hostKeys_bounds (hk_mem hM hF hfin hsi)
    have hnv : ∀ k : ℕ, k < M.W.n →
        ¬ sideInArc (hk M S R i) (hk M S R ((i + 1) % nk M S R)) k := by
      intro k hk hkin
      exact hk_gap hM hF hfin hN2 hi
        (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k (Nat.cast_nonneg k) (by exact_mod_cast hk) hkin⟩)
        hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      (hk_succ_ne hM hF hfin hN2 hi) hnv z hz
    exact ⟨q, hq, s, hs0, hs1, hzq⟩
  · have hPa : hostPt M.W (hk M S R i) = sidePt M.W p t := by
      rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
    have hPb : hostPt M.W (hk M S R ((i + 1) % nk M S R)) = sidePt M.W p' t' := by
      rw [hb, hostPt_eq M.W hB.2.1 hB.2.2.1]
    obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hA hB hAB
    rw [hPa, hPb] at hz
    obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hz
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · right
        exact ⟨hopen s ⟨h0, h1⟩, c, hc, by rw [hcab]; exact lerp_mem_segment _ _ hs0 hs1⟩
      · left
        subst h1
        rw [Chazelle.Geometry.lerp_one]
        exact ⟨p', hB.1, t', hB.2.1, hB.2.2.1, rfl⟩
    · left
      subst h0
      rw [Chazelle.Geometry.lerp_zero]
      exact ⟨p, hA.1, t, hA.2.1, hA.2.2.1, rfl⟩

/-- The boundary of the host polygon lies in the filled polygon `Q`. -/
theorem hostBd_sub_filled (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).boundary ⊆ Q.filled := by
  intro z hz
  obtain ⟨i, hi, hz⟩ := mem_hostPoly_boundary.1 hz
  obtain ⟨-, hWb, -, -⟩ := FactsInterior.interiorWalk_spec hQ
  rcases hostEdge_cases hQ hFam hne hR hi hz with ⟨p, hp, t, ht0, ht1, rfl⟩ | ⟨hzD, -⟩
  · apply Chazelle.Jordan.boundary_subset_filled
    rw [← hWb]
    exact sidePt_mem_boundary hp ht0 ht1.le
  · exact hzD.1

/-- **The filled host polygon lies in the filled polygon `Q`** (Jordan: the exterior of `Q` is
connected, misses `∂H` and contains far points). -/
theorem hostFilled_sub (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).filled ⊆ Q.filled := by
  intro x hx
  by_contra hxQ
  have hH  := hostPts_simple hQ hFam hne hR
  set w : Point := (max (coordBound (hostPoly Q S R)) (coordBound Q) + 1, 0) with hw
  have hwQ : w ∉ Q.filled := Chazelle.Jordan.far_not_mem_filled Q (Or.inl (by
    linarith [le_max_right (coordBound (hostPoly Q S R)) (coordBound Q)]))
  have hwH : w ∉ (hostPoly Q S R).filled :=
    Chazelle.Jordan.far_not_mem_filled (hostPoly Q S R) (Or.inl (by
      linarith [le_max_left (coordBound (hostPoly Q S R)) (coordBound Q)]))
  have hsub : Q.filledᶜ ⊆ (hostPoly Q S R).boundaryᶜ := fun y hy hyb =>
    hy (hostBd_sub_filled hQ hFam hne hR hyb)
  exact FactsInterior.subset_exterior hH (Chazelle.Jordan.filled_compl_connected hQ) hsub hwQ hwH
    hxQ hx

/-- **The interior of the host polygon lies in the interior of `Q`.** -/
theorem intHost_sub (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).filled \ (hostPoly Q S R).boundary ⊆ Q.filled \ Q.boundary := by
  have hH : (hostPoly Q S R).Simple := hostPts_simple hQ hFam hne hR
  rw [← Chazelle.Jordan.interior_filled hH, ← Chazelle.Jordan.interior_filled hQ]
  exact interior_mono (hostFilled_sub hQ hFam hne hR)

/-- An open nonempty set has a point off finitely many heights. -/
theorem exists_mem_off_heights {U : Set Point} (hU : IsOpen U) (hne : U.Nonempty)
    (V : Finset ℝ) : ∃ z ∈ U, z.2 ∉ V := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ∃ η ∈ Ioo (0 : ℝ) ρ, η ∉ (V.image (· - z.2) : Set ℝ) :=
    ((Set.Ioo_infinite hρ).sdiff (Finset.finite_toSet _)).nonempty
  refine ⟨(z.1, z.2 + η), hball ?_, fun h => hηV ?_⟩
  · rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη0]
    exact max_lt hρ hηρ
  · rw [Finset.coe_image]
    exact ⟨z.2 + η, h, by simp⟩

/-- **The region lies in the interior of its host polygon.** -/
theorem region_sub_intHost (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ (hostPoly Q S R).filled \ (hostPoly Q S R).boundary := by
  set M := interiorModel Q
  have hM  := walkAx_interiorModel hQ
  have hsys := hM.sys S hFam.2.1 hFam.1
  have hRo  := hsys.regionsIn_open subset_rfl hR
  have hH  := hostPts_simple hQ hFam hne hR
  have hRb : R ⊆ (hostPoly Q S R).boundaryᶜ := fun z hz hzb => by
    obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hzb
    exact hostEdge_not_mem hQ hFam hne hR hi hzi hz
  obtain ⟨z, hzR, hzV⟩ := exists_mem_off_heights hRo (Chazelle.Chain.regionsIn_nonempty hR)
    ((Finset.range Q.n).image (fun i => (Q.vtx i).2))
  have hvQ : ∀ i, i < Q.n → z.2 ≠ (Q.vtx i).2 := fun i hi e =>
    hzV (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e.symm⟩)
  obtain ⟨s, -, i, i', hi, -, rfl, lam, hlam, he, r, hr, hnear⟩ :=
    ray_hit hQ hFam hne hR hzR hvQ (Or.inl rfl)
  have hqb : ((z.1 + 1 * s, z.2) : Point) ∈ (hostPoly Q S R).boundary :=
    mem_hostPoly_boundary.2 ⟨i, hi, by rw [he]; exact lerp_mem_segment _ _ hlam.1 hlam.2⟩
  obtain ⟨u, hu, hdu⟩ := Metric.mem_closure_iff.1
    (Chazelle.Jordan.boundary_subset_closure_interior hH hqb) r hr
  have huD  := intHost_sub hQ hFam hne hR hu
  have huR : u ∈ R := hnear u (by rwx [mem_ball, dist_comm]) huD
  exact FactsInterior.subset_interior hH (Chazelle.Chain.regionsIn_isPreconnected hR) hRb huR hu.1

/-- **The frontier of the region lies on the boundary of its host polygon.** -/
theorem frontier_sub_hostBd (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {w : Point}
    (hw : w ∈ closure R) (hwR : w ∉ R) : w ∈ (hostPoly Q S R).boundary := by
  set M := interiorModel Q
  have hM  := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hsys := hM.sys S hF hfin
  by_contra hwb
  have hwf : w ∈ (hostPoly Q S R).filled :=
    closure_minimal (fun x hx => (region_sub_intHost hQ hFam hne hR hx).1)
      (Chazelle.Jordan.isClosed_filled _) hw
  have hwD  := intHost_sub hQ hFam hne hR ⟨hwf, hwb⟩
  by_cases hwc : ∃ c ∈ S, w ∈ c
  · obtain ⟨c, hc, hwc⟩ := hwc
    have h2 : 2 ≤ nk M S R := le_trans (by norm_num) (three_le_nk hQ hFam hne hR)
    obtain ⟨i, hi, p, p', t, t', hA, hB, e1, e2, -, hcs⟩ :=
      exit_chordGap hM hF hfin hR h2 hc ⟨w, ⟨hwc, hwD⟩, hw⟩
    apply hwb
    refine mem_hostPoly_boundary.2 ⟨i, hi, ?_⟩
    rw [e1, e2, hostPt_eq M.W hA.2.1 hA.2.2.1, hostPt_eq M.W hB.2.1 hB.2.2.1, ← hcs]
    exact hwc
  · push Not at hwc
    have hfree : w ∈ freeIn M.D S := ⟨hwD, fun ⟨c, hc, hwc'⟩ => hwc c hc hwc'⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hsys.isOpen_freeIn subset_rfl) w hfree
    obtain ⟨u, hu, hdu⟩ := Metric.mem_closure_iff.1 hw ε hε
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR (convex_ball w ε).isPreconnected
      hball ⟨u, by rwx [mem_ball, dist_comm], hu⟩
    exact hwR (hsub (mem_ball_self hε))

/-- Mod arithmetic: `i + 1 ≡ j + 1` forces `i = j` below the modulus. -/
theorem succ_mod_inj {N i j : ℕ} (hi : i < N) (hj : j < N) (h : (i + 1) % N = (j + 1) % N) :
    i = j := by
  rcases Nat.lt_or_ge (i + 1) N with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) N with h2 | h2
  · rwo [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
  · rwo [Nat.mod_eq_of_lt h1, show j + 1 = N by omega, Nat.mod_self] at h
  · rwo [Nat.mod_eq_of_lt h2, show i + 1 = N by omega, Nat.mod_self] at h
  · omega

/-- Mod arithmetic of the chain index of a host key. -/
theorem kIdx_facts {N s i : ℕ} (hs : s < N) (hi : i < N) :
    (s + (i + N - s) % N) % N = i ∧ (s + ((i + N - s) % N + 1)) % N = (i + 1) % N := by
  constructor
  · have := chain_idx (j := 0) hs hi
    rwa [add_zero, add_zero, Nat.mod_eq_of_lt hi] at this
  · rw [← add_assoc]; exact chain_idx (j := 1) hs hi

variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **Host edges other than the gap are chain edges.** -/
theorem hostEdge_mem_set {i : ℕ} (hi : i < nk (interiorModel Q) S R) (hg : g < nk (interiorModel Q) S R)
    (hig : i ≠ g) {z : Point}
    (hz : z ∈ Chazelle.segment (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i))
      (hostPt (interiorModel Q).W
        (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)))) :
    z ∈ (hostChain Q S R g h3).set := by
  have hN : 0 < nk (interiorModel Q) S R := by omega
  have hsN : (g + 1) % nk (interiorModel Q) S R < nk (interiorModel Q) S R := Nat.mod_lt _ hN
  obtain ⟨e0, e1⟩ := kIdx_facts hsN hi
  have hkN : (i + nk (interiorModel Q) S R - (g + 1) % nk (interiorModel Q) S R) %
      nk (interiorModel Q) S R < nk (interiorModel Q) S R := Nat.mod_lt _ hN
  refine ⟨(i + nk (interiorModel Q) S R - (g + 1) % nk (interiorModel Q) S R) %
      nk (interiorModel Q) S R, ?_, ?_⟩
  · show _ < nk (interiorModel Q) S R - 1
    by_contra hk1
    have hkeq : (i + nk (interiorModel Q) S R - (g + 1) % nk (interiorModel Q) S R) %
        nk (interiorModel Q) S R = nk (interiorModel Q) S R - 1 := by omega
    rw [hkeq, show (g + 1) % nk (interiorModel Q) S R + (nk (interiorModel Q) S R - 1 + 1) =
      (g + 1) % nk (interiorModel Q) S R + nk (interiorModel Q) S R by omega,
      Nat.add_mod_right, Nat.mod_mod] at e1
    exact hig (succ_mod_inj hi hg e1.symm)
  · rw [Chain.chainEdge_eq, hostChain_vertex, hostChain_vertex, e0, e1]
    exact hz

/-- **A kept chord**: a horizontal chord of the host chain's domain meeting `R` has its open part
in `R` and its endpoints off the interior of `Q`. -/
theorem kept_chord (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    (hg : g < nk (interiorModel Q) S R) (hgc : ChordGap (interiorModel Q) S R g)
    {y a b : ℝ} (hc : IsHChordIn (hostChain Q S R g h3).dom y a b) {z₀ : Point}
    (hz₀ : z₀ ∈ Visibility.hseg y a b) (hz₀R : z₀ ∈ R) :
    (∀ x, a < x → x < b → ((x, y) : Point) ∈ R) ∧ ((a, y) : Point) ∉ (interiorModel Q).D ∧
      ((b, y) : Point) ∉ (interiorModel Q).D := by
  set M := interiorModel Q
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hsys := hM.sys S hF hfin
  have hRo : IsOpen R := hsys.regionsIn_open subset_rfl hR
  have hRdom : R ⊆ (hostChain Q S R g h3).dom := region_sub_dom hQ hFam hne hR
  have hRfree : ∀ c ∈ S, ∀ z ∈ R, z ∉ c := fun c hc z hz hzc =>
    (Chazelle.Chain.regionsIn_subset hR hz).2 ⟨c, hc, hzc⟩
  -- `z₀` lies in the open part
  obtain ⟨hz0y, hz0a, hz0b⟩ := hz₀
  have hz0a' : a < z₀.1 := by
    rcases hz0a.lt_or_eq with h | h
    · exact h
    · exfalso; apply hc.left_not
      have : z₀ = (a, y) := Prod.ext h.symm hz0y
      rw [← this]; exact hRdom hz₀R
  have hz0b' : z₀.1 < b := by
    rcases hz0b.lt_or_eq with h | h
    · exact h
    · exfalso; apply hc.right_not
      have : z₀ = (b, y) := Prod.ext h hz0y
      rw [← this]; exact hRdom hz₀R
  set O := (fun x : ℝ => ((x, y) : Point)) '' Ioo a b with hOdef
  have hOpre : IsPreconnected O :=
    isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => ((x, y) : Point)).continuousOn
  have hz0O : z₀ ∈ O := ⟨z₀.1, ⟨hz0a', hz0b'⟩, Prod.ext rfl hz0y.symm⟩
  -- the gap chord: its points off the domain are chain vertices
  obtain ⟨cg, hcg, p, p', t, t', hA, hB, ha, hb, hAB⟩ := hgc
  obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg (hF hcg) hA hB hAB
  have hAset : sidePt M.W p t ∈ (hostChain Q S R g h3).set := by
    obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3 hg
    rw [← hostPt_eq M.W hA.2.1 hA.2.2.1, ← ha, ← e]
    exact (hostChain Q S R g h3).vertex_mem_set hk
  have hBset : sidePt M.W p' t' ∈ (hostChain Q S R g h3).set := by
    obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3
      (Nat.mod_lt (g + 1) (show 0 < nk M S R by omega))
    rw [← hostPt_eq M.W hB.2.1 hB.2.2.1, ← hb, ← e]
    exact (hostChain Q S R g h3).vertex_mem_set hk
  have hend : ∀ e ∈ cg, e ∉ M.D → e ∈ (hostChain Q S R g h3).set := by
    intro e he heD
    rw [hcab] at he
    obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 he
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exact absurd (hopen s ⟨h0, h1⟩) heD
      · subst h1; rwx [Chazelle.Geometry.lerp_one]
    · subst h0; rwx [Chazelle.Geometry.lerp_zero]
  obtain ⟨yg, ag, bg, hchg, hcgeq⟩ := hF hcg
  -- the open part misses `∂H`
  have hOH : ∀ x, a < x → x < b → ((x, y) : Point) ∉ (hostPoly Q S R).boundary := by
    intro x hxa hxb hxH
    have hxD : ((x, y) : Point) ∈ (hostChain Q S R g h3).dom := hc.open_mem x hxa hxb
    obtain ⟨i, hi, hxi⟩ := mem_hostPoly_boundary.1 hxH
    by_cases hig : i = g
    · rw [hig, ha, hb, hostPt_eq M.W hA.2.1 hA.2.2.1, hostPt_eq M.W hB.2.1 hB.2.2.1,
        ← hcab, hcgeq] at hxi
      obtain ⟨hyy, hxa', hxb'⟩ := hxi
      simp only at hyy hxa' hxb'
      subst hyy
      have hag : ((ag, y) : Point) ∈ (hostChain Q S R g h3).set :=
        hend _ (by rw [hcgeq]; exact ⟨rfl, le_rfl, hchg.lt.le⟩) hchg.left_not
      have hbg : ((bg, y) : Point) ∈ (hostChain Q S R g h3).set :=
        hend _ (by rw [hcgeq]; exact ⟨rfl, hchg.lt.le, le_rfl⟩) hchg.right_not
      have hag' : ag ≤ a := by
        by_contra h; push Not at h
        exact (hostChain Q S R g h3).not_mem_set_of_mem_dom (hc.open_mem ag h (by linarith)) hag
      have hbg' : b ≤ bg := by
        by_contra h; push Not at h
        exact (hostChain Q S R g h3).not_mem_set_of_mem_dom (hc.open_mem bg (by linarith) h) hbg
      exact hRfree cg hcg z₀ hz₀R (by
        rw [hcgeq]; exact ⟨hz0y, by linarith, by linarith⟩)
    · exact (hostChain Q S R g h3).not_mem_set_of_mem_dom hxD (hostEdge_mem_set hi hg hig hxi)
  -- the open part lies in `R`
  have hcover : O ⊆ R ∪ (closure R)ᶜ := by
    rintro _ ⟨x, ⟨hxa, hxb⟩, rfl⟩
    by_cases hxR : ((x, y) : Point) ∈ R
    · exact Or.inl hxR
    · right; intro hxcl
      exact hOH x hxa hxb (frontier_sub_hostBd hQ hFam hne hR hxcl hxR)
  have hOR : O ⊆ R := IsPreconnected.subset_left_of_subset_union hRo
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.2 subset_closure) hcover
    ⟨z₀, hz0O, hz₀R⟩ hOpre
  have hOR' : ∀ x, a < x → x < b → ((x, y) : Point) ∈ R := fun x hxa hxb =>
    hOR ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hab := hc.lt
  -- an endpoint in the domain would lie on a chord of `S` running along the open part
  have hendpt : ∀ e : ℝ, (e = a ∨ e = b) → ((e, y) : Point) ∉ M.D := by
    intro e heab heD
    have hecl : ((e, y) : Point) ∈ closure R := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      set m := min (ε / 2) ((b - a) / 2) with hm
      have hm0 : 0 < m := lt_min (by linarith) (by linarith)
      have hmε : m < ε := by have := min_le_left (ε / 2) ((b - a) / 2); linarith
      have hmb : m < b - a := by have := min_le_right (ε / 2) ((b - a) / 2); linarith
      rcases heab with rfl | rfl
      · refine ⟨(e + m, y), hOR' _ (by linarith) (by linarith), ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          show e - (e + m) = -m by ring, abs_neg, abs_of_pos hm0]
        exact max_lt hmε hε
      · refine ⟨(e - m, y), hOR' _ (by linarith) (by linarith), ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          show e - (e - m) = m by ring, abs_of_pos hm0]
        exact max_lt hmε hε
    have heR : ((e, y) : Point) ∉ R := by
      rcases heab with rfl | rfl
      · exact fun h => hc.left_not (hRdom h)
      · exact fun h => hc.right_not (hRdom h)
    obtain ⟨i, hi, hei⟩ := mem_hostPoly_boundary.1 (frontier_sub_hostBd hQ hFam hne hR hecl heR)
    rcases hostEdge_cases hQ hFam hne hR hi hei with ⟨q, hq, t, ht0, ht1, he⟩ | ⟨-, c', hc', hec'⟩
    · exact hM.trace q hq t ht0 ht1.le (he ▸ heD)
    · obtain ⟨y', a', b', hch', rfl⟩ := hF hc'
      obtain ⟨hyy, ha'e, heb'⟩ := hec'
      simp only at hyy ha'e heb'
      subst hyy
      have ha'lt : a' < e := lt_of_le_of_ne ha'e (fun h => hch'.left_not (by rwx [h]))
      have heb'lt : e < b' := lt_of_le_of_ne heb' (fun h => hch'.right_not (by rwx [← h]))
      rcases heab with rfl | rfl
      · set δ := min (b' - e) (b - e) / 2 with hδ
        have h1 : 0 < δ := by have := lt_min (sub_pos.2 heb'lt) (sub_pos.2 hab); rwli [hδ]
        have h2 : δ < b' - e := by have := min_le_left (b' - e) (b - e); rwli [hδ]
        have : δ < b - e := by have := min_le_right (b' - e) (b - e); rwli [hδ]
        exact hRfree _ hc' _ (hOR' (e + δ) (by linarith) (by linarith))
          ⟨rfl, by sil only, by sil only⟩
      · set δ := min (e - a') (e - a) / 2 with hδ
        have h1 : 0 < δ := by have := lt_min (sub_pos.2 ha'lt) (sub_pos.2 hab); rwli [hδ]
        have h2 : δ < e - a' := by have := min_le_left (e - a') (e - a); rwli [hδ]
        have : δ < e - a := by have := min_le_right (e - a') (e - a); rwli [hδ]
        exact hRfree _ hc' _ (hOR' (e - δ) (by linarith) (by linarith))
          ⟨rfl, by sil only, by sil only⟩
  exact ⟨hOR', hendpt a (Or.inl rfl), hendpt b (Or.inr rfl)⟩

/-- **Kept chords are admissible in the interior model**, and meet its domain only in `R`. -/
theorem kept_adm (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    (hg : g < nk (interiorModel Q) S R) (hgc : ChordGap (interiorModel Q) S R g)
    {c : Set Point} (hc : c ∈ (chainModel (hostChain Q S R g h3)).Adm) (hcR : (c ∩ R).Nonempty) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R := by
  obtain ⟨y, a, b, hch, -, rfl⟩ := hc
  obtain ⟨z₀, hz₀, hz₀R⟩ := hcR
  obtain ⟨hin, hla, hlb⟩ := kept_chord hQ hFam hne hR hg hgc hch hz₀ hz₀R
  refine ⟨⟨y, a, b, ⟨hch.lt, hla, hlb, fun x hxa hxb =>
    (Chazelle.Chain.regionsIn_subset hR (hin x hxa hxb)).1⟩, rfl⟩, ?_⟩
  rintro z ⟨⟨hzy, hza, hzb⟩, hzD⟩
  have hz : z = (z.1, y) := Prod.ext rfl hzy
  rcases hza.lt_or_eq with h1 | h1
  · rcases hzb.lt_or_eq with h2 | h2
    · rw [hz]; exact hin _ h1 h2
    · exact absurd (by rw [hz, h2] at hzD; exact hzD) hlb
  · exact absurd (by rw [hz, ← h1] at hzD; exact hzD) hla

end

end DownHost

end Chazelle.Core
