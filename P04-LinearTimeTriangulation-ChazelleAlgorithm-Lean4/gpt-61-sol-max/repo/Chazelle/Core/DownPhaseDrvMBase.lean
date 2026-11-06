module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBase
public import Chazelle.Core.DownPhaseDrvKept

/-!
# Down-phase driver, B-M2: the base case finds every missing vertex chord region-locally

At the base of the down phase the driver completes the interior family `S` region by region
(design `docs/design-downphase-driver.md` §4.4): in the host polygon `H` of a region `R`
(`int H = R`, `∂H ⊆ ∂Q ∪ ⋃ S`), from every host vertex that is a vertex of `Q`, in every horizontal
direction entering `int H`, it shoots against the edges of `H` only.

* `hitParam_eq_of_sub`: the first hit of a ray starting into `int H ⊆ int Q` is the same in `H` and
  in `Q` if the first `∂H` point of the ray is on `∂Q`;
* **soundness** `chord_of_host`: such a region-local shot is the vertex chord of `Q`
  (`chordSet Q i σ = chordSet H j σ`), it is a vertex chord of `Q`, it is not in `S`, and its
  domain part lies in `R`;
* **completeness** `missing_found` (B-M2): every vertex chord of `Q` not in `S` is such a shot, in
  the region its domain part meets (B-M1), from a vertex of the host polygon `hostPoly Q S R`;
* `vtx_mem_hostPoly`: a vertex of `Q` in the closure of `R` is a vertex of `hostPoly Q S R`;
* `hostPoly_bd_sub`: `∂(hostPoly Q S R) ⊆ ∂Q ∪ ⋃ S`;
* `chordSet_inj`: with distinct heights, a vertex chord determines its vertex and direction (so
  the shots of the base emit no chord twice).
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt sideInArc freeIn regionsIn IsHChordIn SideAttach)
open Chazelle.Visibility (hseg rayPt chords chordSet chordEnd chordParam hitParam DirInterior)
open Chazelle.Geometry (lerp)
open DownHost

/-! ## Region-local first hits -/

/-- **The first hit in a sub-polygon.**  If the ray from `p` in direction `σ` starts into the
interior of the simple polygon `H`, the interior of `H` lies in that of `Q`, and the first boundary
point of `H` on the ray is a boundary point of `Q`, then the first hits agree. -/
theorem hitParam_eq_of_sub {H Q : Polygon} (hH : H.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    (hin : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt p σ t ∈ H.filled \ H.boundary)
    (hsub : H.filled \ H.boundary ⊆ Q.filled \ Q.boundary)
    (hbd : ∀ t, 0 < t → rayPt p σ t ∈ H.boundary →
      (∀ s, 0 < s → s < t → rayPt p σ s ∈ H.filled \ H.boundary) → rayPt p σ t ∈ Q.boundary) :
    hitParam Q p σ = hitParam H p σ ∧ 0 < hitParam H p σ ∧
      ∀ t, 0 < t → t < hitParam H p σ → rayPt p σ t ∈ H.filled \ H.boundary := by
  obtain ⟨u, hu, hsubu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hin
  rw [mem_Ioi] at hu
  obtain ⟨h1, h2, h3⟩ :=
    Visibility.hit_of_initial hH hσ hu (fun t ht1 ht2 => hsubu ⟨ht1, ht2⟩)
  have hpos : 0 < hitParam H p σ := lt_of_lt_of_le hu h1
  exact ⟨Visibility.hitParam_eq_of_first Q p σ hpos (hbd _ hpos h2 h3)
    (fun s hs1 hs2 => (hsub (h3 s hs1 hs2)).2), hpos, h3⟩

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- A region of an interior family lies in the interior of `Q`, off the chords. -/
theorem region_sub_free (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ freeIn (Q.filled \ Q.boundary) S :=
  Chazelle.Chain.regionsIn_subset hR

section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
include hQ hFam
/-- **Soundness of the region-local shot.**  Let `H` be a simple polygon whose interior is the
region `R` of `S` and whose boundary lies on `∂Q` or on chords of `S`.  If the vertex `j` of `H`
is the vertex `i` of `Q` and direction `σ` enters `int H` there, then direction `σ` enters the
interior of `Q`, the chord of `Q` at `i` in direction `σ` is the chord of `H` at `j`, it is a
vertex chord of `Q` not in `S`, and its domain part lies in `R`. -/
theorem chord_of_host
    (hR : R ∈ (interiorModel Q).regions S) {H : Polygon} (hH : H.Simple)
    (hHR : H.filled \ H.boundary = R) (hHb : H.boundary ⊆ Q.boundary ∪ ⋃₀ S)
    {i j : ℕ} (hi : i < Q.n) (hv : H.vtx j = Q.vtx i) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior H j σ) :
    DirInterior Q i σ ∧ chordSet Q i σ = chordSet H j σ ∧ chordSet Q i σ ∈ chords Q ∧
      chordSet Q i σ ∉ S ∧ chordSet Q i σ ∩ (interiorModel Q).D ⊆ R := by
  set D := Q.filled \ Q.boundary with hD
  have hRfree := region_sub_free hR
  have hRD : R ⊆ D := fun z hz => (hRfree hz).1
  have hsub : H.filled \ H.boundary ⊆ D := by simp_all
  have hσ0 : σ ≠ 0 := by grind
  set v := Q.vtx i with hvdef
  have hin : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt v σ t ∈ H.filled \ H.boundary := by
    simp_all [DirInterior] 
  have hvb : v ∈ Q.boundary := ⟨i, hi, Chazelle.Geometry.left_mem_segment _ _⟩
  -- the first boundary point of `H` on the ray is on `∂Q`
  have hbd : ∀ t, 0 < t → rayPt v σ t ∈ H.boundary →
      (∀ s, 0 < s → s < t → rayPt v σ s ∈ H.filled \ H.boundary) →
        rayPt v σ t ∈ Q.boundary := by
    intro t ht hzH hbefore
    by_contra hzQ
    set z := rayPt v σ t with hz
    -- `z` is a limit of points of `D`
    have hzcl : z ∈ closure D := by
      have hlim : Tendsto (fun s => rayPt v σ s) (𝓝[<] t) (𝓝 z) :=
        ((Visibility.continuous_rayPt v σ).tendsto t).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT ht] with s hs
      grind
    have hzF : z ∈ Q.filled :=
      (Chazelle.Jordan.isClosed_filled Q).closure_subset_iff.2 (fun w hw => hw.1) hzcl
    have hzD : z ∈ D := ⟨hzF, hzQ⟩
    obtain ⟨c, hc, hzc⟩ : ∃ c ∈ S, z ∈ c := by
      grind
    obtain ⟨y, a, b, hch, rfl⟩ := hFam.2.1 hc
    obtain ⟨hzy, hza, hzb⟩ := hzc
    have hza' : a < z.1 := lt_of_le_of_ne hza fun e => hch.left_not (by
      grind)
    have hzb' : z.1 < b := lt_of_le_of_ne hzb fun e => hch.right_not (by
      grind)
    -- a ray point just before `z` lies on the chord
    set δ := min (t / 2) (min (z.1 - a) (b - z.1) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by
      grind)
    have hδt : δ < t := by grind
    have hδa : δ < z.1 - a := by
      grind
    have hδb : δ < b - z.1 := by
      grind
    have hw := hbefore (t - δ) (by linarith) (by linarith)
    rw [hHR] at hw
    apply (hRfree hw).2
    refine ⟨hseg y a b, hc, ?_, ?_, ?_⟩
    · show v.2 = y; rw [← hzy]; rfl
    · have e : (rayPt v σ (t - δ)).1 = z.1 - σ * δ := by
        grind [Visibility.rayPt_fst]
      rw [e]; rcases hσ with rfl | rfl <;> linarith
    · have e : (rayPt v σ (t - δ)).1 = z.1 - σ * δ := by
        core_grind
      rw [e]; rcases hσ with rfl | rfl <;> linarith
  obtain ⟨heq, hpos, hint⟩ := hitParam_eq_of_sub hH hσ0 hin hsub hbd
  have hdirQ : DirInterior Q i σ := hin.mono fun t ht => hsub ht
  have hcs : chordSet Q i σ = chordSet H j σ := by
    grind [chordSet, chordEnd, chordParam]
  have hTQ : chordParam Q i σ = hitParam H v σ := heq
  -- the domain part lies in `R`
  have himg := Visibility.chordSet_eq_image hQ hi hdirQ
  have hinR : ∀ t, 0 < t → t < chordParam Q i σ → rayPt v σ t ∈ R := fun t h1 h2 => by
    grind
  refine ⟨hdirQ, hcs, ⟨i, σ, hi, hσ, hdirQ, rfl⟩, fun hS => ?_, ?_⟩
  · -- a point of the open chord would be free and on a chord of `S`
    
    have hmem : rayPt v σ (chordParam Q i σ / 2) ∈ chordSet Q i σ := by
      grind
    exact (hRfree (hinR _ (by linarith) (by linarith))).2 ⟨_, hS, hmem⟩
  · rintro z ⟨hz, hzD⟩
    rw [himg] at hz
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · grind
      · exfalso
        have := Visibility.chordEnd_mem_boundary hQ hi hdirQ
        unfold chordEnd at this
        rw [hs1] at hzD
        exact hzD.2 this
    · exfalso
      rw [← hs0, Visibility.rayPt_zero] at hzD
      exact hzD.2 hvb

/-! ## The host polygon of a region -/

/-- **The boundary of the host polygon lies on `∂Q` or on chords of `S`.** -/
theorem hostPoly_bd_sub
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).boundary ⊆ Q.boundary ∪ ⋃₀ S := by
  intro z hz
  obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hz
  obtain ⟨-, hWb, -, -⟩ := FactsInterior.interiorWalk_spec hQ
  rcases hostEdge_cases hQ hFam hne hR hi hzi with ⟨p, hp, t, ht0, ht1, rfl⟩ | ⟨-, c, hc, hzc⟩
  · left
    rw [← hWb]
    exact sidePt_mem_boundary hp ht0 ht1.le
  grind


end

/-- A point of an edge of a simple polygon that is a vertex is the start of the edge (for a
parameter in `[0, 1)`). -/
theorem sidePt_eq_vtx {W : Polygon} (hW : W.Simple) {p k : ℕ} (hp : p < W.n) (hk : k < W.n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h : sidePt W p t = W.vtx k) : t = 0 ∧ p = k := by
  rcases ht0.lt_or_eq with ht0 | ht0
  · exact absurd h (Chazelle.Jordan.simple_openEdge_ne_vtx hW hp ⟨ht0, ht1⟩ hk)
  · subst ht0
    rw [Chazelle.Chain.sidePt_zero] at h
    exact ⟨rfl, Chazelle.Jordan.simple_vtx_inj hW hp hk h⟩

/-- A vertex of `Q` is a vertex of the interior walk. -/
theorem exists_walk_vtx {k : ℕ} (hk : k < Q.n) :
    ∃ k', k' < (interiorWalk Q).n ∧ (interiorWalk Q).vtx k' = Q.vtx k := by
  unfold interiorWalk
  split_ifs
  · grind
  · refine ⟨Q.n - 1 - k, by grind [FactsInterior.rev_n], ?_⟩
    rw [FactsInterior.rev_vtx Q _ (by omega), show Q.n - 1 - (Q.n - 1 - k) = k by omega]

section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
include hQ hFam hne
/-- **A vertex of `Q` in the closure of a region is a vertex of its host polygon.** -/
theorem vtx_mem_hostPoly (hR : R ∈ (interiorModel Q).regions S) {k : ℕ} (hkn : k < Q.n)
    (hcl : Q.vtx k ∈ closure R) :
    ∃ j, j < (hostPoly Q S R).n ∧ (hostPoly Q S R).vtx j = Q.vtx k := by
  set M := interiorModel Q with hMdef
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hWs := (FactsInterior.interiorWalk_spec hQ).1
  have hvb : Q.vtx k ∈ Q.boundary := ⟨k, hkn, Chazelle.Geometry.left_mem_segment _ _⟩
  have hvR : Q.vtx k ∉ R := fun h => ((region_sub_free hR) h).1.2 hvb
  have hvH := frontier_sub_hostBd hQ hFam hne hR hcl hvR
  obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hvH
  have hHn : (hostPoly Q S R).n = nk M S R := hostPoly_n
  have h3 : 3 ≤ nk M S R := three_le_nk hQ hFam hne hR
  have hN2 : 2 ≤ nk M S R := le_trans (by norm_num) h3
  have hsi : (i + 1) % nk M S R < nk M S R := Nat.mod_lt _ (by omega)
  -- it suffices that the point is one of the two ends of the host edge
  suffices hend : Q.vtx k = hostPt M.W (hk M S R i) ∨
      Q.vtx k = hostPt M.W (hk M S R ((i + 1) % nk M S R)) by
    rcases hend with e | e
    · exact ⟨i, by simp_all, by rw [hostPoly_vtx hi, e]⟩
    · exact ⟨_, by rw [hHn]; exact hsi, by rw [hostPoly_vtx hsi, e]⟩
  obtain ⟨k', hk', hkv⟩ := exists_walk_vtx (Q := Q) hkn
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
      hB, ha, hb, hAB⟩
  · have hb1 := hostKeys_bounds (hk_mem hM hF hfin hi)
    have hb2 := hostKeys_bounds (hk_mem hM hF hfin hsi)
    have hnv : ∀ kk : ℕ, kk < M.W.n →
        ¬ sideInArc (hk M S R i) (hk M S R ((i + 1) % nk M S R)) kk := by
      intro kk hkk hkin
      exact hk_gap hM hF hfin hN2 hi
        (Or.inr ⟨kk, hkk, rfl, a', b', harc,
          hsub kk (Nat.cast_nonneg kk) (by exact_mod_cast hkk) hkin⟩) hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, hkey⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      (hk_succ_ne hM hF hfin hN2 hi) hnv _ hzi
    have hq' : q < (interiorWalk Q).n := hq
    obtain ⟨rfl, rfl⟩ := sidePt_eq_vtx hWs hq' hk' hs0 hs1 (hzq.symm.trans hkv.symm)
    -- the vertex key is an end of the gap
    have hnk := hnv q hq
    have hq0 : ((q : ℝ) + 0) = q := by ring
    rw [hq0] at hkey
    have hvq : Q.vtx k = hostPt M.W q := by
      rw [← hkv, show ((q : ℕ) : ℝ) = (q : ℝ) + 0 by ring, hostPt_eq M.W le_rfl one_pos,
        Chazelle.Chain.sidePt_zero]; rfl
    unfold sideInArc at hnk
    grind
  · -- a chord gap: the host edge is the chord, whose inner points are in the domain
    have hPa : hostPt M.W (hk M S R i) = sidePt M.W p t := by
      rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
    have hPb : hostPt M.W (hk M S R ((i + 1) % nk M S R)) = sidePt M.W p' t' := by
      rw [hb, hostPt_eq M.W hB.2.1 hB.2.2.1]
    obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hA hB hAB
    rw [hPa, hPb] at hzi ⊢
    obtain ⟨s, hs0, hs1, hs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzi
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exact absurd (hs ▸ hopen s ⟨h0, h1⟩) (fun h => h.2 hvb)
      · right; grind [Chazelle.Geometry.lerp_one]
    grind [Chazelle.Geometry.lerp_zero]

/-! ## Completeness (B-M2) -/

/-- **B-M2: every missing vertex chord is found region-locally.**  A vertex chord `c` of `Q` not
in `S` is the chord at a vertex `i` of `Q` in a direction `σ` entering the interior, whose domain
part lies in a region `R` of `S` (B-M1); the vertex `i` is a vertex `j` of the host polygon of
`R`, and direction `σ` enters `int (hostPoly Q S R) = R` there. -/
theorem missing_found {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S) :
    ∃ R ∈ (interiorModel Q).regions S, ∃ i σ, i < Q.n ∧ (σ = 1 ∨ σ = -1) ∧
      c = chordSet Q i σ ∧ DirInterior Q i σ ∧ c ∩ (interiorModel Q).D ⊆ R ∧
      ∃ j, j < (hostPoly Q S R).n ∧ (hostPoly Q S R).vtx j = Q.vtx i ∧
        DirInterior (hostPoly Q S R) j σ := by
  obtain ⟨R, hR, hcR, -⟩ := full_in_region hQ hFam hc hcS
  obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := hc
  have hT := Visibility.chordParam_pos hQ hi hdir
  have himg := Visibility.chordSet_eq_image hQ hi hdir
  -- the open chord lies in `R`
  have hopen : ∀ t, 0 < t → t < chordParam Q i σ → rayPt (Q.vtx i) σ t ∈ R := by
    intro t h1 h2
    refine hcR ⟨?_, (Visibility.chord_spec hQ hi hdir).2.2 t h1 h2⟩
    grind
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt (Q.vtx i) σ t ∈ R := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    simp_all
  -- the vertex is in the closure of `R`
  have hcl : Q.vtx i ∈ closure R := by
    have hlim : Tendsto (fun t => rayPt (Q.vtx i) σ t) (𝓝[>] 0) (𝓝 (Q.vtx i)) := by
      have := ((Visibility.continuous_rayPt (Q.vtx i) σ).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp_all
    exact mem_closure_of_tendsto hlim hev
  obtain ⟨j, hj, hjv⟩ := vtx_mem_hostPoly hQ hFam hne hR hi hcl
  refine ⟨R, hR, i, σ, hi, hσ, rfl, hdir, hcR, j, hj, hjv, ?_⟩
  unfold DirInterior
  rw [hjv, ← region_eq_intHost hQ hFam hne hR]
  exact hev

/-! ## No chord is emitted twice -/


end

/-- **With distinct heights, a vertex chord determines its vertex and its direction.** -/
theorem chordSet_inj (hQ : Q.Simple) (hdh : DistinctHeights Q) {i i' : ℕ} (hi : i < Q.n)
    (hi' : i' < Q.n) {σ σ' : ℝ} (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hd : DirInterior Q i σ) (hd' : DirInterior Q i' σ')
    (h : chordSet Q i σ = chordSet Q i' σ') : i = i' ∧ σ = σ' := by
  have hT := Visibility.chordParam_pos hQ hi hd
  have hT' := Visibility.chordParam_pos hQ hi' hd'
  have himg := Visibility.chordSet_eq_image hQ hi hd
  have himg' := Visibility.chordSet_eq_image hQ hi' hd'
  -- the vertex of `i` is on the chord of `i'`, so at the same height
  have hvi : Q.vtx i ∈ chordSet Q i' σ' := by
    rw [← h, himg]; exact ⟨0, ⟨le_rfl, hT.le⟩, Visibility.rayPt_zero _ _⟩
  rw [himg'] at hvi
  obtain ⟨s, -, hs⟩ := hvi
  have hy : (Q.vtx i').2 = (Q.vtx i).2 := by rw [← hs]; rfl
  have hii : i = i' := by
    by_contra hne
    exact hdh i' i hi' hi (Ne.symm hne) hy
  subst hii
  refine ⟨rfl, ?_⟩
  -- a point of the open chord of `σ` lies on the side `σ`
  have hm : rayPt (Q.vtx i) σ (chordParam Q i σ / 2) ∈ chordSet Q i σ' := by
    grind
  rw [himg'] at hm
  obtain ⟨u, ⟨hu0, -⟩, hu⟩ := hm
  have e := congrArg Prod.fst hu
  simp only [Visibility.rayPt_fst] at e
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
  all_goals grind

end

end DownDrv

end Chazelle.Core
