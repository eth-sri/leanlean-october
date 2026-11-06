module

public import Chazelle.MacT
public import Chazelle.Core.BruteRam3
public import Chazelle.Core.SpecNF
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.GranRamBody
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.BruteCorner

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
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, (ztewr : Point) ∈ D) ∧
      (ztews : Point) ∉ D := by
  zur
  · obtain ⟨s, hs, h1, h2⟩ := exists_first_exit hD hz (fun x hx => (abs_lt.1 (hB x hx)).2)
    grind
  · set f : Point → Point := fun p => zthqc
    zuhyo
    set D' := f ⁻¹' D
    have hD' := hD.preimage hf
    have hz' : ((-z.1, z.2) : Point) ∈ D' := by_grind
    obtain ⟨s, hs, h1, h2⟩ := exists_first_exit hD' hz' (R := B) by_grind
    grind
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **A horizontal ray leaves the region on an arc piece.** -/
theorem ray_hit (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {z : Point} (hzR : z ∈ R)
    (hvQ : ∀ i, i < Q.n → z.2 ≠ (Q.vtx i).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ s > (0 : ℝ), ∃ i i' : ℕ, i < nk ztd S R ∧ i' < nk ztd S R ∧
      i' = ztg % nk ztd S R ∧
      ∃ lam ∈ Icc (0 : ℝ) 1, (ztews : Point) =
        lerp ztbaju
          (hostPt (interiorModel Q).W (hk ztd S R i')) lam ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball (ztews : Point) r, x ∈ (interiorModel Q).D →
        x ∈ R := by
  zubze
  zuys
  zubl

  zudg
  zukhm
  have hDo := hM.isOpen
  -- the chords are at vertex heights
  have hch : ∀ c ∈ S, ∀ w ∈ c, w.2 ≠ z.2 := by
    zubrd

  -- the exit point
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit_dir hDo hzfree.1 (B := coordBound Q + 1)
    (fun x hx => by
      have := (filled_subset_square Q hx.1).1; linarith) hσ
  set q : Point := ztews with hqdef
  zudps
  have hqf : q ∈ Q.filled := by
    by_contra hnf
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_filled Q).isOpen_compl _ hnf
    zudbs
    zudpq
    zufhm

    apply hball (show (ztysg : Point) ∈ ball q r by
      zufv
      zubmn

      have : ztguu := by_grind
      zuhnn
      exact max_lt hεr hr)
    exact (hseg _ by_grind).1
  have hqb : q ∈ M.W.boundary := by
    show q ∈ (interiorWalk Q).boundary
    rw [hWb]; by_contra hb; exact hq ⟨hqf, hb⟩
  have hWn : M.W.n = Q.n := by
    show (interiorWalk Q).n = Q.n
    zufdi
    · rfl
    · zuhcp
  have hqv : ∀ j, j < M.W.n → q ≠ M.W.vtx j := by
    zujbg
    have hj' : ztsjp := by_omega
    obtain ⟨k, hk, hkv⟩ : ∃ k, k < Q.n ∧ M.W.vtx j = Q.vtx k := by
      show ∃ k, k < Q.n ∧ (interiorWalk Q).vtx j = Q.vtx k
      zugiq

      · grind
      · exact ⟨Q.n - 1 - j, by_omega, FactsInterior.rev_vtx Q j hj'⟩
    grind
  obtain ⟨p, hp, t, ht, hqe⟩ := exists_openEdge_of_mem_boundary M.W hqb hqv
  have hpt : sidePt M.W p t = q := hqe.symm
  -- the segment lies in `R`
  have hsegR : ∀ s' ∈ Ico (0 : ℝ) s, (ztewr : Point) ∈ R := by
    have hT : IsPreconnected ((fun s' : ℝ => (ztewr : Point)) '' Ico 0 s) :=
      isPreconnected_Ico.image _ ztepq
    have hTfree : (fun s' : ℝ => (ztewr : Point)) '' Ico 0 s ⊆ freeIn M.D S := by
      zuvn
      exact ⟨by_grind, fun ⟨c, hc, hmem⟩ => by_grind⟩
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR hT hTfree
      ⟨z, ⟨0, by_grind, by_simp⟩, hzR⟩
    exact fun s' hs' => hsub ztrel
  -- not a cut
  have hncut : ztyzm := by
    rintro ⟨c, hc, q', u, hA, e⟩
    zucta

  zucsi
  have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztwlx X := by
    have h1 := (Loc.tendsto_mul_const_nhdsGT ztkez).eventually
      ztjtb
    zucll
    zumet
    zuhix

  obtain ⟨r0, hr0, hnear0⟩ := Loc.near_sub_region hQ hF hfin hp ht.1.le ht.2 hncut hX hfX
  have hXR : ztpli := by
    set ε := min s r0 / 2 with hε
    zucmw
    have hεs : ztjaz := by zunbb; have := min_le_left s r0; linarith
    have hεr : ε < r0 := by zunbb; have := min_le_right s r0; linarith
    have hmem := hsegR ztdig by_grind
    have hdist : (ztysg : Point) ∈ ball ztbp r0 := by
      rw [hpt, mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      zubmn

      have : ztguu := by rcases hσ with rfl | rfl <;> norm_num
      zuhnn
      exact max_lt hεr hr0
    have hX' := hnear0 _ hdist (Chazelle.Chain.regionsIn_subset hR hmem).1
    zubba
    · zubh
    · exact absurd (h.le_bot ⟨hX', hmem⟩) zthxd
  zubch
  -- the arc piece

  have hb : ztfdt := fun i hi =>
    hostKeys_bounds ztzl
  have hlb := hA.hl ▸ hb _ hA.hil
  have hrb := hA.hr ▸ hb _ (Nat.mod_lt _ (by have := hA.hdN; omega))
  have hxb : ztgae := by
    zuhiz

    push_cast at this
    zujcc
  zuesk
  have hab' : ztmwz := by
    zudgc

  zucwr

  set xx := unwrapK n a _ with hxx
  zucgz

  zugmc
  have hex : ztydb := ⟨d - 1, by
    grind⟩
  zujun

  have hj1 : xx < ukey M S X i_l _ := Nat.find_spec hex
  have hjd : j < d := by
    zufm
    have := Nat.find_min' hex (show xx < ukey M S X i_l ztqkw by
      rw [Nat.sub_add_cancel hd0]; exact hxd)
    omega
  have hj0 : ztorn := by
    zuzo
    · grind
    · have := Nat.find_min hex ztglx
      grind
  have hjj : ukey M S X i_l j < ukey M S X i_l _ :=
    ukey_mono hM hF hfin hA.hil ztffs by_omega
  obtain ⟨q', -, -, -, hq'⟩ := arc_piece hM hF hfin hA hjd
  have hw : hostPt M.W ztudk = q := by
    rw [wrapK_unwrapK hxb, hostPt_eq M.W ht.1.le ht.2, hpt]
  have e1 := hq' xx hj0 hj1.le
  have e2 := hq' _ le_rfl hjj.le
  have e3 := hq' _ hjj.le le_rfl
  rw [wrapK_ukey hM hF hfin hA.hil by_omega] at e2 e3
  refine ⟨s, hs, ztzm % N, ztwwf % N, Nat.mod_lt _ by_omega,
    Nat.mod_lt _ by_omega, by_grind,
    (xx - ukey M S X i_l j) / (ukey M S X i_l ztl - ukey M S X i_l j),
    ⟨div_nonneg by_linarith by_linarith, (div_le_one by_linarith).2 by_linarith⟩, ?_,
    r0, hr0, fun x hx hxD => hnear0 x by_grind hxD⟩
  rw [e2, e3, lerp_lerp]
  calc q = hostPt M.W _ := hw.symm
    _ = _ := e1
    _ = _ := by
      have hne : ukey M S X i_l _ - ukey M S X i_l j ≠ 0 := sub_ne_zero.2 hjj.ne'
      grind

/-- **A region lies within the coordinate bound of its host points.** -/
theorem region_abs_le (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {B : ℝ}
    (hB : ∀ i, i < nk ztd S R →
      |(hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).1| ≤ B ∧
      |(hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).2| ≤ B) :
    ∀ z ∈ R, |z.1| < B + 1 ∧ |z.2| < B + 1 := by
  zubmj
  zubdo
  zuizk
  intro z hzR
  zudnz
  zueux
  set V : Finset ℝ := (Finset.range Q.n).image ztdzz
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ∃ η ∈ Ioo (0 : ℝ) (min ρ 1),
      η ∉ (V.image (· - z.2) : Set ℝ) :=
    ((Set.Ioo_infinite (lt_min hρ one_pos)).sdiff ztgdv).nonempty
  have hηρ' : η < ρ := by_simp_all
  have hη1 : η < 1 := by_simp_all
  zulab
  have hz'R : z' ∈ R := hball (by
    zucji

    simp_all)
  have hvQ : ztioy := by
    intro i hi e
    apply hηV
    rw [Finset.coe_image]
    exact ⟨(Q.vtx i).2, by_grind, by
      grind⟩
  -- the coordinates of a convex combination of host points
  have hcomb : ∀ i i', i < nk M S R → i' < nk M S R → ∀ lam ∈ Icc (0 : ℝ) 1,
      |(lerp (hostPt M.W (hk M S R i)) (hostPt M.W (hk M S R i')) lam).1| ≤ B ∧
      |(lerp (hostPt M.W (hk M S R i)) (hostPt M.W (hk M S R i')) lam).2| ≤ B := by
    intro i i' hi hi' lam hlam
    obtain ⟨a1, a2⟩ := hB i hi
    obtain ⟨b1, b2⟩ := hB i' hi'
    have key : ∀ u v : ℝ, |u| ≤ B → |v| ≤ B → |u + lam * ztbnr| ≤ B := by
      intro u v hu hv
      rw [abs_le] at *
      constructor <;> nlinarith [hlam.1, hlam.2, hu.1, hu.2, hv.1, hv.2]
    simp_all
  obtain ⟨s, hs, i, i', hi, hi', -, lam, hlam, he, -⟩ :=
    ray_hit hQ hFam hne hR hz'R hvQ ztp
  obtain ⟨s₂, hs₂, j, j', hj, hj', -, lam₂, hlam₂, he₂, -⟩ :=
    ray_hit hQ hFam hne hR hz'R hvQ ztbt
  have c1 := hcomb i i' hi hi' lam hlam
  have c2 := hcomb j j' hj hj' lam₂ hlam₂
  zvndl at c1
  rw [← he₂] at c2
  simp only [z'] at c1 c2
  simp only [abs_le] at c1 c2
  refine ⟨abs_lt.2 by_grind,
    abs_lt.2 ztsr⟩
theorem hostEdge_not_mem (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    {i : ℕ} (hi : i < nk ztd S R) {z : Point}
    (hz : z ∈ Chazelle.segment ztbaju
      (hostPt (interiorModel Q).W
        ztbakh)) :
    z ∉ R := by
  zubmj
  zuys
  zubl

  have h3 : 3 ≤ nk M S R := three_le_nk hQ hFam hne hR
  zucgl
  intro hzR
  zukhm
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA, hB,
    ha, hb, hAB⟩
  · zucgy
    zuyt

    have hnv : ∀ k : ℕ, k < M.W.n →
        ¬ sideInArc ztbmz ztwkn k := by
      zugoj
      exact hk_gap hM hF hfin hN2 hi
        ztenq
        hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      ztfhv hnv z hz
    exact hM.trace q hq s hs0 hs1.le (hzq ▸ hzfree.1)
  · have hPa : ztxpu := by
      zudjz
    have hPb : ztbalo := by
      zubyq
    obtain ⟨hcab, -⟩ := hM.attach_seg ztlz hA hB hAB
    rw [hPa, hPb, ← hcab] at hz
    exact hzfree.2 ⟨c, hc, hz⟩
variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The region lies in the domain of the host chain.** -/
theorem region_sub_dom (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ (hostChain Q S R g h3).dom := by
  zubmj
  zudku
  zujmq
  zuftq
  have hCn : C.P.n = N := hostPoly_n
  -- every host point is a chain vertex
  have hvert : ∀ i, i < N → ∃ k, k ≤ C.m ∧ C.vertex k = hostPt M.W ztbmz := by
    zug
    refine ⟨ztwtu % N, by
      have := Nat.mod_lt ztwtu hN; show _ ≤ N - 1; omega, ?_⟩
    zuiki
  -- the box
  have hbox : ∀ z ∈ R, z ∈ Chazelle.Chain.box C.radius := by
    zugh
    have hB : ∀ i, i < N → |(hostPt M.W ztbmz).1| ≤ coordBound C.P ∧
        |(hostPt M.W (hk M S R i)).2| ≤ coordBound C.P := by
      zug
      zufkf
      zulqw
      exact C.abs_le_coordBound_of_mem_set ztdkv
    have := region_abs_le hQ hFam hne hR hB z hz
    tauto
  -- the chain
  have hset : ∀ z ∈ R, z ∉ C.set := by
    intro z hz ⟨k, hk, hzk⟩
    rw [C.chainEdge_eq, hostChain_vertex, hostChain_vertex] at hzk
    set i := (ztbs % N + k) % N
    have hi : i < N := Nat.mod_lt _ hN
    have e : (ztbs % N + zts) % N = ztg % N := by
      grind
    zvmwe at hzk
    exact hostEdge_not_mem hQ hFam hne hR hi hzk hz
  -- the slit
  have htop : ∀ z ∈ R, z.2 ≤ C.top.2 := by
    zujfd
    zufkf
    zvmyr; exact C.vertex_snd_le_top hk
  zugh
  refine (C.mem_dom_iff).2 ⟨hbox z hz, hset z hz, fun hs => ?_⟩
  zufxy
  have h3' := htop z hz
  have hzt : z = C.top := Prod.ext h1 (le_antisymm h3' h2)
  exact hset z hz zttov

/-- **Every host point is a chain vertex.** -/
theorem host_vertex (_h3' : 3 ≤ nk ztd S R) {i : ℕ}
    (hi : i < nk ztd S R) :
    ∃ k, k ≤ (hostChain Q S R g h3).m ∧
      (hostChain Q S R g h3).vertex k = hostPt (interiorModel Q).W ztwln := by
  zujmr
  zuftq
  refine ⟨ztwtu % N, by
    have := Nat.mod_lt ztwtu hN; show _ ≤ N - 1; omega, ?_⟩
  zuiki

/-- **The region lies below the top of its host chain.** -/
theorem region_below_top (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    ∀ z ∈ R, z.2 ≤ (hostChain Q S R g h3).top.2 := by
  zujfd
  obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3 hi
  zvmyr; exact (hostChain Q S R g h3).vertex_snd_le_top hk
open Chazelle.Chain (TouchesIn IsHChordIn)
open Chazelle.Geometry (lerp_mem_segment)
theorem mem_hostPoly_boundary {z : Point} :
    z ∈ (hostPoly Q S R).boundary ↔ ∃ i, i < nk ztd S R ∧
      z ∈ Chazelle.segment ztbaju
        (hostPt (interiorModel Q).W
          ztbakh) := by
  have hn := hostPoly_n (Q := Q) (S := S) (R := R)
  constructor
  · zuifs
    zukvf
    unfold Polygon.edge at hz
    rw [hn, hostPoly_vtx hi, hostPoly_vtx ztcv] at hz
    grind
  · zuifs
    refine ztrdj
    zucrd
    rw [hn, hostPoly_vtx hi, hostPoly_vtx ztcv]
    exact hz

/-- **A host edge** consists of walk points and of points of chords of `S` in the domain. -/
theorem hostEdge_cases (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    {i : ℕ} (hi : i < nk ztd S R) {z : Point}
    (hz : z ∈ Chazelle.segment ztbaju
      (hostPt (interiorModel Q).W
        ztbakh)) :
    (∃ p, p < (interiorModel Q).W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      z = sidePt (interiorModel Q).W p t) ∨ (z ∈ (interiorModel Q).D ∧ ∃ c ∈ S, z ∈ c) := by
  zubmj
  zuys
  zubl

  zukh
  zucgl
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
    hB, ha, hb, hAB⟩
  · left
    zucgy
    zuyt

    have hnv : ∀ k : ℕ, k < M.W.n →
        ¬ sideInArc ztbmz ztwkn k := by
      zugoj
      exact hk_gap hM hF hfin hN2 hi
        (Or.inr ⟨k, hk, rfl, a', b', harc, by_simp_all⟩)
        hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      ztfhv hnv z hz
    exact ⟨q, hq, s, hs0, hs1, hzq⟩
  · have hPa : ztxpu := by
      zudjz
    have hPb : ztbalo := by
      zubyq
    zubbw
    rw [hPa, hPb] at hz
    zubxv
    zunl
    · zuqy
      · right
        grind
      · left
        zucuj
        rw [Chazelle.Geometry.lerp_one]
        exact ⟨p', hB.1, t', hB.2.1, hB.2.2.1, rfl⟩
    · left
      zubvi
      rw [Chazelle.Geometry.lerp_zero]
      exact ⟨p, hA.1, t, hA.2.1, hA.2.2.1, rfl⟩

/-- The boundary of the host polygon lies in the filled polygon `Q`. -/
theorem hostBd_sub_filled (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).boundary ⊆ Q.filled := by
  zugh
  obtain ⟨i, hi, hz⟩ := mem_hostPoly_boundary.1 hz
  zueto
  rcases hostEdge_cases hQ hFam hne hR hi hz with ⟨p, hp, t, ht0, ht1, rfl⟩ | ⟨hzD, -⟩
  · apply Chazelle.Jordan.boundary_subset_filled
    zugxr

  · exact hzD.1

/-- **The filled host polygon lies in the filled polygon `Q`** (Jordan: the exterior of `Q` is
connected, misses `∂H` and contains far points). -/
theorem hostFilled_sub (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).filled ⊆ Q.filled := by
  zuh
  by_contra hxQ
  zuhwu
  set w : Point := (max (coordBound ztefi) ztvlq + 1, 0) with hw
  have hwQ : w ∉ Q.filled := Chazelle.Jordan.far_not_mem_filled Q by_grind
  have hwH : w ∉ (hostPoly Q S R).filled :=
    Chazelle.Jordan.far_not_mem_filled _ by_grind
  have hsub : Q.filledᶜ ⊆ (hostPoly Q S R).boundaryᶜ := fun y hy hyb =>
    hy (hostBd_sub_filled hQ hFam hne hR hyb)
  exact FactsInterior.subset_exterior hH (Chazelle.Jordan.filled_compl_connected hQ) hsub hwQ hwH
    hxQ hx

/-- **The interior of the host polygon lies in the interior of `Q`.** -/
theorem intHost_sub (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).filled \ (hostPoly Q S R).boundary ⊆ Q.filled \ Q.boundary := by
  zucvw
  rw [← Chazelle.Jordan.interior_filled hH, ← Chazelle.Jordan.interior_filled hQ]
  exact interior_mono (hostFilled_sub hQ hFam hne hR)

/-- An open nonempty set has a point off finitely many heights. -/
theorem exists_mem_off_heights {U : Set Point} (hU : IsOpen U) (hne : U.Nonempty)
    (V : Finset ℝ) : ∃ z ∈ U, z.2 ∉ V := by
  zucik
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ztezm :=
    ((Set.Ioo_infinite hρ).sdiff ztgdv).nonempty
  refine ⟨ztkho, hball ?_, fun h => hηV ?_⟩
  · zukpt
    simp only [Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη0]
    simp_all
  grind

/-- **The region lies in the interior of its host polygon.** -/
theorem region_sub_intHost (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ (hostPoly Q S R).filled \ (hostPoly Q S R).boundary := by
  zubmj
  zubdo
  zuizk
  zudnz
  zuhwu
  have hRb : R ⊆ (hostPoly Q S R).boundaryᶜ := fun z hz hzb => by
    obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hzb
    exact hostEdge_not_mem hQ hFam hne hR hi hzi hz
  obtain ⟨z, hzR, hzV⟩ := exists_mem_off_heights hRo ztuxl
    ztyux
  have hvQ : ztioz := by_grind
  obtain ⟨s, -, i, i', hi, -, rfl, lam, hlam, he, r, hr, hnear⟩ :=
    ray_hit hQ hFam hne hR hzR hvQ ztp
  have hqb : (ztokl : Point) ∈ (hostPoly Q S R).boundary :=
    mem_hostPoly_boundary.2 ⟨i, hi, by zvmxm; exact lerp_mem_segment _ _ hlam.1 hlam.2⟩
  obtain ⟨u, hu, hdu⟩ := Metric.mem_closure_iff.1
    (Chazelle.Jordan.boundary_subset_closure_interior hH hqb) r hr
  have huD := intHost_sub hQ hFam hne hR hu
  have huR := hnear u (by zunop; omega) huD
  exact FactsInterior.subset_interior hH ztpwu hRb huR hu.1

/-- **The frontier of the region lies on the boundary of its host polygon.** -/
theorem frontier_sub_hostBd (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {w : Point}
    (hw : w ∈ closure R) (hwR : w ∉ R) : w ∈ (hostPoly Q S R).boundary := by
  zubmj
  zubdo
  zubl

  zucwp
  by_contra hwb
  have hwf :=
    closure_minimal (fun x hx => (region_sub_intHost hQ hFam hne hR hx).1)
      (Chazelle.Jordan.isClosed_filled _) hw
  have hwD : w ∈ M.D := intHost_sub hQ hFam hne hR by_simp_all
  by_cases hwc : ∃ c ∈ S, w ∈ c
  · obtain ⟨c, hc, hwc⟩ := hwc
    have h2 : ztfkq := le_trans by_norm_num (three_le_nk hQ hFam hne hR)
    obtain ⟨i, hi, p, p', t, t', hA, hB, e1, e2, -, hcs⟩ :=
      exit_chordGap hM hF hfin hR h2 hc ⟨w, ztuim, hw⟩
    apply hwb
    refine mem_hostPoly_boundary.2 ztbfn
    rw [e1, e2, hostPt_eq M.W hA.2.1 hA.2.2.1, hostPt_eq M.W hB.2.1 hB.2.2.1, ← hcs]
    omega
  · push Not at hwc
    have hfree : w ∈ freeIn M.D S := ⟨hwD, by_simp_all⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hsys.isOpen_freeIn subset_rfl) w hfree
    obtain ⟨u, hu, hdu⟩ := Metric.mem_closure_iff.1 hw ε hε
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR (convex_ball w ε).isPreconnected
      hball ⟨u, by zunop; omega, hu⟩
    exact hwR (hsub (mem_ball_self hε))

/-- Mod arithmetic: `i + 1 ≡ j + 1` forces `i = j` below the modulus. -/
theorem succ_mod_inj {N i j : ℕ} (hi : i < N) (hj : j < N) (h : ztg % N = ztl % N) :
    i = j := by
  rcases Nat.lt_or_ge ztg N with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) N with h2 | h2
  · zufmp
  · rw [Nat.mod_eq_of_lt h1, show j + 1 = N by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show i + 1 = N by omega, Nat.mod_self] at h; omega
  · omega

/-- Mod arithmetic of the chain index of a host key. -/
theorem kIdx_facts {N s i : ℕ} (hs : s < N) (hi : i < N) :
    ztzgw % N = i ∧ (s + (ztgkf % N + 1)) % N = ztg % N := by
  constructor
  · have := chain_idx (j := 0) hs hi
    rwa [add_zero, add_zero, Nat.mod_eq_of_lt hi] at this
  · zuork; exact chain_idx hs hi
variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **Host edges other than the gap are chain edges.** -/
theorem hostEdge_mem_set {i : ℕ} (hi : i < nk ztd S R) (hg : g < nk ztd S R)
    (hig : i ≠ g) {z : Point}
    (hz : z ∈ Chazelle.segment ztbaju
      (hostPt (interiorModel Q).W
        ztbakh)) :
    z ∈ (hostChain Q S R g h3).set := by
  zujzq
  have hsN : ztbs % nk _ S R < nk _ S R := Nat.mod_lt _ hN
  obtain ⟨e0, e1⟩ := kIdx_facts hsN hi
  have hkN : ztwwe %
      nk _ S R < nk _ S R := Nat.mod_lt _ hN
  refine ⟨ztwwe %
      nk ztd S R, ?_, ?_⟩
  · show _ < nk _ S R - 1
    by_contra hk1
    have hkeq : ztwwe %
        nk ztd S R = nk ztd S R - 1 := by_omega
    rw [hkeq, show ztbs % nk _ S R + (nk _ S R - 1 + 1) =
      ztbs % nk ztd S R + nk ztd S R by omega,
      Nat.add_mod_right, Nat.mod_mod] at e1
    exact hig (succ_mod_inj hi hg e1.symm)
  · rw [Chain.chainEdge_eq, hostChain_vertex, hostChain_vertex, e0, e1]
    exact hz

/-- **A kept chord**: a horizontal chord of the host chain's domain meeting `R` has its open part
in `R` and its endpoints off the interior of `Q`. -/
theorem kept_chord (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    (hg : g < nk ztd S R) (hgc : ChordGap ztd S R g)
    {y a b : ℝ} (hc : IsHChordIn (hostChain Q S R g h3).dom y a b) {z₀ : Point}
    (hz₀ : z₀ ∈ Visibility.hseg y a b) (hz₀R : z₀ ∈ R) :
    (∀ x, a < x → x < b → (ztjw : Point) ∈ R) ∧ (ztdv : Point) ∉ (interiorModel Q).D ∧
      (ztdy : Point) ∉ (interiorModel Q).D := by
  zubmj
  zubdo
  zubl

  zucwp
  zudnz
  have hRdom : ztfkv := region_sub_dom hQ hFam hne hR
  have hRfree : ∀ c ∈ S, ∀ z ∈ R, z ∉ c := fun c hc z hz hzc =>
    (Chazelle.Chain.regionsIn_subset hR hz).2 by_grind
  -- `z₀` lies in the open part
  obtain ⟨hz0y, hz0a, hz0b⟩ := hz₀
  have hz0a' : a < z₀.1 := by
    rcases hz0a.lt_or_eq with h | h
    · zubh
    · exfalso; apply hc.left_not
      grind
  have hz0b' : z₀.1 < b := by
    rcases hz0b.lt_or_eq with h | h
    · zubh
    · exfalso; apply hc.right_not
      grind
  set O := (fun x : ℝ => (ztjw : Point)) '' Ioo a b with hOdef
  have hOpre : IsPreconnected O :=
    isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => (ztjw : Point)).continuousOn
  have hz0O : z₀ ∈ O := by_grind
  -- the gap chord: its points off the domain are chain vertices
  obtain ⟨cg, hcg, p, p', t, t', hA, hB, ha, hb, hAB⟩ := hgc
  obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg (hF hcg) hA hB hAB
  have hAset : sidePt M.W p t ∈ (hostChain Q S R g h3).set := by
    obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3 hg
    rw [← hostPt_eq M.W hA.2.1 hA.2.2.1, ← ha, ← e]
    zufrz
  have hBset : sidePt M.W p' t' ∈ (hostChain Q S R g h3).set := by
    obtain ⟨k, hk, e⟩ := host_vertex (g := g) (h3 := h3) h3
      (Nat.mod_lt ztbs (show 0 < nk M S R by omega))
    rw [← hostPt_eq M.W hB.2.1 hB.2.2.1, ← hb, ← e]
    zufrz
  have hend : ∀ e ∈ cg, e ∉ M.D → e ∈ (hostChain Q S R g h3).set := by
    intro e he heD
    zvmyh at he
    obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 he
    zunl
    · zuqy
      · exact absurd (hopen s by_grind) heD
      · subst h1; rw [Chazelle.Geometry.lerp_one]; omega
    · subst h0; rw [Chazelle.Geometry.lerp_zero]; omega
  obtain ⟨yg, ag, bg, hchg, hcgeq⟩ := hF hcg
  -- the open part misses `∂H`
  have hOH : ∀ x, a < x → x < b → (ztjw : Point) ∉ (hostPoly Q S R).boundary := by
    intro x hxa hxb hxH
    have hxD := hc.open_mem x hxa hxb
    obtain ⟨i, hi, hxi⟩ := mem_hostPoly_boundary.1 hxH
    by_cases hig : i = g
    · rw [hig, ha, hb, hostPt_eq M.W hA.2.1 hA.2.2.1, hostPt_eq M.W hB.2.1 hB.2.2.1,
        ← hcab, hcgeq] at hxi
      obtain ⟨hyy, hxa', hxb'⟩ := hxi
      simp only at hyy hxa' hxb'
      zulau
      have hag :=
        hend _ (by zuoee; exact ⟨rfl, le_rfl, hchg.lt.le⟩) hchg.left_not
      have hbg :=
        hend _ (by zuoee; exact ⟨rfl, hchg.lt.le, le_rfl⟩) hchg.right_not
      have hag' : ag ≤ a := by
        zufm
        exact (hostChain Q S R g h3).not_mem_set_of_mem_dom (hc.open_mem ag h by_linarith) hag
      have hbg' : b ≤ bg := by
        zufm
        exact (hostChain Q S R g h3).not_mem_set_of_mem_dom (hc.open_mem bg by_linarith h) hbg
      exact hRfree cg hcg z₀ hz₀R (by
        zuoee; exact ⟨hz0y, by_linarith, by_linarith⟩)
    · exact (hostChain Q S R g h3).not_mem_set_of_mem_dom hxD (hostEdge_mem_set hi hg hig hxi)
  -- the open part lies in `R`
  have hcover : O ⊆ R ∪ (closure R)ᶜ := by
    rintro _ ⟨x, ⟨hxa, hxb⟩, rfl⟩
    by_cases hxR : (ztjw : Point) ∈ R
    · tauto
    · right; intro hxcl
      exact hOH x hxa hxb (frontier_sub_hostBd hQ hFam hne hR hxcl hxR)
  have hOR := IsPreconnected.subset_left_of_subset_union hRo
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.2 subset_closure) hcover
    ⟨z₀, hz0O, hz₀R⟩ hOpre
  have hOR' : ∀ x, a < x → x < b → (ztjw : Point) ∈ R := fun x hxa hxb =>
    hOR ⟨x, by_grind, rfl⟩
  have hab := hc.lt
  -- an endpoint in the domain would lie on a chord of `S` running along the open part
  have hendpt : ∀ e : ℝ, ztnxq → (ztcna : Point) ∉ M.D := by
    intro e heab heD
    have hecl : (ztcna : Point) ∈ closure R := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      set m := min ztfvo ztwsh with hm
      have hm0 : ztphu := lt_min by_linarith by_linarith
      have hmε : ztski := by have := min_le_left ztfvo ztwsh; linarith
      have hmb : m < b - a := by have := min_le_right ztfvo ztwsh; linarith
      zufzw
      · refine ⟨(e + m, y), hOR' _ by_linarith by_linarith, ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          show e - (e + m) = -m by ring, abs_neg, abs_of_pos hm0]
        zulzg
      · refine ⟨(e - m, y), hOR' _ by_linarith by_linarith, ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          show e - (e - m) = m by ring, abs_of_pos hm0]
        zulzg
    have heR : (ztcna : Point) ∉ R := by
      zufzw
      · exact fun h => hc.left_not ztvts
      · exact fun h => hc.right_not ztvts
    obtain ⟨i, hi, hei⟩ := mem_hostPoly_boundary.1 (frontier_sub_hostBd hQ hFam hne hR hecl heR)
    rcases hostEdge_cases hQ hFam hne hR hi hei with ⟨q, hq, t, ht0, ht1, he⟩ | ⟨-, c', hc', hec'⟩
    · exact hM.trace q hq t ht0 ht1.le by_grind
    · obtain ⟨y', a', b', hch', rfl⟩ := hF hc'
      obtain ⟨hyy, ha'e, heb'⟩ := hec'
      simp only at hyy ha'e heb'
      zulau
      have ha'lt := lt_of_le_of_ne ha'e (fun h => hch'.left_not (by zvmwc; tauto))
      have heb'lt := lt_of_le_of_ne heb' (fun h => hch'.right_not (by zvmzi; tauto))
      zufzw
      · set δ := min ztnrp ztnrn / 2 with hδ
        zujyd
        have h2 : δ < b' - e := by have := min_le_left ztnrp ztnrn; grind
        have : δ < b - e := by have := min_le_right ztnrp ztnrn; grind
        exact hRfree _ hc' _ (hOR' (e + δ) by_linarith by_linarith)
          ⟨rfl, by_grind, by_grind⟩
      · set δ := min ztnxp ztjug / 2 with hδ
        zujyd
        have h2 : δ < e - a' := by have := min_le_left ztnxp ztjug; grind
        have : δ < e - a := by have := min_le_right ztnxp ztjug; grind
        exact hRfree _ hc' _ (hOR' (e - δ) by_linarith by_linarith)
          ⟨rfl, by_grind, by_grind⟩
  exact ⟨hOR', hendpt a ztp, hendpt b ztbt⟩

/-- **Kept chords are admissible in the interior model**, and meet its domain only in `R`. -/
theorem kept_adm (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S)
    (hg : g < nk ztd S R) (hgc : ChordGap ztd S R g)
    {c : Set Point} (hc : c ∈ (chainModel ztog).Adm) (hcR : (c ∩ R).Nonempty) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R := by
  obtain ⟨y, a, b, hch, -, rfl⟩ := hc
  obtain ⟨z₀, hz₀, hz₀R⟩ := hcR
  obtain ⟨hin, hla, hlb⟩ := kept_chord hQ hFam hne hR hg hgc hch hz₀ hz₀R
  refine ⟨⟨y, a, b, ⟨hch.lt, hla, hlb, fun x hxa hxb =>
    (Chazelle.Chain.regionsIn_subset hR by_simp_all).1⟩, rfl⟩, ?_⟩
  rintro z ⟨⟨hzy, hza, hzb⟩, hzD⟩
  grind
end
end DownHost
namespace DownDrv
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open DownHost
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {g : ℕ}
  {h3 : 3 ≤ nk ztd S R}

/-- **The region is the interior of its host polygon.** -/
theorem region_eq_intHost (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R = (hostPoly Q S R).filled \ (hostPoly Q S R).boundary := by
  zucvw
  have hMH : WalkAx (interiorModel ztefi) := walkAx_interiorModel hH
  zuok
  have hRo : ztrfp := (hM.sys S hFam.2.1 hFam.1).regionsIn_open subset_rfl hR
  zuhib
  have hsub := region_sub_intHost hQ hFam hne hR
  refine Subset.antisymm hsub ?_
  have hpre : IsPreconnected ((hostPoly Q S R).filled \ (hostPoly Q S R).boundary) := hMH.preconn
  refine hpre.subset_of_closure_inter_subset hRo ⟨z, hsub hz, hz⟩ ?_
  rintro w ⟨hwc, hwH⟩
  by_contra hwR
  exact hwH.2 (frontier_sub_hostBd hQ hFam hne hR hwc hwR)

/-- The left endpoint of a horizontal segment written as a segment of two points is one of
them. -/
theorem left_end_of_segment {a' b' : Point} {y a b : ℝ} (hab : a < b) (hy : a'.2 = b'.2)
    (h : hseg y a b = Chazelle.segment a' b') : (ztdv : Point) = a' ∨ (ztdv : Point) = b' := by
  zujhh
  obtain ⟨h1, h2, -⟩ := Merge.hseg_inj hab.le h
  grind

/-- The horizontal direction to the right. -/
def eX : Point := ztcei
open Chazelle.Chain (sideInArc freeIn regionsIn)
open Chazelle.Visibility (rayPt chords chordSet chordEnd chordParam hitParam DirInterior)
open Chazelle.Geometry (lerp)
theorem hitParam_eq_of_sub {H Q : Polygon} (hH : H.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    (hin : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt p σ t ∈ H.filled \ H.boundary)
    (hsub : H.filled \ H.boundary ⊆ Q.filled \ Q.boundary)
    (hbd : ∀ t, 0 < t → rayPt p σ t ∈ H.boundary →
      (∀ s, 0 < s → s < t → rayPt p σ s ∈ H.filled \ H.boundary) → rayPt p σ t ∈ Q.boundary) :
    hitParam Q p σ = hitParam H p σ ∧ 0 < hitParam H p σ ∧
      ∀ t, 0 < t → t < hitParam H p σ → rayPt p σ t ∈ H.filled \ H.boundary := by
  obtain ⟨u, hu, hsubu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hin
  zuduw
  obtain ⟨h1, h2, h3⟩ :=
    Visibility.hit_of_initial hH hσ hu (fun t ht1 ht2 => hsubu ztuii)
  have hpos : 0 < hitParam H p σ := by_grind
  exact ⟨Visibility.hitParam_eq_of_first Q p σ hpos by_grind
    by_grind, hpos, h3⟩
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- A region of an interior family lies in the interior of `Q`, off the chords. -/
theorem region_sub_free (hR : R ∈ (interiorModel Q).regions S) :
    R ⊆ freeIn ztrx S :=
  Chazelle.Chain.regionsIn_subset hR

/-- **Soundness of the region-local shot.**  Let `H` be a simple polygon whose interior is the
region `R` of `S` and whose boundary lies on `∂Q` or on chords of `S`.  If the vertex `j` of `H`
is the vertex `i` of `Q` and direction `σ` enters `int H` there, then direction `σ` enters the
interior of `Q`, the chord of `Q` at `i` in direction `σ` is the chord of `H` at `j`, it is a
vertex chord of `Q` not in `S`, and its domain part lies in `R`. -/
theorem chord_of_host (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : R ∈ (interiorModel Q).regions S) {H : Polygon} (hH : H.Simple)
    (hHR : H.filled \ H.boundary = R) (hHb : H.boundary ⊆ Q.boundary ∪ ⋃₀ S)
    {i j : ℕ} (hi : i < Q.n) (hv : H.vtx j = Q.vtx i) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior H j σ) :
    DirInterior Q i σ ∧ chordSet Q i σ = chordSet H j σ ∧ chordSet Q i σ ∈ chords Q ∧
      chordSet Q i σ ∉ S ∧ chordSet Q i σ ∩ (interiorModel Q).D ⊆ R := by
  zuint
  have hRfree := region_sub_free hR
  have hRD : R ⊆ D := fun z hz => (hRfree hz).1
  have hsub : H.filled \ H.boundary ⊆ D := by_simp_all
  zubat
  set v := Q.vtx i with hvdef
  have hin : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt v σ t ∈ H.filled \ H.boundary := by
    have := hdir; unfold DirInterior at this; simp_all
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
    have hzF :=
      (Chazelle.Jordan.isClosed_filled Q).closure_subset_iff.2 by_simp_all hzcl
    have hzD : z ∈ D := by_simp_all
    obtain ⟨c, hc, hzc⟩ : ∃ c ∈ S, z ∈ c := by
      grind
    obtain ⟨y, a, b, hch, rfl⟩ := hFam.2.1 hc
    zugpz
    have hza' := lt_of_le_of_ne hza fun e => hch.left_not (by
      grind)
    have hzb' := lt_of_le_of_ne hzb fun e => hch.right_not (by
      grind)
    -- a ray point just before `z` lies on the chord
    set δ := min (t / 2) (min ztueu zttfl / 2) with hδ
    zukhp
    have hδt : δ < t := by_grind
    have hδa : δ < z.1 - a := by
      grind
    have hδb : δ < b - z.1 := by
      grind
    have hw := hbefore (t - δ) by_linarith by_linarith
    rw [hHR] at hw
    apply (hRfree hw).2
    refine ⟨hseg y a b, hc, ?_, ?_, ?_⟩
    · tauto
    · have e : ztgtq := by
        zugvs
      zuexj
    · have e : ztgtq := by
        zugvs
      zuexj
  obtain ⟨heq, hpos, hint⟩ := hitParam_eq_of_sub hH hσ0 hin hsub hbd
  have hdirQ : DirInterior Q i σ := hin.mono by_grind
  have hcs : chordSet Q i σ = chordSet H j σ := by
    unfold chordSet chordEnd chordParam
    grind
  have hTQ : chordParam Q i σ = hitParam H v σ := heq
  -- the domain part lies in `R`
  have himg := Visibility.chordSet_eq_image hQ hi hdirQ
  have hinR : ∀ t, 0 < t → t < chordParam Q i σ → rayPt v σ t ∈ R := fun t h1 h2 => by
    grind
  refine ⟨hdirQ, hcs, ⟨i, σ, hi, hσ, hdirQ, rfl⟩, fun hS => ?_, ?_⟩
  · -- a point of the open chord would be free and on a chord of `S`
    have hT := Visibility.chordParam_pos hQ hi hdirQ
    have hmem : rayPt v σ ztpad ∈ chordSet Q i σ := by
      grind
    exact (hRfree by_grind).2 ⟨_, hS, hmem⟩
  · rintro z ⟨hz, hzD⟩
    rw [himg] at hz
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
    zunm
    · zuji
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
theorem hostPoly_bd_sub (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    (hostPoly Q S R).boundary ⊆ Q.boundary ∪ ⋃₀ S := by
  zugh
  obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hz
  zueto
  rcases hostEdge_cases hQ hFam hne hR hi hzi with ⟨p, hp, t, ht0, ht1, rfl⟩ | ⟨-, c, hc, hzc⟩
  · left
    zugxr

  grind

/-- A point of an edge of a simple polygon that is a vertex is the start of the edge (for a
parameter in `[0, 1)`). -/
theorem sidePt_eq_vtx {W : Polygon} (hW : W.Simple) {p k : ℕ} (hp : p < W.n) (hk : k < W.n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h : sidePt W p t = W.vtx k) : t = 0 ∧ p = k := by
  rcases ht0.lt_or_eq with ht0 | ht0
  · exact absurd h (Chazelle.Jordan.simple_openEdge_ne_vtx hW hp by_simp_all hk)
  · zudlw
    rw [Chazelle.Chain.sidePt_zero] at h
    exact ⟨rfl, Chazelle.Jordan.simple_vtx_inj hW hp hk h⟩

/-- A vertex of `Q` is a vertex of the interior walk. -/
theorem exists_walk_vtx {k : ℕ} (hk : k < Q.n) :
    ∃ k', k' < (interiorWalk Q).n ∧ (interiorWalk Q).vtx k' = Q.vtx k := by
  zugiq

  · grind
  · refine ⟨Q.n - 1 - k, by rw [FactsInterior.rev_n]; omega, ?_⟩
    rw [FactsInterior.rev_vtx Q _ by_omega, show Q.n - 1 - ztcgz = k by omega]

/-- **A vertex of `Q` in the closure of a region is a vertex of its host polygon.** -/
theorem vtx_mem_hostPoly (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {k : ℕ} (hkn : k < Q.n)
    (hcl : Q.vtx k ∈ closure R) :
    ∃ j, j < (hostPoly Q S R).n ∧ (hostPoly Q S R).vtx j = Q.vtx k := by
  zubze
  zubdo
  zubl

  zudyr
  have hvb : Q.vtx k ∈ Q.boundary := ⟨k, hkn, Chazelle.Geometry.left_mem_segment _ _⟩
  have hvR := fun h => ((region_sub_free hR) h).1.2 hvb
  have hvH := frontier_sub_hostBd hQ hFam hne hR hcl hvR
  obtain ⟨i, hi, hzi⟩ := mem_hostPoly_boundary.1 hvH
  zujzj
  zukh
  zucgl
  zucgy
  -- it suffices that the point is one of the two ends of the host edge
  suffices hend : Q.vtx k = hostPt M.W ztbmz ∨
      Q.vtx k = hostPt M.W (hk M S R _) by
    rcases hend with e | e
    · exact ⟨i, by_simp_all, by rw [hostPoly_vtx hi, e]⟩
    · exact ⟨_, by zuovs; omega, by rw [hostPoly_vtx hsi, e]⟩
  obtain ⟨k', hk', hkv⟩ := exists_walk_vtx (Q := Q) hkn
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
      hB, ha, hb, hAB⟩
  · zuyt

    have hnv : ∀ kk : ℕ, kk < M.W.n →
        ¬ sideInArc ztbmz ztwkn kk := by
      intro kk hkk hkin
      exact hk_gap hM hF hfin hN2 hi
        (Or.inr ⟨kk, hkk, rfl, a', b', harc,
          by simp_all⟩) hkin
    obtain ⟨q, hq, s, hs0, hs1, hzq, hkey⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
      ztfhv hnv _ hzi
    zubwm
    obtain ⟨rfl, rfl⟩ := sidePt_eq_vtx hWs hq' hk' hs0 hs1 (hzq.symm.trans hkv.symm)
    -- the vertex key is an end of the gap
    have hnk := hnv q hq
    have hq0 : ztmzn = q := by_ring
    rw [hq0] at hkey
    have hvq : Q.vtx k = hostPt M.W q := by
      rw [← hkv, show ((q : ℕ) : ℝ) = (q : ℝ) + 0 by ring, hostPt_eq M.W le_rfl one_pos,
        Chazelle.Chain.sidePt_zero]; rfl
    unfold sideInArc at hnk
    split_ifs at hkey hnk with hlt
    · rcases hkey.1.lt_or_eq with h1 | h1
      · grind
      grind
    · push Not at hnk
      rcases hkey with h1 | h1
      · grind
      grind
  · -- a chord gap: the host edge is the chord, whose inner points are in the domain
    have hPa : ztxpu := by
      zudjz
    have hPb : ztbalo := by
      zubyq
    obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg ztlz hA hB hAB
    rw [hPa, hPb] at hzi ⊢
    obtain ⟨s, hs0, hs1, hs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzi
    zunl
    · zuqy
      · exact absurd ztqqs (fun h => h.2 hvb)
      simp_all
    · left; rw [hs, ← h0, Chazelle.Geometry.lerp_zero]

/-! ## Completeness (B-M2) -/

/-- **B-M2: every missing vertex chord is found region-locally.**  A vertex chord `c` of `Q` not
in `S` is the chord at a vertex `i` of `Q` in a direction `σ` entering the interior, whose domain
part lies in a region `R` of `S` (B-M1); the vertex `i` is a vertex `j` of the host polygon of
`R`, and direction `σ` enters `int (hostPoly Q S R) = R` there. -/
theorem missing_found (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S) :
    ∃ R ∈ (interiorModel Q).regions S, ∃ i σ, i < Q.n ∧ ztdd ∧
      c = chordSet Q i σ ∧ DirInterior Q i σ ∧ c ∩ (interiorModel Q).D ⊆ R ∧
      ∃ j, j < (hostPoly Q S R).n ∧ (hostPoly Q S R).vtx j = Q.vtx i ∧
        DirInterior ztefi j σ := by
  obtain ⟨R, hR, hcR, -⟩ := full_in_region hQ hFam hc hcS
  zubhh
  have hT := Visibility.chordParam_pos hQ hi hdir
  have himg := Visibility.chordSet_eq_image hQ hi hdir
  -- the open chord lies in `R`
  have hopen : ∀ t, 0 < t → t < chordParam Q i σ → rayPt ztdli σ t ∈ R := by
    zumhl
    refine hcR ⟨?_, (Visibility.chord_spec hQ hi hdir).2.2 t h1 h2⟩
    grind
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt ztdli σ t ∈ R := by
    zuhda

  -- the vertex is in the closure of `R`
  have hcl : Q.vtx i ∈ closure R := by
    have hlim : Tendsto (fun t => rayPt (Q.vtx i) σ t) (𝓝[>] 0) (𝓝 (Q.vtx i)) := by
      have := ((Visibility.continuous_rayPt ztdli σ).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp_all
    zulzh
  obtain ⟨j, hj, hjv⟩ := vtx_mem_hostPoly hQ hFam hne hR hi hcl
  refine ⟨R, hR, i, σ, hi, hσ, rfl, hdir, hcR, j, hj, hjv, ?_⟩
  zultr
  rw [hjv, ← region_eq_intHost hQ hFam hne hR]
  omega

/-! ## No chord is emitted twice -/

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
    rw [← h, himg]; exact ⟨0, by_grind, by_simp_all⟩
  rw [himg'] at hvi
  obtain ⟨s, -, hs⟩ := hvi
  have hy : (Q.vtx i').2 = (Q.vtx i).2 := by rw [← hs]; rfl
  have hii : i = i' := by
    zuct
    exact hdh i' i hi' hi ztnr hy
  subst hii
  zubee
  -- a point of the open chord of `σ` lies on the side `σ`
  have hm : rayPt ztdli σ ztpad ∈ chordSet Q i σ' := by
    grind
  rw [himg'] at hm
  obtain ⟨u, ⟨hu0, -⟩, hu⟩ := hm
  have e := congrArg Prod.fst hu
  simp only [Visibility.rayPt_fst] at e
  zuzq
  · rfl
  · grind
  · grind
  · rfl
open Chazelle.Chain (TouchesIn)
variable {M : Model} {F : Set (Set Point)}

/-- The attachment keys of a chord. -/
def attachKeys (M : Model) (c : Set Point) : Set ℝ :=
  {x | ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- Points of a segment arbitrarily close to either end. -/
theorem near_end {a b : Point} (hab : a ≠ b) {ρ : ℝ} (hρ : 0 < ρ) (e : Point)
    (he : e = a ∨ e = b) : ∃ x ∈ Chazelle.segment a b, x ≠ e ∧ dist x e < ρ := by
  set L := |b.1 - a.1| + |b.2 - a.2| + 1 with hL
  zujzk
  set s := min (1 / 2 : ℝ) ztbabe with hs
  have hs0 : ztxx := lt_min by_norm_num by_positivity
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hsL : s * L ≤ ρ / 2 := by
    have := min_le_right (1 / 2 : ℝ) ztbabe
    calc s * L ≤ ρ / ztbtk * L := mul_le_mul_of_nonneg_right this hL0.le
      _ = ρ / 2 := by field_simp
  have hb1 : |b.1 - a.1| ≤ L := by_grind
  have hb2 : |b.2 - a.2| ≤ L := by_grind
  have hne : ∀ u : ℝ, u ≠ 0 → (u * ztbco, u * ztti) ≠ ztbxh := by
    grind
  zudsd
  · refine ⟨(e.1 + s * zttfr, e.2 + s * zttfs), ⟨s, hs0.le, by_linarith, rfl⟩, ?_, ?_⟩
    · zuq
      zuldg

    · zutq
      simp only [add_sub_cancel_left, abs_mul, abs_of_pos hs0]
      zumji
      · nlinarith [abs_nonneg zttfr]
      · nlinarith [abs_nonneg zttfs]
  · refine ⟨(a.1 + zteb * ztjum, a.2 + zteb * ztjuo),
      ⟨1 - s, by_linarith, by_linarith, rfl⟩, ?_, ?_⟩
    · zuq
      zuldg

    · zutq
      have e1 : a.1 + zteb * ztjum - e.1 = -(s * ztjum) := by_ring
      have e2 : a.2 + zteb * ztjuo - e.2 = -(s * ztjuo) := by_ring
      rw [e1, e2, abs_neg, abs_neg, abs_mul, abs_mul, abs_of_pos hs0]
      zumji
      · nlinarith [abs_nonneg ztjum]
      · nlinarith [abs_nonneg ztjuo]

/-- **A chord has at most two attachment keys** (one at each end). -/
theorem attachKeys_sub (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ k₁ k₂ : ℝ, attachKeys M c ⊆ {k₁, k₂} := by
  zuchm
  obtain ⟨pa, ta, hAa, hPa⟩ := hEa.1
  obtain ⟨pb, tb, hAb, hPb⟩ := hEb.1
  refine ⟨pa + ta, pb + tb, ?_⟩
  zugbg
  have hPc : sidePt M.W p t ∈ c := hA.2.2.2.1
  have hend : sidePt M.W p t = a ∨ sidePt M.W p t = b := by
    zvmyh at hPc
    obtain ⟨s, hs0, hs1, hs⟩ := hPc
    zunl
    · zuqy
      · exfalso
        apply hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
        zvmyz; tauto
      simp_all
    grind
  have key : ∀ (e : Point) (pe : ℕ) (te : ℝ), ztnxq → WalkEnd M.W c e →
      SideAttach M.W c pe te → sidePt M.W pe te = e → sidePt M.W p t = e → p = pe ∧ t = te := by
    intro e pe te hee hE hAe hPe hP
    zuct
    have hne' : p = pe → t ≠ te := fun h1 h2 => hne ztwo
    obtain ⟨r, hr, hdisj⟩ := hE.2 p pe t te hA.1 hA.2.1 hA.2.2.1 hAe.1 hAe.2.1 hAe.2.2.1 hne' hP hPe
    obtain ⟨r1, hr1, hs1⟩ := hA.2.2.2.2
    obtain ⟨r2, hr2, hs2⟩ := hAe.2.2.2.2
    obtain ⟨x, hx, hxe, hxd⟩ := near_end hab (lt_min hr zttss) e hee
    have hxc : ztsmy := by_grind
    have h1 := hs1 x hxc by_grind
      by_grind
    have h2 := hs2 x hxc by_grind
      by_grind
    exact hdisj x (lt_of_lt_of_le hxd ztff) h1 h2
  grind
theorem attachKeys_ncard_le (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    (attachKeys M c).ncard ≤ 2 := by
  obtain ⟨k₁, k₂, hsub⟩ := attachKeys_sub hM hc
  refine (ncard_le_ncard hsub ztcwq).trans ?_
  refine (ncard_insert_le _ _).trans ?_
  simp

/-- A union of sets of at most two elements over a finite index set. -/
theorem ncard_biUnion_le_two {E : Set ztf} (hE : E.Finite) (f : Set Point → Set ℝ)
    (hf : ∀ c ∈ E, (f c).ncard ≤ 2) : (⋃ c ∈ E, f c).ncard ≤ 2 * E.ncard := by
  induction E, hE using Set.Finite.induction_on with
  | empty => simp
  | @insert c E hcE hE ih =>
    rw [Set.biUnion_insert, ncard_insert_of_notMem hcE hE]
    zuiev
    have h1 := hf c (mem_insert c E)
    have h2 := ih fun d hd => hf d ztttg
    omega

/-- **The exit keys of a region number at most twice its degree.** -/
theorem exitKeys_ncard_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (U : Set Point) :
    (exitKeys M F U).ncard ≤ 2 * M.deg F U := by
  set E := {c | c ∈ F ∧ TouchesIn M.D c U} with hE
  have hEfin : E.Finite := hfin.subset fun c hc => hc.1
  have hsub : exitKeys M F U ⊆ ⋃ c ∈ E, attachKeys M c := by
    rintro x ⟨c, hc, ht, p, t, hA, rfl⟩
    exact mem_iUnion₂.2 ⟨c, ⟨hc, ht⟩, p, t, hA, rfl⟩
  have hfinU : (⋃ c ∈ E, attachKeys M c).Finite := hEfin.biUnion fun c hc => by
    obtain ⟨k₁, k₂, h⟩ := attachKeys_sub hM ztmko
    exact (toFinite _).subset h
  exact (ncard_le_ncard hsub hfinU).trans
    (ncard_biUnion_le_two hEfin _ fun c hc => attachKeys_ncard_le hM ztmko)

/-- The walk vertices strictly inside the arcs of a region. -/
def vtxIdx (M : Model) (F : Set ztf) (U : Set Point) : Set ℕ :=
  {k | k < M.W.n ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b k}
variable (U : Set Point)
theorem vtxKeys_eq : vtxKeys M F U = (fun k : ℕ => (k : ℝ)) '' vtxIdx M F U := by
  zumx
  constructor
  · rintro ⟨k, hk, rfl, a, b, harc, hin⟩
    exact ⟨k, ⟨hk, a, b, harc, hin⟩, rfl⟩
  · rintro ⟨k, ⟨hk, a, b, harc, hin⟩, rfl⟩
    exact ⟨k, hk, rfl, a, b, harc, hin⟩
theorem vtxKeys_ncard : (vtxKeys M F U).ncard = (vtxIdx M F U).ncard := by
  rw [vtxKeys_eq, ncard_image_of_injective _ Nat.cast_injective]

/-- **The inner vertices of distinct regions are disjoint.** -/
theorem vtxIdx_disjoint {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (hne : U ≠ U') : Disjoint (vtxIdx M F U) (vtxIdx M F U') := by
  zugua
  rintro k ⟨hk, a, b, harc, hin⟩ ⟨-, a', b', harc', hin'⟩
  have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b zthig ∧ sideInArc a' b' zthig ∧
      ε ∈ Ioo (0 : ℝ) 1 :=
    (eventually_in_arc hin).and ((eventually_in_arc hin').and
      ztxve)
  obtain ⟨t, ht1, ht2, ht3⟩ := ev.exists
  have hf := harc.2.2.2.2.2.2 k t hk ht3.1 ht3.2 ht1
  have hf' := harc'.2.2.2.2.2.2 k t hk ht3.1 ht3.2 ht2
  obtain ⟨δ, hδ1, hδ2⟩ := (hf.and hf').exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hU' with h | h
  · simp_all
  grind

/-- **The host keys of a region**: at most its inner vertices plus twice its degree. -/
theorem nk_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (U : Set Point) :
    nk M F U ≤ (vtxIdx M F U).ncard + 2 * M.deg F U := by
  zuccw
  have e : nk M F U = (hostKeys M F U).ncard := by
    unfold nk
    rw [hostKeyList_eq hS, Finset.length_sort, Set.ncard_eq_toFinset_card _ hS]
  zui
  zuiev
  rw [vtxKeys_ncard]
  have := exitKeys_ncard_le hM hF hfin U
  omega

/-- The inner vertices of any set of regions: disjoint, so their total is the size of the union. -/
theorem sum_vtxIdx_eq {T : Set ztf} (hT : T.Finite) (hTR : T ⊆ M.regions F) :
    ∑ᶠ U ∈ T, (vtxIdx M F U).ncard = (⋃ U ∈ T, vtxIdx M F U).ncard := by
  have hVfin : ∀ U, (vtxIdx M F U).Finite := fun U =>
    (Set.finite_lt_nat M.W.n).subset fun k hk => hk.1
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert U T hUT hT ih =>
    rw [finsum_mem_insert _ hUT hT, Set.biUnion_insert,
      ih (fun V hV => hTR ztttf)]
    rw [ncard_union_eq _ (hVfin U) (hT.biUnion fun V _ => hVfin V)]
    rw [Set.disjoint_iUnion₂_right]
    zulmk
    exact vtxIdx_disjoint (hTR (mem_insert U T)) (hTR ztttf)
      (fun e => hUT (e ▸ hV))

/-- **The host polygons of all regions together have at most `n + 4|F|` points.** -/
theorem sum_nk_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    ∑ᶠ U ∈ M.regions F, nk M F U ≤ M.W.n + 4 * F.ncard := by
  zudr
  have hRfin : (M.regions F).Finite := hsys.regionsIn_finite hM.preconn hM.nonempty subset_rfl
  -- the degrees
  have hdeg : ∑ᶠ U ∈ M.regions F, M.deg F U ≤ 2 * F.ncard := by
    have := Merge.potential_le hsys hM.preconn hM.nonempty subset_rfl 0
    tauto
  -- the inner vertices
  have hvtx : ∑ᶠ U ∈ M.regions F, (vtxIdx M F U).ncard ≤ M.W.n := by
    rw [sum_vtxIdx_eq hRfin subset_rfl]
    calc (⋃ U ∈ M.regions F, vtxIdx M F U).ncard ≤ ((Finset.range M.W.n : Finset ℕ) : Set ℕ).ncard :=
          ncard_le_ncard (fun k hk => by
            obtain ⟨U, -, hk⟩ := mem_iUnion₂.1 hk
            simpa using hk.1) (Finset.finite_toSet _)
      _ = M.W.n := by rw [ncard_coe_finset, Finset.card_range]
  rw [finsum_mem_eq_finite_toFinset_sum _ hRfin] at hdeg hvtx ⊢
  calc ∑ U ∈ hRfin.toFinset, nk M F U
      ≤ ∑ U ∈ hRfin.toFinset, ((vtxIdx M F U).ncard + 2 * M.deg F U) :=
        Finset.sum_le_sum fun U _ => nk_le hM hF hfin U
    _ = ∑ U ∈ hRfin.toFinset, (vtxIdx M F U).ncard + 2 * ∑ U ∈ hRfin.toFinset, M.deg F U := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M.W.n + 4 * F.ncard := by_omega
end
end DownDrv
namespace ExtG
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm offset_fst offset_snd)

/-- **Corners with positively scaled arms have the same left sector.** -/
theorem sideLeftOf_scale {a a' v b b' x : Point} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (ha : a' - v = l • ztgg) (hb : b' - v = m • ztfd) :
    sideLeftOf a' v b' x ↔ sideLeftOf a v b x := by
  zucfg
  zucpu
  have := BoxT.sideCcw_smul hm one_pos hl ztfd ztsq ztgg
  simp_all

/-- The left half-plane of a sub-segment is that of the segment. -/
theorem det_lerp_pair (A B y : Point) (τ₀ τ₁ : ℝ) :
    Chazelle.det ztrtc ztrtd y = ztkid * Chazelle.det A B y := by
  unfold Chazelle.det lerp; grind
variable (A B : Point)
/-- The arms of a sub-segment are positive multiples of the arms of the segment. -/
theorem lerp_sub_lerp (τ₀ τ₁ : ℝ) :
    lerp A B τ₁ - lerp A B τ₀ = ztkid • (B - A) := by
  apply Prod.ext <;> zundk <;> ring

/-- **Attachment transfers** between positions with the same point and the same sector. -/
theorem attach_of_sector {W W' : Polygon} {c : Set Point} {p p' : ℕ} {t t' : ℝ}
    (hpt : sidePt W' p' t' = sidePt W p t)
    (hsec : ∀ y, sideLeft W p t y → sideLeft W' p' t' y) (hp' : p' < W'.n) (ht0 : 0 ≤ t')
    (ht1 : t' < 1) (h : SideAttach W c p t) : SideAttach W' c p' t' := by
  obtain ⟨-, -, -, hmem, r, hr, hnear⟩ := h
  refine ⟨hp', ht0, ht1, hpt ▸ hmem, r, hr, fun y hy hne hd => hsec y (hnear y hy ?_ ?_)⟩
  · simp_all
  simp_all

/-- The offsets of a sub-segment. -/
theorem offset_lerp_pair (τ₀ τ₁ s δ : ℝ) :
    offset ztrtc ztrtd s δ = offset A B (τ₀ + s * ztkid) (δ * ztkid) := by
  apply Prod.ext <;> simp only [offset_fst, offset_snd, Chazelle.Geometry.lerp_fst,
    Chazelle.Geometry.lerp_snd] <;> ring

/-- **Facing transfers** when the offsets agree up to a positive scaling. -/
theorem faces_of_offset {M₁ M₂ : Model} {p₁ p₂ : ℕ} {t₁ t₂ c : ℝ} (hc : 0 < c)
    (hoff : ∀ δ, offset (M₁.wa p₁) (M₁.wb p₁) t₁ δ = offset (M₂.wa p₂) (M₂.wb p₂) t₂ (δ * c))
    {U V : Set Point} (hVU : V ⊆ U) (hV : M₂.Faces p₂ t₂ V) : M₁.Faces p₁ t₁ U := by
  have h := (Loc.tendsto_mul_const_nhdsGT hc).eventually hV
  filter_upwards [h] with δ hδ
  grind
end
end ExtG
namespace Extract
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf)
open Chazelle.Geometry (lerp)
open DownHost
open ArcT (wrapK)

/-- The hypotheses on the region. -/
structure Ctx (Q : Polygon) (S : Set ztf) (R : Set Point) : Prop where
  hQ : Q.Simple
  hFam : (interiorModel Q).ChordFamily Q S
  hne : S.Nonempty
  hR : R ∈ (interiorModel Q).regions S
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}
namespace Ctx
variable (X : Ctx Q S R)
include X
theorem walkAx : WalkAx ztd := walkAx_interiorModel X.hQ
theorem three : 3 ≤ nk ztd S R := three_le_nk X.hQ X.hFam X.hne X.hR
end Ctx

/-- The chain index of the host key `i`. -/
noncomputable def kIdx (N g i : ℕ) : ℕ := ztwtu % N
variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The chain vertices along an arc.** -/
theorem vertex_arc (X : Ctx Q S R) {i_l : ℕ} (hil : i_l < nk ztd S R) (j : ℕ) :
    (hostChain Q S R g h3).vertex ztbajh =
      hostPt (interiorModel Q).W ztbamc := by
  zujzq
  rw [hostChain_vertex, ← add_assoc]
  unfold kIdx
  rw [chain_idx ztjkk hil]

/-- The walk point of an unwrapped key in `[p, p + 1)` is at position `(p mod n, key - p)`. -/
theorem wrapK_edge {n p : ℕ} (_hn : 0 < n) (hp : p < 2 * n) {y : ℝ} (hy1 : (p : ℝ) ≤ y)
    (hy2 : y < p + 1) : wrapK n y = ((p % n : ℕ) : ℝ) + ztfvk := by
  zuiqh
  zus
  · have hpn : ztsks := by
      have : ztixm := lt_of_le_of_lt hy1 h
      simp_all
    rw [Nat.mod_eq_of_lt hpn]; ring
  · zubpo
    have hpn : n ≤ p := by
      zudxd

    zuigs
    simp_all

/-- **A piece of an arc**: chain edge `kl + j` lies on interior walk edge `p` (mod `n`). -/
theorem piece (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData ztd S R l r i_l d) {j : ℕ} (hj : j < d) :
    ∃ p : ℕ, p < 2 * (interiorModel Q).W.n ∧
      (p : ℝ) ≤ ukey ztd S R i_l j ∧
      ukey ztd S R i_l ztl ≤ p + 1 ∧
      (hostChain Q S R g h3).vertex ztbajh =
        lerp ztblj
          zttv
          ztwxh ∧
      (hostChain Q S R g h3).vertex ztbakz =
        lerp ztblj
          zttv
          ztxhk ∧
      ∀ y, ukey ztd S R i_l j ≤ y → y ≤ ukey ztd S R i_l ztl →
        hostPt (interiorModel Q).W (wrapK (interiorModel Q).W.n y) =
          lerp ztblj
            zttv
            ztfvk := by
  zukt

  zugmc
  obtain ⟨p, hp1, hp2, hp3, hq⟩ := arc_piece hM hF hfin hA hj
  have hjj := ukey_mono (U := R) hM hF hfin hA.hil ztffs by_omega
  refine ⟨p, hp3, hp1, hp2, ?_, ?_, hq⟩
  · rw [vertex_arc X hA.hil, ← wrapK_ukey hM hF hfin hA.hil by_omega]
    grind
  · rw [add_assoc, vertex_arc X hA.hil, ← wrapK_ukey hM hF hfin hA.hil by_omega]
    grind

/-- **Inner host keys are integers.** -/
theorem ukey_inner_int (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData ztd S R l r i_l d) {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    ∃ k : ℕ, ukey ztd S R i_l j = k := by
  zukt

  obtain ⟨⟨k, hk⟩, -⟩ := hA.inner j hj0 hjd
  zugmc
  rw [ukey_eq_unwrap hM hF hfin hA.hil by_omega, hk]
  unfold unwrapK
  split_ifs
  · simp
  · exact ⟨k + (interiorModel Q).W.n, by_simp⟩

/-- **At an inner host key the pieces meet at a walk vertex**: the piece before ends at the end of
its walk edge, the piece after starts at the start of the next one. -/
theorem piece_inner {i_l j p p' : ℕ} (K : ℕ)
    (hK : ukey ztd S R i_l j = K)
    (hp1 : (p : ℝ) ≤ ukey ztd S R i_l j)
    (hp2 : ukey ztd S R i_l ztl ≤ p + 1)
    (hlt : ukey ztd S R i_l j < ukey ztd S R i_l ztl)
    (hp1' : (p' : ℝ) ≤ ukey ztd S R i_l zthv)
    (hp2' : ukey ztd S R i_l ztjzb ≤ p' + 1)
    (hlt' : ukey ztd S R i_l zthv < ukey ztd S R i_l j)
    (hj0 : 0 < j) : p = K ∧ p' + 1 = K := by
  rw [Nat.sub_add_cancel hj0] at hp2'
  rw [hK] at hp1 hlt hp2' hlt'
  constructor
  · have h1 : p ≤ K := by_simp_all
    have h2 : (K : ℝ) < p + 1 := lt_of_lt_of_le hlt hp2
    have h2' : K < p + 1 := by exact_mod_cast h2
    omega
  · have h1 : (p' : ℝ) < K := lt_of_le_of_lt hp1' hlt'
    have h1' : p' < K := by_simp_all
    have h2 : K ≤ p' + 1 := by exact_mod_cast hp2'
    omega
open Filter Topology Metric
open Chazelle.Chain (sideCcw)
variable {h3 : 3 ≤ nk ztd S R}
theorem prev_mod {n a : ℕ} (hn : 0 < n) : (ztdf % n + n - 1) % n = a % n := by
  rw [← Nat.mod_add_mod a n 1]
  have hb := Nat.mod_lt a hn
  rcases Nat.lt_or_ge (a % n + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, show a % n + 1 + n - 1 = a % n + n by omega, Nat.add_mod_right,
      Nat.mod_mod]
  · have e : ztplk := by_omega
    rw [e, Nat.mod_self, zero_add, Nat.mod_eq_of_lt by_omega]
    omega

/-- The integer part of a wrapped integer key. -/
theorem wrapK_nat {n K : ℕ} (_hn : 0 < n) (hK : K < 2 * n) :
    wrapK n (K : ℝ) = ((K % n : ℕ) : ℝ) := by
  zuiqh
  zus
  · have : K < n := by_simp_all
    rw [Nat.mod_eq_of_lt this]
  · zubpo
    have : n ≤ K := by_simp_all
    rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt by_omega]
    simp_all

/-- **The corner at an inner host key**: the chain corner there is positively scaled from the
corner of the interior walk at the walk vertex. -/
theorem corner_inner (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData ztd S R l r i_l d) {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    ∃ P : ℕ, P < (interiorModel Q).W.n ∧
      (P : ℝ) = wrapK (interiorModel Q).W.n (ukey ztd S R i_l j) ∧
      (hostChain Q S R g h3).vertex ztbajh =
        (interiorModel Q).W.vtx P ∧
      ∀ y, sideLeftOf ((hostChain Q S R g h3).vertex ztbakm)
          ((hostChain Q S R g h3).vertex ztbajh)
          ((hostChain Q S R g h3).vertex ztbakz) y ↔
        sideLeft (interiorModel Q).W P 0 y := by
  zukt

  zukbs
  have hb0 := hostKeys_bounds (hk_mem (U := R) hM hF hfin hA.hil)
  have hn : ztixr := by
    have : ztkyr := lt_of_le_of_lt hb0.1 hb0.2
    simp_all
  obtain ⟨K, hK⟩ := ukey_inner_int X hA hj0 hjd
  zubhk
  obtain ⟨p', hpn', hp1', hp2', hv0', hv1', -⟩ :=
    piece (g := g) (h3 := h3) X hA (show j - 1 < d by omega)
  have hlt := ukey_mono (U := R) hM hF hfin hA.hil ztffs by_omega
  have hlt' := ukey_mono (U := R) hM hF hfin hA.hil ztglx by_omega
  obtain ⟨hpK, hp'K⟩ := piece_inner K hK hp1 hp2 hlt hp1' hp2' hlt' hj0
  have hkm1 : kIdx ztwiy g i_l + zthv + 1 =
      kIdx ztwiy g i_l + j := by_omega
  rw [hkm1, Nat.sub_add_cancel hj0] at hv1'
  zugfx
  set v := (hostChain Q S R g h3).vertex k with hvdef
  zubqf
  have hv : v = W.vtx zttuz := by
    simp_all
  have hτ₁ : 0 < ukey ztd S R i_l ztl - p := by_grind
  have hnext : (hostChain Q S R g h3).vertex zts - v =
      ztxhk • (W.vtx ztlcu - v) := by
    rw [hv1, hv0, hK, hpK, sub_self, ExtG.lerp_sub_lerp, sub_zero,
      Chazelle.Geometry.lerp_zero]
  have hvB : v = W.vtx ztlcw := by
    grind
  have hτ₀ : 0 < 1 - ztyki := by
    grind
  have hprev : (hostChain Q S R g h3).vertex ztbakm - v =
      (1 - ztyki) • (W.vtx zttvh - v) := by
    have hB : v = lerp (W.vtx zttvh) (W.vtx ztlcw) 1 := by
      rw [Chazelle.Geometry.lerp_one]; omega
    rw [hv0', hB, ExtG.lerp_sub_lerp, Chazelle.Geometry.lerp_one]
    apply Prod.ext <;> simp <;> ring
  have hPn : p % W.n < W.n := Nat.mod_lt _ hn
  have hPprev : (p % W.n + W.n - 1) % W.n = p' % W.n := by
    have hpp : p = p' + 1 := by_omega
    rw [hpp, prev_mod hn]
  refine ⟨p % W.n, hPn, ?_, hv, fun y => ?_⟩
  · have hK2 : K < 2 * W.n := by_omega
    rw [hK, wrapK_nat hn hK2, hpK]
  · rw [Chazelle.Chain.sideLeft_zero, hPprev, ← hv]
    exact ExtG.sideLeftOf_scale hτ₀ hτ₁ hprev hnext

/-- **The top vertex is not an inner vertex of an arc when the slit leaves on side `A`.** -/
theorem top_not_inner (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData ztd S R l r i_l d)
    {j : ℕ} (hj0 : 0 < j) (hjd : j < d)
    (hT : kIdx ztwiy g i_l + j = (hostChain Q S R g h3).topIdx)
    (hb : (hostChain Q S R g h3).sideBeta = true) : False := by
  zukt

  zukbs
  zueua
  obtain ⟨P, hPn, hPkey, hvP, hsec⟩ := corner_inner (g := g) (h3 := h3) X hA hj0 hjd
  zucql
  zubqf
  zugfx
  set v := C.vertex k with hvdef
  -- the slit direction is in the left sector
  have hbeta := (C.sideBeta_eq_true_iff).1 hb
  have htop : C.top = v := by
    rw [hvdef, hT]; rfl
  have hslit : sideLeftOf (C.vertex ztbakm) v ztwkj C.slitTop := by
    have e1 : C.topIdx + 1 = k + 1 := by_omega
    have e2 : C.topIdx - 1 = kIdx ztwiy g i_l + zthv := by
      omega
    zucfg
    simp_all
  have hup : ∀ ε : ℝ, 0 < ε → sideLeft W P 0 (v + ε • ztjhn) := by
    zudik
    rw [← hsec]
    unfold sideLeftOf at hslit ⊢
    rw [add_sub_cancel_left]
    have := BoxT.sideCcw_smul one_pos hε one_pos (C.vertex zts - v) ztjhn
      (C.vertex ztbakm - v)
    simp_all
  -- the vertex position is inside the arc
  have hkey : (P : ℝ) + 0 = hk ztd S R ztwsr := by
    rw [add_zero, hPkey, wrapK_ukey hM hF hfin hA.hil by_omega]
  have hin := (hA.inner j hj0 hjd).2
  rw [← hkey] at hin
  have hncut : ¬ (interiorModel Q).IsCut S ztnns := harc.2.2.2.2.2.1 _ hin
  have hfU : ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces P (0 + s * ztsqq) R := by
    filter_upwards [cyc_open hin, Ioo_mem_nhdsGT ztja] with s h1 hs1
    rw [zero_add, sub_zero, mul_one]
    zvncl at h1
    exact harc.2.2.2.2.2.2 P s hPn hs1.1 hs1.2 h1
  obtain ⟨r₀, hr₀, hnear⟩ := Loc.near_sub_region X.hQ hF hfin hPn le_rfl zero_lt_one hncut X.hR hfU
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hPn le_rfl zero_lt_one
  have hvP' : sidePt W P 0 = v := by rw [Chazelle.Chain.sidePt_zero, ← hvP]
  -- a point just above the top in `R`
  have hrad : v.2 < C.radius := by rw [← htop]; exact C.top_snd_lt_radius
  set ε := min r₀ rC / (2 * zthaa) with hε
  have hε0 : ztbad := div_pos (lt_min hr₀ hrC) by_linarith
  set y := v + ε • ztjhn with hy
  have hy2 : y.2 = v.2 + ε * zthaa := by
    rfl
  have hy1 : y.1 = v.1 := by
    show (v + ε • ztjhn).1 = _
    zughd
    rw [show C.slitTop.1 = C.top.1 from rfl, htop]
    ring
  have hpos : 0 < ε * zthaa := mul_pos hε0 by_linarith
  have hdist : dist y v = min r₀ rC / 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy1, hy2, sub_self, abs_zero,
      show v.2 + ε * zthaa - v.2 = ε * zthaa by ring,
      abs_of_pos hpos, max_eq_right hpos.le, hε]
    have : C.radius - v.2 ≠ 0 := by_linarith
    field_simp
  have hmin := lt_min hr₀ hrC
  have hyb₀ : y ∈ ball ztrwy r₀ := by
    zunym; have := min_le_left r₀ rC; linarith
  have hybC : y ∈ ball ztrwy rC := by
    zunym; have := min_le_right r₀ rC; linarith
  have hyD : ztpqn := by
    by_contra hyD
    exact hclean y hybC ztdlx zttoq
  have hyR := hnear y hyb₀ hyD
  have := region_below_top (g := g) (h3 := h3) X.hQ X.hFam X.hne X.hR y hyR
  grind

/-- **No split of side `A` inside an arc.** -/
theorem no_split (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData ztd S R l r i_l d)
    {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    kIdx ztwiy g i_l + j ≠
      TourA.sA ztog (hostChain Q S R g h3).sideBeta := by
  zudku
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    ztech hA.gaps
  zukdo
  have hwrap' : ztbaoj := by
    tauto
  zumcp
  unfold TourA.sA
  zudjk
  · zubqb
    zuiea
    · exact fun hT => top_not_inner X harc hA hj0 hjd hT hb
    · omega
    · omega
  omega

/-- **Side `A` along an arc is contiguous.** -/
theorem tourA_arc (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData ztd S R l r i_l d)
    {j : ℕ} (hj : j < d) :
    TourA.tourA ztog (hostChain Q S R g h3).sideBeta
        ztbajh =
      TourA.tourA ztog (hostChain Q S R g h3).sideBeta
        ztbaqf + j := by
  zudku
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    ztech hA.gaps
  zukdo
  have hwrap' : ztbaoj := by
    tauto
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show kIdx ztwiy g i_l + ztl =
      kIdx ztwiy g i_l + j + 1 by ring,
      TourA.tourA_succ (C := C) (β := C.sideBeta) (k := kIdx ztwiy g i_l + j)
        by_omega
        (show kIdx ztwiy g i_l + j + 1 ≠ _ from
          no_split (h3 := h3) X hg hgc harc hA (j := j + 1) by_omega hj),
      ih by_omega]
    ring
open Chazelle.Jordan (offset)
open Chazelle.Visibility (hseg)
open ArcT (NonVtx)
def kept (R : Set Point) (F₁ : Set ztf) : Set ztf :=
  {c | c ∈ F₁ ∧ (c ∩ R).Nonempty}

/-- The chain walk key of the start of the side-`A` run of an arc. -/
noncomputable def cStart (Q : Polygon) (S : Set ztf) (R : Set Point) (g : ℕ)
    (h3 : 3 ≤ nk ztd S R) (i_l : ℕ) : ℕ :=
  TourA.tourA ztog (hostChain Q S R g h3).sideBeta
    ztbaqf + 6

/-- **The key map of an arc.** -/
noncomputable def kmap (Q : Polygon) (S : Set ztf) (R : Set Point) (g : ℕ)
    (h3 : 3 ≤ nk ztd S R) (i_l d : ℕ) : ℝ → ℝ :=
  ArcT.brk ztwpw d (cStart Q S R g h3 i_l : ℝ)
theorem brkInc (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData ztd S R l r i_l d) :
    ArcT.BrkInc ztwpw d := fun j hj =>
  ukey_mono (U := R) X.walkAx X.hFam.2.1 X.hFam.1 hA.hil ztffs
    (by have := hA.hdN; omega)

/-- **The keys just after a position inside an arc face the region.** -/
theorem faces_after {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r ztk) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces p ztwlx R := by
  have h1 := (Loc.tendsto_mul_const_nhdsGT ztmns).eventually
    ztjtb
  zucll
  zumet
  refine harc.2.2.2.2.2.2 p _ hp by_nlinarith (by nlinarith [hs1.2]) ?_
  grind

/-- A point of a horizontal segment near a given point of it. -/
theorem exists_near_mem {y₀ a b : ℝ} (hab : a < b) {P : Point} (hP : P ∈ hseg y₀ a b) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ y ∈ hseg y₀ a b, y ≠ P ∧ dist y P < ρ := by
  obtain ⟨hP2, hPa, hPb⟩ := hP
  rcases hPb.lt_or_eq with hPb | hPb
  · set ε := min (b - P.1) ρ / 2 with hεd
    zucmx
    have hε1 : ε < b - P.1 := by
      grind
    have hε2 : ε < ρ := by
      grind
    refine ⟨(P.1 + ε, y₀), ztbci, fun e => ?_, ?_⟩
    · grind
    · zutq
      grind
  · have hPa' : a < P.1 := by_linarith
    set ε := min (P.1 - a) ρ / 2 with hεd
    zucmx
    have hε1 : ε < P.1 - a := by
      grind
    have hε2 : ε < ρ := by
      grind
    refine ⟨(P.1 - ε, y₀), ztbci, fun e => ?_, ?_⟩
    · grind
    · zutq
      grind

/-- **A chord attached at a position inside an arc meets the region.** -/
theorem kept_of_attach (X : Ctx Q S R) {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r)
    {c : Set Point} (hc : ∃ y₀ a b : ℝ, a < b ∧ c = hseg y₀ a b) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r ztk) (hA₂ : SideAttach (interiorModel Q).W c p t) :
    (c ∩ R).Nonempty := by
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  zueua
  have hncut : ¬ (interiorModel Q).IsCut S _ := harc.2.2.2.2.2.1 _ hin
  obtain ⟨r₀, hr₀, hnear⟩ := Loc.near_sub_region X.hQ hF hfin hp ht0 ht1 hncut X.hR
    (faces_after harc hp ht0 ht1 hin)
  zuebi
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA₂
  zuejm
  set ρ := min rA (min r₀ rC)
  have hρ : 0 < ρ := by_grind
  obtain ⟨y, hyc, hne, hyd⟩ := exists_near_mem hab hmem hρ
  have hyA : dist y _ < rA :=
    lt_of_lt_of_le hyd by_grind
  have hy₀ : y ∈ ball _ r₀ :=
    lt_of_lt_of_le hyd by_grind
  have hyC : y ∈ ball _ rC :=
    lt_of_lt_of_le hyd by_grind
  have hyl := hsec y hyc hne hyA
  have hyD : ztpqn := by
    by_contra hyD
    exact hclean y hyC ztdlx hyl
  exact ⟨y, hyc, by_simp_all⟩

/-- **The positions of an arc key**: its piece `j`, its interior walk edge `p` (mod `n`), its
chain walk edge and parameter. -/
theorem pos_data (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData ztd S R l r i_l d)
    {x : ℝ} (hx : x ∈ Ioo ztxrh ztxri) :
    ∃ j p : ℕ, j < d ∧ p < 2 * (interiorModel Q).W.n ∧
      (p : ℝ) ≤ ukey ztd S R i_l j ∧ ukey ztd S R i_l j ≤ x ∧
      x < ukey ztd S R i_l ztl ∧
      ukey ztd S R i_l ztl ≤ p + 1 ∧
      ⌊kmap Q S R g h3 i_l d x⌋₊ = TourA.tourA ztog
        (hostChain Q S R g h3).sideBeta ztbajh + 6 ∧
      kmap Q S R g h3 i_l d x - ⌊kmap Q S R g h3 i_l d x⌋₊ =
        (x - ukey ztd S R i_l j) /
          ztxrj ∧
      (hostChain Q S R g h3).vertex ztbajh =
        lerp ztblj
          zttv
          ztwxh ∧
      (hostChain Q S R g h3).vertex ztbakz =
        lerp ztblj
          zttv
          ztxhk ∧
      wrapK (interiorModel Q).W.n x = (((p % (interiorModel Q).W.n : ℕ)) : ℝ) + (x - p) := by
  zukcq
  zumdh
  obtain ⟨hjd, hj1, hj2⟩ := ArcT.seg_spec hinc hd1 hx.1.le hx.2
  zubhk
  have hb0 := hostKeys_bounds (hk_mem X.walkAx X.hFam.2.1 X.hFam.1 hA.hil)
  have hwn : ztixr := by
    omega
  have hlt : ukey ztd S R i_l ztbamr <
      ukey ztd S R i_l ztbaop := by
    linarith
  have hκ : kmap Q S R g h3 i_l d x = (cStart Q S R g h3 i_l : ℝ) +
      (ArcT.seg _ d x : ℕ) +
      (x - ukey _ S R i_l _) /
        (ukey _ S R i_l _ -
          ukey _ S R i_l _) := rfl
  have hf0 : 0 ≤ (x - ukey _ S R i_l ztrim) /
      (ukey _ S R i_l _ -
        ukey _ S R i_l ztrim) :=
    div_nonneg by_linarith by_linarith
  have hf1 : (x - ukey ztd S R i_l ztbamr) /
      (ukey ztd S R i_l ztbaop -
        ukey ztd S R i_l ztbamr) < 1 := by
    zubie
  have hfl : ⌊kmap Q S R g h3 i_l d x⌋₊ =
      cStart Q S R g h3 i_l + ArcT.seg ztwpw d x := by
    rw [hκ, Nat.floor_eq_iff by_positivity]
    simp_all
  have htour := tourA_arc (h3 := h3) X hg hgc harc hA hjd
  refine ⟨ArcT.seg _ d x, p, hjd, hpn, hp1, hj1, hj2, hp2, ?_, ?_,
    hv0, hv1, wrapK_edge hwn hpn by_grind by_grind⟩
  · rw [hfl, htour]; unfold cStart; ring
  simp_all

/-- **The key correspondence of an arc** (`ArcT.ArcCorr`). -/
theorem arcCorr (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData ztd S R l r i_l d)
    {F₁ : Set ztf} (hF₁ : F₁ ⊆ (chainModel ztog).Adm)
    {U V : Set Point} (hVU : V ⊆ U) :
    ArcT.ArcCorr (chainModel ztog) ztd F₁ ztenz U V
      ztxrh ztxri
      ztmlz := by
  zukt

  have hdN : d < nk _ S R := hA.hdN
  zumdh
  zukcq
  zuerd
  have hlb :=
    hA.hl ▸ hostKeys_bounds (hk_mem hM hF hfin hA.hil)
  have hrb :=
    hA.hr ▸ hostKeys_bounds (hk_mem hM hF hfin ztcv)
  have hwn : ztixr := by
    have  := lt_of_le_of_lt hlb.1 hlb.2
    simp_all
  have hP := hostPts_simple X.hQ X.hFam X.hne X.hR
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    ztech hA.gaps
  have hwrap' : kIdx ztwiy g i_l + d ≤ (hostChain Q S R g h3).m := by
    tauto
  have hbot : kmap Q S R g h3 i_l d _ =
      (cStart Q S R g h3 i_l : ℝ) := ArcT.brk_bot hinc hd1
  have htop : kmap Q S R g h3 i_l d _ =
      (cStart Q S R g h3 i_l : ℝ) + d := ArcT.brk_top hinc hd1
  have hmono : StrictMonoOn ztmlz
      _ :=
    ArcT.brk_strictMonoOn hinc hd1
  have hcs : cStart Q S R g h3 i_l + d ≤ 2 * (hostChain Q S R g h3).m + 6 := by
    have h1 := tourA_arc (h3 := h3) X hg hgc harc hA ztmnv
    have h2 := TourA.tourA_lt (C := hostChain Q S R g h3) (β := (hostChain Q S R g h3).sideBeta)
      (kIdx ztwiy g i_l + ztku)
    unfold cStart; omega
  have hn₁ : (chainModel _).W.n = 2 * (hostChain Q S R g h3).m + 7 :=
    Chain.sideWalk_n _ _
  have hlr' : unwrapK (interiorModel Q).W.n l l < unwrapK (interiorModel Q).W.n l r := by
    rw [unwrapK_self, ← hA.hud, ← hl0]
    exact ukey_mono hM hF hfin hA.hil hA.hd0 hdN
  -- the interior position of a key of the arc lies inside the arc
  have hinarc : ∀ x ∈ Ioo ztxrh ztxri,
      sideInArc l r (wrapK (interiorModel Q).W.n x) := by
    zuh
    rw [hl0, hA.hud] at hx
    have hx0 := le_trans hlb.1 hx.1.le
    have hxl := lt_trans hx.2 (unwrapK_bounds hlb hrb).2
    zufhh

    have hwl := ArcT.wrapK_lt by_simp_all hx0 hx2
    rw [cyc_unwrap hlb hlb hrb by_simp_all hlr', unwrapK_self,
      unwrapK_wrapK hlb.1 by_simp_all hx.1.le hxl]
    zufsg
  refine ⟨?_, ?_, ?_, hmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · rw [hA.hud, hl0]; exact (unwrapK_bounds hlb hrb).2.le
  · -- range
    zuh
    have h1 := hmono.monotoneOn ⟨le_rfl, le_trans hx.1 hx.2⟩ hx hx.1
    have h2 := hmono.monotoneOn hx ⟨le_trans hx.1 hx.2, le_rfl⟩ hx.2
    zufnk

    refine ⟨by_grind, lt_of_le_of_lt h2 ?_⟩
    zumns
    zuhuk
  · -- onto
    zujbw
    zufnk

    exact ArcT.brk_onto hinc hd1 h1 h2
  · -- vertices to vertices
    zukjy
    obtain ⟨j, hj, rfl⟩ := (ArcT.brk_int_iff hinc hd1 hx.1.le
      hx.2).1 ⟨k, hk⟩
    zuzo
    · simp_all
    · obtain ⟨K, hK⟩ := ukey_inner_int X hA h0 hj
      tauto
  · -- vertex keys to vertex keys
    zudqi

    obtain ⟨K, hK⟩ := hnv
    zumfa
    rw [hl0, hA.hud] at hx'
    have hx0 : ztrzu := by_simp_all
    have hxl := lt_trans hx'.2 (unwrapK_bounds hlb hrb).2
    zufhh

    have hwl := ArcT.wrapK_lt (show (0 : ℝ) < (interiorModel Q).W.n by exact_mod_cast hwn) hx0 hx2
    have hK2 : K < 2 * (interiorModel Q).W.n := by
      have : (K : ℝ) < ((2 * (interiorModel Q).W.n : ℕ) : ℝ) := by_grind
      zufc
    obtain ⟨j, hj0, hjd, hjx⟩ := hA.vtx _ hw0 hwl (hinarc x hx)
      ⟨K % (interiorModel Q).W.n, by rw [hK, wrapK_nat hwn hK2]⟩
    have hu : ukey ztd S R i_l j = x := by
      rw [ukey_eq_unwrap hM hF hfin hA.hil by_omega, hA.hl, hjx,
        unwrapK_wrapK hlb.1 by_grind hx'.1.le hxl]
    obtain ⟨k, hk⟩ := (ArcT.brk_int_iff hinc hd1 hx.1.le
      hx.2).2 ⟨j, hjd, hu.symm⟩
    exact hnv' k hk
  · -- cuts
    zudta
    obtain ⟨j, p, hjd, hpn, hp1, hj1, hj2, hp2, hfl, hfr, hv0, hv1, hwr⟩ :=
      pos_data (h3 := h3) X hg hgc harc hA hx
    zubqf
    zucql
    set s := (x - ukey _ S R i_l j) /
      (ukey _ S R i_l _ - ukey _ S R i_l j) with hs
    have hjj : ztxtk := by
      linarith
    have hs0 : 0 ≤ s := div_nonneg by_linarith by_linarith
    have hs1 : ztdrm := by rw [hs, div_lt_one by_linarith]; linarith
    zukda
    -- the chain position
    have hkey : ((p₁ : ℕ) : ℝ) + t₁ =
        ((TourA.tourA C C.sideBeta ztbajh + 6 : ℕ) : ℝ) + s := by
      rw [← he, ← hfl, ← hfr]; ring
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA₁.2.1 hA₁.2.2.1 hs0 hs1 hkey
    -- the interior position
    set p₂ := p % W.n with hp₂
    zuioi
    have hp₂n : p₂ < W.n := Nat.mod_lt _ hwn
    zuehf

    have hpar : t₂ = ztwxh +
        s * ztxrj := by
      have hne : ztiec :=
        sub_ne_zero.2 hjj.ne'
      grind
    -- the points agree
    have hpt : sidePt W p₂ t₂ = sidePt ztcs
        (TourA.tourA C C.sideBeta ztbajh + 6) s := by
      rw [TourA.sidePt_tourA hkm, hv0, hv1, lerp_lerp]
      zucky
      grind
    -- the sectors agree
    have hsec : ∀ y, sideLeft ztcs
        (TourA.tourA C C.sideBeta ztbajh + 6) s y →
        sideLeft W p₂ t₂ y := by
      zusy
      rcases hs0.lt_or_eq with hs0' | hs0'
      · -- inside a piece
        have ht₂0' : 0 < t₂ := by_grind
        rw [TourA.sideLeft_tourA_edge hP hkm ⟨hs0', hs1⟩, hv0, hv1, ExtG.det_lerp_pair] at hy
        rw [Chazelle.Chain.sideLeft_edge (hM.nd p₂ hp₂n) ⟨ht₂0', ht₂1⟩]
        have hτ : 0 < ukey ztd S R i_l ztl - p -
            ztwxh := by_linarith
        exact pos_of_mul_pos_right hy hτ.le
      · -- at an inner host key
        have hxj : x = ukey ztd S R i_l j := by
          grind
        have hj0 : ztpht := by
          zuirx
          zudgu
          simp_all
        obtain ⟨P, hPn, hPkey, hvP, hcorner⟩ := corner_inner X hA hj0 hjd
        have hP₂ : p₂ = P ∧ t₂ = 0 := by
          have e : ((p₂ : ℕ) : ℝ) + t₂ = ((P : ℕ) : ℝ) + 0 := by
            grind
          exact Chazelle.Chain.sideKey_inj ht₂0 ht₂1 le_rfl zero_lt_one e
        rw [← hs0'] at hy
        rw [TourA.sideLeft_tourA_vtx by_omega hkm
          (no_split X hg hgc harc hA hj0 hjd)] at hy
        rw [hP₂.1, hP₂.2, ← hcorner]
        rwa [show kIdx _ g i_l + j - 1 =
          kIdx ztwiy g i_l + zthv by omega] at hy
    have hA₂ :=
      ExtG.attach_of_sector hpt hsec hp₂n ht₂0 ht₂1 hA₁
    -- the chord meets `R`
    have hcsh : ∃ y₀ a b : ℝ, a < b ∧ c = hseg y₀ a b := by
      obtain ⟨y₀, a, b, hh, -, e⟩ := hF₁ hc
      exact ⟨y₀, a, b, hh.lt, e⟩
    have hin2 : sideInArc l r ztoeu := by rw [← hwr]; exact hinarc x hx
    have hmeet := kept_of_attach X harc hcsh hp₂n ht₂0 ht₂1 hin2 hA₂
    exact ⟨c, Or.inr ⟨hc, hmeet⟩, p₂, t₂, hA₂, hwr⟩
  · -- faces
    intro x hx hv hfa
    obtain ⟨j, p, hjd, hpn, hp1, hj1, hj2, hp2, hfl, hfr, hv0, hv1, hwr⟩ :=
      pos_data X hg hgc harc hA hx
    zubqf
    zucql
    have hjj : ztxtk := by
      linarith
    zukda
    -- a non-vertex key is inside a piece
    have hxj : ukey ztd S R i_l j < x := by
      rcases hj1.lt_or_eq with h | h
      · zubh
      · exfalso
        zuzo
        · zvmzn at h; simp_all
        · obtain ⟨K, hK⟩ := ukey_inner_int X hA h0 hjd
          exact hv K by_grind
    zuioi
    zuehf

    have hfl2 : ⌊wrapK W.n x⌋₊ = p % W.n := by rw [hwr]; exact floor_add ht₂0 ht₂1
    have hfr2 : wrapK W.n x - ⌊wrapK W.n x⌋₊ = t₂ := by_grind
    rw [hfr2, hfl2] at hfa
    zukuf
    refine ExtG.faces_of_offset (c := ukey _ S R i_l _ - p -
      (ukey _ S R i_l j - p)) by_linarith (fun δ => ?_) hVU hfa
    show Chazelle.Jordan.offset ((C.sideWalk C.sideBeta).vtx
        _)
      ((C.sideWalk C.sideBeta).vtx
        ((TourA.tourA C C.sideBeta _ + 6 + 1) %
          (C.sideWalk C.sideBeta).n)) _ δ = _
    rw [TourA.vtx_tourA hkm, TourA.vtx_tourA_succ hkm, hv0, hv1, ExtG.offset_lerp_pair]
    zucr
    have hne : ztiec :=
      sub_ne_zero.2 hjj.ne'
    grind
  · -- counted
    zumhq
    obtain ⟨j, p, hjd, -, -, -, -, -, hfl, -⟩ := pos_data X hg hgc harc hA hx
    zumng
    exact TourA.counted_tourA _
open Chazelle.Chain (TouchesIn freeIn regionsIn)
theorem cyc_unwrap' {n l a b y : ℝ} (hl : 0 ≤ l ∧ l < n) (ha : 0 ≤ a ∧ a < n)
    (hb : 0 ≤ b ∧ b < n) (hy : 0 ≤ y ∧ y < n) (hab : unwrapK n l b < unwrapK n l a) :
    sideInArc a b y ↔ unwrapK n l y < unwrapK n l b ∨ unwrapK n l a < unwrapK n l y := by
  unfold unwrapK at *
  zuiq

/-- **An interval inside an arc, unwrapped.**  If `(a, b)` and `(l, r)` share a key `x₀` and
`(a, b)` contains neither `l` nor `r`, then, unwrapped from `l`, `(a, b)` is an increasing
sub-interval of `(l, r)`. -/
theorem unwrap_sub {n l r a b x₀ : ℝ} (hl : 0 ≤ l ∧ l < n) (hr : 0 ≤ r ∧ r < n)
    (ha : 0 ≤ a ∧ a < n) (hb : 0 ≤ b ∧ b < n) (hx : 0 ≤ x₀ ∧ x₀ < n)
    (hlr : l < unwrapK n l r) (hab : a ≠ b) (hxab : sideInArc a b x₀)
    (hxlr : sideInArc l r x₀) (hla : ¬ sideInArc a b l) (hra : ¬ sideInArc a b r) :
    unwrapK n l a < unwrapK n l b ∧ unwrapK n l b ≤ unwrapK n l r := by
  have e2 := (cyc_unwrap hl hl hr hx ztcmh).1 hxlr
  rw [unwrapK_self] at e2
  have hbx := unwrapK_bounds hl hx
  have hbb := unwrapK_bounds hl hb
  have hba := unwrapK_bounds hl ha
  have hne : unwrapK n l a ≠ unwrapK n l b := fun e => hab (by
    rw [← wrapK_unwrapK (l := l) ha, ← wrapK_unwrapK (l := l) hb, e])
  zuto
  · have e1 := (cyc_unwrap hl ha hb hx h).1 hxab
    zulov
    zudxc
    push Not at h'
    exact hra ((cyc_unwrap hl ha hb hr h).2 ⟨by_grind, h'⟩)
  · exfalso
    have e1 := (cyc_unwrap' hl ha hb hx h).1 hxab
    have h1 : ¬ (unwrapK n l l < unwrapK n l b ∨ unwrapK n l a < unwrapK n l l) := fun h' =>
      hla ((cyc_unwrap' hl ha hb hl h).2 h')
    have h2 : ¬ (unwrapK n l r < unwrapK n l b ∨ unwrapK n l a < unwrapK n l r) := fun h' =>
      hra ((cyc_unwrap' hl ha hb hr h).2 h')
    rw [unwrapK_self] at h1
    grind

/-- A cut of `S` is a cut of any larger family. -/
theorem isCut_mono {M : Model} {F G : Set ztf} (hFG : F ⊆ G) {x : ℝ} (h : M.IsCut F x) :
    M.IsCut G x := by
  obtain ⟨c, hc, p, t, hA, e⟩ := h
  exact ⟨c, hFG hc, p, t, hA, e⟩

/-- **(X2) for one arc.** -/
theorem arcWt_kept (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {F₁ : Set ztf}
    (hF₁ : F₁ ⊆ (chainModel ztog).Adm) (hfin₁ : F₁.Finite)
    {U : Set Point} (hU : U ∈ (chainModel ztog).regions F₁)
    {V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) {a b : ℝ}
    (harc : (interiorModel Q).IsArc ztenz V a b) :
    (interiorModel Q).arcWt a b ≤ (chainModel ztog).weight F₁ U := by
  zukt

  have hTne : (S ∪ kept R F₁).Nonempty := X.hne.mono subset_union_left
  obtain ⟨p, hp, t, ht, hxab, hncT, hfV⟩ := WalkAx.exists_pos_in_arc hTne harc
  have hncS : ¬ (interiorModel Q).IsCut S ztk := fun h => hncT (isCut_mono subset_union_left h)
  obtain ⟨Y, hY, l, r, harcY, hxlr⟩ := hM.arc_around hF hfin X.hne hncS
  have hfR : (interiorModel Q).Faces p t R := hfV.mono (fun δ h => hVR h)
  have hfY : (interiorModel Q).Faces p t Y := harcY.2.2.2.2.2.2 p t hp ht.1 ht.2 hxlr
  have hYR : Y = R := WalkAx.faces_unique hY X.hR hfY hfR
  rw [hYR] at harcY
  obtain ⟨hcl, hcr, -⟩ := WalkAx.arc_cuts X.hne harcY
  have hla : ztsob := fun h =>
    harc.2.2.2.2.2.1 l h (isCut_mono subset_union_left hcl)
  have hra : ¬ sideInArc a b r := fun h =>
    harc.2.2.2.2.2.1 r h (isCut_mono subset_union_left hcr)
  obtain ⟨-, -, hab⟩ := WalkAx.arc_cuts hTne harc
  have ha : 0 ≤ a ∧ a < (interiorModel Q).W.n := ⟨harc.1, harc.2.1⟩
  have hb : 0 ≤ b ∧ b < (interiorModel Q).W.n := ⟨harc.2.2.1, harc.2.2.2.1⟩
  have hlb : 0 ≤ l ∧ l < (interiorModel Q).W.n := ⟨harcY.1, harcY.2.1⟩
  have hrb : 0 ≤ r ∧ r < (interiorModel Q).W.n := ⟨harcY.2.2.1, harcY.2.2.2.1⟩
  have hxb : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < (interiorModel Q).W.n := by
    refine ztgnz
    have : ((p + 1 : ℕ) : ℝ) ≤ ((interiorModel Q).W.n : ℝ) := by exact_mod_cast hp
    grind
  have hn : ztkyr := lt_of_le_of_lt hlb.1 hlb.2
  obtain ⟨i_l, d, hA⟩ := arc_keys hM hF hfin X.hne X.hR harcY
  zuerd
  have hlrU : l < unwrapK (interiorModel Q).W.n l r := by
    rw [← hA.hud, ← hl0]
    exact ukey_mono hM hF hfin hA.hil hA.hd0 hA.hdN
  obtain ⟨h1, h2⟩ := unwrap_sub hlb hrb ha hb hxb hlrU hab hxab hxlr hla hra
  have hP : (hostChain Q S R g h3).P.Simple := hostPts_simple X.hQ X.hFam X.hne X.hR
  have corr := arcCorr X hg hgc harcY hA hF₁ hVU
  have hrU := (unwrapK_bounds hlb hrb).2
  refine ArcT.arcWt_le ztwhs hF₁ hfin₁ hU corr
    (aa := unwrapK (interiorModel Q).W.n l a) (bb := unwrapK (interiorModel Q).W.n l b)
    ?_ h1 ?_ ?_ ?_ harc.2.2.2.2.2.1 harc.2.2.2.2.2.2
  · rw [hl0]; exact (unwrapK_bounds hlb ha).1
  · rw [hA.hud]; exact h2
  · intro x hx0 hxn hx
    exact ⟨unwrapK (interiorModel Q).W.n l x, (cyc_unwrap hlb ha hb ztuiq h1).1 hx,
      wrapK_unwrapK ztuiq⟩
  · intro xx hxx
    have hlo : l ≤ xx := le_trans (unwrapK_bounds hlb ha).1 hxx.1.le
    have hhi : xx < l + (interiorModel Q).W.n := by_grind
    have hxx0 : 0 ≤ xx := le_trans hlb.1 hlo
    have hxx2 : xx < 2 * ((interiorModel Q).W.n : ℝ) := by_grind
    have hy : 0 ≤ wrapK (interiorModel Q).W.n xx ∧
        wrapK (interiorModel Q).W.n xx < (interiorModel Q).W.n :=
      ⟨ArcT.wrapK_nonneg hxx0 hxx2, ArcT.wrapK_lt hn hxx0 hxx2⟩
    have e := unwrapK_wrapK hlb.1 hn hlo hhi
    refine (cyc_unwrap hlb ha hb hy h1).2 ?_
    simp_all

/-- **(X2) The weight transfer.** -/
theorem weight_kept (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {F₁ : Set ztf}
    (hF₁ : F₁ ⊆ (chainModel ztog).Adm) (hfin₁ : F₁.Finite)
    {U : Set Point} (hU : U ∈ (chainModel ztog).regions F₁)
    {V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) :
    (interiorModel Q).weight ztenz V ≤
      (chainModel ztog).weight F₁ U := by
  zudwr

  exact arcWt_kept X hg hgc hF₁ hfin₁ hU hVR hVU hab

/-- **(X1, localization)** The kept chords are admissible and meet the domain only in `R`. -/
theorem kept_local (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {F₁ : Set ztf}
    (hF₁ : F₁ ⊆ (chainModel ztog).Adm) {c : Set Point}
    (hc : c ∈ kept R F₁) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R :=
  kept_adm X.hQ X.hFam X.hne X.hR hg hgc (hF₁ hc.1) hc.2

/-- The walk vertices of the interior walk are vertices of `Q`. -/
theorem interiorWalk_vtx {k : ℕ} (hk : k < (interiorWalk Q).n) :
    ∃ h, h < Q.n ∧ (interiorWalk Q).vtx k = Q.vtx h := by
  have hWn : ztcfx := by
    zufdi
    · rfl
    · zuhcp
  have hk' : ztsjy := hWn ▸ hk
  zugiq

  · grind
  · exact ⟨Q.n - 1 - k, by_omega, FactsInterior.rev_vtx Q k hk'⟩

/-- **Host points lie at vertex heights of `Q`.** -/
theorem host_height (X : Ctx Q S R) {i : ℕ} (hi : i < nk ztd S R) :
    ∃ h, h < Q.n ∧ (hostPt (interiorModel Q).W ztwln).2 = (Q.vtx h).2 := by
  have hM := X.walkAx
  rcases hk_mem hM X.hFam.2.1 X.hFam.1 hi with ⟨c, hc, -, p, t, hA, e⟩ | ⟨k, hk, e, -⟩
  · rw [e, hostPt_eq _ hA.2.1 hA.2.2.1]
    obtain ⟨h, hh, a, b, rfl⟩ := X.hFam.2.2 c hc
    exact ⟨h, hh, hA.2.2.2.1.1⟩
  · rw [e, show ((k : ℕ) : ℝ) = (k : ℝ) + 0 by ring, hostPt_eq _ le_rfl one_pos,
      Chazelle.Chain.sidePt_zero]
    obtain ⟨h, hh, e'⟩ := interiorWalk_vtx (Q := Q) hk
    tauto

/-- **Every region of the extended family inside `R` lies in a region of `F₁`.** -/
theorem exists_chain_region (X : Ctx Q S R) {F₁ : Set ztf} {V : Set Point}
    (hV : V ∈ (interiorModel Q).regions ztenz) (hVR : V ⊆ R) :
    ∃ U ∈ (chainModel ztog).regions F₁, V ⊆ U := by
  zuov
  zugme
  have hfree : V ⊆ freeIn (hostChain Q S R g h3).dom F₁ := by
    zugh
    refine ⟨hdom (hVR hz), fun ⟨c, hc, hzc⟩ => ?_⟩
    exact (Chazelle.Chain.regionsIn_subset hV hz).2 ⟨c, Or.inr ⟨hc, z, hzc, hVR hz⟩, hzc⟩
  exact ⟨_, ztpgd,
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hfree⟩

/-- **(X3) The degree bound.** -/
theorem deg_kept (X : Ctx Q S R) (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {F₁ : Set ztf}
    (hF₁ : F₁ ⊆ (chainModel ztog).Adm) (hfin₁ : F₁.Finite)
    {U V : Set Point} (hVR : V ⊆ R) (hVU : V ⊆ U) :
    (interiorModel Q).deg ztenz V ≤
      (chainModel ztog).deg F₁ U + (interiorModel Q).deg S R := by
  zuhqm
  zugme
  have hsub : {c | c ∈ S ∪ kept R F₁ ∧ TouchesIn (interiorModel Q).D c V} ⊆
      {c | c ∈ F₁ ∧ TouchesIn (chainModel ztog).D c U} ∪
        {c | c ∈ S ∧ TouchesIn (interiorModel Q).D c R} := by
    rintro c ⟨hc | hc, z, hz, hzV⟩
    · exact Or.inr ⟨hc, z, hz, closure_mono hVR hzV⟩
    · have hzR := (kept_local X hg hgc hF₁ hc).2 hz
      exact Or.inl ⟨hc.1, z, ⟨hz.1, hdom hzR⟩, closure_mono hVU hzV⟩
  refine le_trans (Set.ncard_le_ncard hsub ?_) (Set.ncard_union_le _ _)
  exact (hfin₁.subset fun c hc => hc.1).union (X.hFam.1.subset fun c hc => hc.1)
end
end Extract
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
      hostPt W a = sidePt W p zteoo ∧ hostPt W b = sidePt W p t'' := by
  zuhoj
  have hp : (p : ℝ) ≤ a := Nat.floor_le ha0
  have hp1 : a < p + 1 := Nat.lt_floor_add_one a
  have hpn : p < W.n := by
    have : ztphc := lt_of_le_of_lt hp han
    simp_all
  zujyv
  refine ⟨p, hpn, ?_⟩
  zufrd
  · have hbp : ztsdq := by
      zubq

      have hk : zteie := by
        have : ztcrc := by_grind
        zufc
      zulvv
      zuxb
    refine ⟨b - p, by_linarith, by_linarith, by_linarith, hA, ?_⟩
    zukky
    · have := hostPt_eq W (p := p) (t := b - p) by_linarith by_linarith
      simp_all
    · have hk : zteie := by
        zulgm
        zufc
      zujwy
      rw [e, hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
        show ((p + 1 : ℕ) : ℝ) + 0 - p = 1 by push_cast; ring, sidePt_one,
        Nat.mod_eq_of_lt hk]
  · have hb0' : b = 0 := by
      zumv
      have hbpos : ztrzh := lt_of_le_of_ne hb0 zthrm
      zulvt
      zuxb
    have hpn1 : ztskp := by
      zumv
      zukcw
      zulvv
      zuxb
    refine ⟨1, by_linarith, le_rfl, by_linarith, hA, ?_⟩
    rw [hb0', show (0 : ℝ) = ((0 : ℕ) : ℝ) + 0 by simp, hostPt_eq W le_rfl one_pos,
      Chazelle.Chain.sidePt_zero, sidePt_one, hpn1, Nat.mod_self]
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The host polygon is counterclockwise.** -/
theorem hostPoly_orient (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    Mountain.orient ztefi = 1 := by
  zubze
  zuys
  zubl

  zucwp
  zuhxk
  zucvw
  have X : Extract.Ctx Q S R := ztonv
  have h3 := X.three
  zucgl
  zudg
  obtain ⟨z, hzR, hzV⟩ := exists_mem_off_heights hRo ztuxl
    ztyux
  have hvQ : ztioz := fun i hi e =>
    hzV (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e.symm⟩)
  obtain ⟨s, -, i, i', hi, hi', rfl, lam, hlam, he, r, hr, hnear⟩ :=
    ray_hit hQ hFam hne hR hzR hvQ ztp
  set P : Point := (ztokl : Point) with hPdef
  set A := hostPt M.W ztbmz with hAdef
  set B := hostPt M.W ztwkn with hBdef
  -- the ends are at vertex heights, the exit point is not
  obtain ⟨ha, hha, hAy⟩ := Extract.host_height X hi
  obtain ⟨hb, hhb, hBy⟩ := Extract.host_height X hi'
  have hPy : P.2 = A.2 + lam * (B.2 - A.2) := by
    have := congrArg Prod.snd he; tauto
  have hlam0 : lam ≠ 0 := by
    grind
  have hlam1 : lam ≠ 1 := by
    grind
  have hlam' : lam ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hlam.1 (Ne.symm hlam0), lt_of_le_of_ne hlam.2 hlam1⟩
  -- the gap is an arc gap
  zucgy
  rcases gap_cases hM hF hfin hne hR hN2 hi with ⟨a', b', harc, hsub⟩ | ⟨c, hc, p, p', t, t', hA,
      hB, hka, hkb, -⟩
  swap
  · exfalso
    obtain ⟨h, hh, x₁, x₂, rfl⟩ := hFam.2.2 c hc
    have hA' : A = sidePt M.W p t := by rw [hAdef, hka, hostPt_eq M.W hA.2.1 hA.2.2.1]
    have hB' : B = sidePt M.W p' t' := by rw [hBdef, hkb, hostPt_eq M.W hB.2.1 hB.2.2.1]
    have e1 : A.2 = (Q.vtx h).2 := by rw [hA']; exact hA.2.2.2.1.1
    have e2 : B.2 = (Q.vtx h).2 := by zuodu; exact hB.2.2.2.1.1
    grind
  zuyt

  have hnv : ∀ k : ℕ, k < M.W.n →
      ¬ sideInArc ztbmz ztwkn k := by
    zugoj
    exact hk_gap hM hF hfin hN2 hi
      (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k ztqal (by exact_mod_cast hk) hkin⟩)
      hkin
  obtain ⟨p, hp, t'', ht1, ht2, ht0, hAe, hBe⟩ := arcEdge_pair M.W hb1.1 hb1.2 hb2.1 hb2.2
    ztfhv hnv
  set τ₀ := hk M S R i - p with hτ₀
  -- the host edge as a piece of the walk edge
  zujzj
  have hvi : (hostPoly Q S R).vtx i = A := hostPoly_vtx hi
  have hvi' : (hostPoly Q S R).vtx ztyfz = B := by
    zuovs; exact hostPoly_vtx hsi
  have hiH : i < (hostPoly Q S R).n := by_grind
  have hcpos : 0 < t'' - τ₀ := by_linarith
  set t' := τ₀ + lam * ztcwp with ht'
  have ht'I : t' ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have : 0 < lam * ztcwp := mul_pos hlam'.1 hcpos; linarith
    · have : lam * ztcwp < 1 * ztcwp := mul_lt_mul_of_pos_right hlam'.2 hcpos
      linarith
  have hWn : (interiorWalk Q).n = M.W.n := rfl
  have hpW : p < (interiorWalk Q).n := hp
  have hoff : ∀ δ : ℝ, Chazelle.Jordan.offset ((hostPoly Q S R).vtx i)
      ((hostPoly Q S R).vtx ztyfz) lam δ =
      Chazelle.Jordan.offset ztbwp
        ztwkf t' ztxzc := by
    intro δ
    rw [hvi, hvi', show A = sidePt M.W p τ₀ from hAe, show B = sidePt M.W p t'' from hBe]
    exact ExtG.offset_lerp_pair _ _ _ _ _ _
  -- the exit point
  have hP' : Chazelle.Jordan.offset ztbwp
      ztwkf t' 0 = P := by
    rw [← zero_mul ztcwp, ← hoff 0, Chazelle.Jordan.offset_zero, hvi, hvi', he]
  refine Mountain.orient_eq_of_eventually hH hiH hlam' ztp ?_
  have hev := Mountain.eventually_offset_orient hWs hpW ht'I
  rw [hWo] at hev
  have hev' := (Loc.tendsto_mul_const_nhdsGT hcpos).eventually hev
  have hnearev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset ztbwp
      ztwkf t' ztbarb ∈
        ball P r := by
    have hcont : Continuous fun δ : ℝ => Chazelle.Jordan.offset ztbwp
        ztwkf t' ztbarb :=
      (Chazelle.Jordan.continuous_offset _ _ _).comp ztepq
    have h0 : Chazelle.Jordan.offset ztbwp
        ztwkf t' (1 * (0 * ztcwp)) = P := by
      grind
    have := hcont.tendsto 0
    zubuv
    exact (this.eventually ztsd).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hev', hnearev] with δ hδ hball
  rw [one_mul, hoff]
  have hD : Chazelle.Jordan.offset ztbwp
      ztwkf t' ztxzc ∈ M.D := by
    have h1 := hδ.1
    rw [one_mul, hWf, hWb] at h1
    zubvv
  zvohi at hball
  exact (region_sub_intHost hQ hFam hne hR (hnear _ hball hD)).1

/-- **The walk of the interior of the host polygon is the host polygon.** -/
theorem interiorWalk_hostPoly (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    interiorWalk ztefi = hostPoly Q S R := by
  have h := hostPoly_orient hQ hFam hne hR
  have hL : Mountain.LeftInside ztefi := by
    zuldp
    unfold Mountain.orient at h
    grind
  zumsz
  simp_all
open Chazelle.Chain (sidePrev sideNext sideCcw IsHChordIn)
open Mir
structure ExtractOK (Q : Polygon) (S : Set ztf) (R : Set Point) (C : Chain) : Prop where
  loc : ∀ {F₁ : Set ztf}, F₁ ⊆ (chainModel C).Adm → ∀ c ∈ Extract.kept R F₁,
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R
  region : ∀ {F₁ : Set ztf} {V : Set Point},
    V ∈ (interiorModel Q).regions ztjmd → V ⊆ R →
      ∃ U ∈ (chainModel C).regions F₁, V ⊆ U
  weight : ∀ {F₁ : Set ztf}, F₁ ⊆ (chainModel C).Adm → F₁.Finite →
    ∀ {U : Set Point}, U ∈ (chainModel C).regions F₁ → ∀ {V : Set Point}, V ⊆ R → V ⊆ U →
      (interiorModel Q).weight ztjmd V ≤ (chainModel C).weight F₁ U
  deg : ∀ {F₁ : Set ztf}, F₁ ⊆ (chainModel C).Adm → F₁.Finite →
    ∀ {U V : Set Point}, V ⊆ R → V ⊆ U →
      (interiorModel Q).deg ztjmd V ≤
        (chainModel C).deg F₁ U + (interiorModel Q).deg S R
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The extraction facts for the host chain** (counterclockwise orientation of the host). -/
theorem extractOK_host (X : Extract.Ctx Q S R) {g : ℕ} (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) :
    ExtractOK Q S R (hostChain Q S R g X.three) where
  loc := fun hF₁ _c hc => Extract.kept_local X hg hgc hF₁ hc
  region := fun hV hVR => Extract.exists_chain_region X hV hVR
  weight := fun {_} hF₁ hfin {_} hU {_} hVR hVU => Extract.weight_kept X hg hgc hF₁ hfin hU hVR hVU
  deg := fun {_} hF₁ hfin {_ _} hVR hVU => Extract.deg_kept X hg hgc hF₁ hfin hVR hVU

/-! ## Transport through the mirror -/

/-- **Kept chords of the mirrored family** are the mirrored kept chords. -/
theorem kept_mir (R : Set Point) (F : Set ztf) :
    mirF (Extract.kept R F) = Extract.kept zttm ztciv := by
  zubcj
  zudux
  unfold Extract.kept
  simp only [mem_ofPred_eq, mem_mirF]
  have e : mir '' (c ∩ mir '' R) = mir '' c ∩ R := by
    rw [image_inter mir_injective, image_mir_image_mir]
  constructor
  · zubf
    zujfv
    zvmyr at h2
    exact h2.of_image
  · zubf
    exact ⟨h1, by zvmyr; exact h2.image _⟩

/-- The mirrored family after extraction. -/
theorem mirF_step (S : Set ztf) (R : Set Point) (F : Set ztf) :
    mirF (S ∪ Extract.kept R F) = mirF S ∪ Extract.kept zttm ztciv := by
  rw [mirF_union, kept_mir]

/-- **The region hypotheses of the mirror image.** -/
theorem ctx_mir (X : Extract.Ctx Q S R) : Extract.Ctx Q.mir ztbks zttm := by
  have hI := modelMir_interior X.hQ
  refine ⟨mir_simple Q X.hQ, (hI.chordFamily Q S).2 X.hFam, mirF_nonempty.2 X.hne, ?_⟩
  rw [hI.regions]
  exact image_mem_mirF.2 X.hR

/-- **Extraction transfers from the mirror image.** -/
theorem extractOK_of_mir {C : Chain} (hQ : Q.Simple) (hP : C.P.Simple)
    (h : ExtractOK Q.mir ztbks zttm C.mir) : ExtractOK Q S R C := by
  have hI := modelMir_interior hQ
  have hC := modelMir_chain C hP
  have hadm : ∀ {F₁ : Set ztf}, F₁ ⊆ (chainModel C).Adm →
      mirF F₁ ⊆ (chainModel C.mir).Adm := fun hF₁ => by
    rw [hC.Adm]; exact mirF_subset.2 hF₁
  zudfi
  · intro F₁ hF₁ c hc
    have hc' : mir '' c ∈ Extract.kept zttm ztqtp := by
      rw [← kept_mir]; tauto
    obtain ⟨h1, h2⟩ := h.loc ztqpu _ hc'
    rw [hI.Adm, image_mem_mirF] at h1
    refine ⟨h1, fun x ⟨hxc, hxD⟩ => ?_⟩
    have := h2 ⟨mem_image_of_mem mir hxc, by rw [hI.D]; grind⟩
    rwa [mem_image_mir, mir_mir] at this
  · intro F₁ V hV hVR
    have hV' : mir '' V ∈ (interiorModel Q.mir).regions (mirF S ∪ Extract.kept zttm
        ztqtp) := by
      rw [← mirF_step, hI.regions]; tauto
    obtain ⟨U', hU', hVU'⟩ := h.region hV' ztqrn
    rw [hC.regions] at hU'
    refine ⟨mir '' U', mem_mirF.1 hU', ?_⟩
    rw [← image_mir_image_mir V]
    grind
  · intro F₁ hF₁ hfin U hU V hVR hVU
    have hU' : mir '' U ∈ (chainModel C.mir).regions ztqtp := by
      rw [hC.regions]; tauto
    have := h.weight ztqpu ztvze hU' ztqrn ztvwy
    rwa [← mirF_step, hI.weight, hC.weight] at this
  · intro F₁ hF₁ hfin U V hVR hVU
    have := h.deg ztqpu ztvze (U := mir '' U) ztqrn
      ztvwy
    rwa [← mirF_step, hI.deg, hC.deg, hI.deg] at this

/-! ## The kept test for a clockwise host -/

/-! ## Host descriptions of the mirrored polygon -/
end
end DownDrv
namespace DownStep
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)
open DownHost

/-- **The family after one down step.** -/
def stepFam (Q : Polygon) (S : Set ztf) (F : Set Point → Set ztf) :
    Set ztf :=
  S ∪ ⋃ R ∈ (interiorModel Q).regions S, Extract.kept R ztemp

/-! ## The level instance -/

/-- The granularity after the merge chain of a region at merge grade `μ`: leaves `γ'_μ`, box
transport `2 γ'_μ`, at most `15` merges with `fuseLoss = 1`. -/
noncomputable def gamma1 (μ : ℕ) : ℕ := 2 * gradeGran μ + 15

/-- **The schedule**: `γ₁ ≤ 2^(⌈βμ⌉ + 12)`, the semigranularity bound (I2) of index `μ`. -/
theorem gamma1_le (μ : ℕ) : gamma1 μ ≤ 2 ^ ztfni := by
  have h := gradeGran_le_real μ
  have hN : gradeGran μ ≤ 1201 * 2 ^ Cost.ceilBeta μ := by exact_mod_cast h
  have h1 : 1 ≤ 2 ^ Cost.ceilBeta μ := Nat.one_le_two_pow
  unfold gamma1
  grind
end
end DownStep
namespace DownDrv
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)
open DownHost DownStep Mir
variable {Q : Polygon} {S : Set (Set Point)}

/-- **The down step for arbitrary region chains** (X1–X4 for all regions at once): given, for
every region `R` of `S`, a chain `C R` with the extraction facts and a chord family `F R` of
`chainModel (C R)` of degree `≤ D`, `γ`-semigranular, the family `stepFam Q S F` is an interior
chord family of degree `≤ D + d₀`, `γ`-semigranular, whose new chords come from the `F R`. -/
theorem downStepG (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {d₀ D γ : ℕ} (hdeg : (interiorModel Q).DegLe S d₀) (C : Set Point → Chain)
    (F : Set Point → Set ztf)
    (hEx : ∀ R ∈ (interiorModel Q).regions S, ExtractOK Q S R ztjhe)
    (hF : ∀ R ∈ (interiorModel Q).regions S,
      (chainModel ztjhe).ChordFamily Q ztemp ∧ (chainModel ztjhe).DegLe ztemp D ∧
        (chainModel ztjhe).Semigranular ztemp γ) :
    (interiorModel Q).ChordFamily Q ztlto ∧
      (interiorModel Q).DegLe ztlto (D + d₀) ∧
      (interiorModel Q).Semigranular ztlto γ ∧
      stepFam Q S F \ S ⊆ ⋃ R ∈ (interiorModel Q).regions S, F R := by
  zuhm
  set T := stepFam Q S F with hT
  zulk
  have hRfin : (I.regions S).Finite :=
    (hM.sys S hFam.2.1 hFam.1).regionsIn_finite hM.preconn hM.nonempty subset_rfl
  have hloc : ∀ R (hR : R ∈ I.regions S), ∀ c ∈ Extract.kept R ztemp, c ∈ I.Adm ∧ c ∩ I.D ⊆ R :=
    fun R hR c hc => (hEx R hR).loc (hF R hR).1.2.1 c hc
  have hmem : ∀ c, c ∈ T → c ∈ S ∨ ∃ R ∈ I.regions S, c ∈ Extract.kept R ztemp := by
    zubyh
    · simp_all
    simp_all
  have hkT : ∀ R ∈ I.regions S, Extract.kept R ztemp ⊆ T := fun R hR c hc =>
    Or.inr (mem_iUnion₂.2 ⟨R, hR, hc⟩)
  have hTfin : T.Finite :=
    hFam.1.union (hRfin.biUnion fun R hR => (hF R hR).1.1.subset fun c hc => hc.1)
  have hTadm : T ⊆ I.Adm := fun c hc => by
    zuejx
    · exact hFam.2.1 hcS
    grind
  have hX1 : I.ChordFamily Q T := by
    refine ⟨hTfin, hTadm, fun c hc => ?_⟩
    zuejx
    · exact hFam.2.2 c hcS
    · exact (hF R hR).1.2.2 c hcR.1
  have hX4 : T \ S ⊆ ⋃ R ∈ I.regions S, F R := by
    rintro c ⟨hc, hcS⟩
    rcases hmem c hc with h | ⟨R, hR, hcR⟩
    · simp_all
    · exact mem_iUnion₂.2 ⟨R, hR, hcR.1⟩
  have hST : S ⊆ T := subset_union_left
  have key : ∀ V ∈ I.regions T, I.deg T V ≤ D + d₀ ∧ I.weight T V ≤ γ := by
    zulmk
    zuov
    have hVS : V ⊆ freeIn I.D S :=
      (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti I.D hST)
    set R := connectedComponentIn (freeIn I.D S) v with hRdef
    have hR : ztulz := ⟨v, hVS hv, rfl⟩
    have hVR : V ⊆ R :=
      (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVS
    set G := S ∪ Extract.kept R ztemp with hG
    have hSG : S ⊆ G := subset_union_left
    have hGT : G ⊆ T := union_subset hST (hkT R hR)
    have hK : OutOther I.D S G T R := by
      intro c hc hcG
      rcases hmem c hc with hcS | ⟨R', hR', hcR'⟩
      · grind
      · refine ⟨R', hR', fun e => hcG (Or.inr (e ▸ hcR')), (hloc R' hR' c hcR').2⟩
    have hVG : V ∈ I.regions G := region_restrict hSG hGT hR hK hV hVR
    obtain ⟨U, hU, hVU⟩ := (hEx R hR).region hVG hVR
    have hsys := hM.sys T hTadm hTfin
    zujx
    · have hdegTG : I.deg T V = I.deg G V := by
        zuhqm
        rw [exits_restrict hsys hST hGT hR hK hVR]
      rw [hdegTG]
      have h1 : I.deg G V ≤ (chainModel ztjhe).deg ztemp U + I.deg S R :=
        (hEx R hR).deg (hF R hR).1.2.1 (hF R hR).1.1 hVR hVU
      have h2 := (hF R hR).2.1 U hU
      have h3 := hdeg R hR
      omega
    · rw [weight_restrict hM hTadm hTfin hSG hGT hR hK hV hVR]
      exact ((hEx R hR).weight (hF R hR).1.2.1 (hF R hR).1.1 hU hVR hVU).trans
        ((hF R hR).2.2 U hU)
  exact ⟨hX1, fun V hV => (key V hV).1, fun V hV => (key V hV).2, hX4⟩
end
end DownDrv
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (regionsIn)
open DownHost DownStep Mir

/-! ## Lemma 2.3 in a chain model, explicit constant -/
theorem chainModel_size (C : Chain) : (chainModel C).size = 2 * C.m := by
  zuet
  zujpy
  have : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} =
      Set.Ico 6 ztcc := by
    zufj
    zuckp

  zugfl
variable {C : Chain}
/-- **Lemma 2.3 for a chain model** (explicit constant): `|F| (γ + 1) ≤ 140 (D + 2) (2 m + 1)`. -/
theorem lemma23_chain (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    {γ D : ℕ} (hF : (chainModel C).ChordFamily Q F) (hdeg : (chainModel C).DegLe F D)
    (hgran : (chainModel C).Granular F γ) :
    F.ncard * ztgj ≤ 140 * ztmo * ztyw := by
  have hM : ztycg := Or.inl ztiv
  zugc

  obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk _ hM
  rw [← chainModel_size]
  zucyo
  · zuqx
    · simp
    · zugkd
  · zucgc
    calc F.ncard * ztgj ≤ 2 * ztjis := by_nlinarith
      _ ≤ 2 * (2 * ztmo * (5 * (chainModel C).W.n)) := Nat.mul_le_mul_left _ h
      _ ≤ 2 * (2 * ztmo * (5 * (7 * zteiv))) := by gcongr
      _ = 140 * ztmo * zteiv := by_ring

/-! ## The host sizes -/
theorem interiorModel_n (Q : Polygon) : (interiorModel Q).W.n = Q.n :=
  interiorWalk_n Q

/-- **The host sizes** sum to at most `n + 4 |S|`. -/
theorem sum_nk_le' {Q : Polygon} (hQ : Q.Simple) {S : Set ztf}
    (hFam : (interiorModel Q).ChordFamily Q S) (T : Finset ztf)
    (hT : ∀ R ∈ T, R ∈ (interiorModel Q).regions S) :
    ∑ R ∈ T, nk ztd S R ≤ Q.n + 4 * S.ncard := by
  zuok
  have hsum := DownDrv.sum_nk_le hM hFam.2.1 hFam.1
  have hsys := hM.sys _ hFam.2.1 hFam.1
  have hRfin : ((interiorModel Q).regions S).Finite :=
    hsys.regionsIn_finite hM.preconn hM.nonempty subset_rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, interiorModel_n] at hsum
  refine le_trans (Finset.sum_le_sum_of_subset fun R hR => ?_) hsum
  simp_all

/-! ## One level -/

/-! ## Restoration rounds -/

/-- **The level bound** in the form of `DownMath.cnt_step`: if one level gives `K₁` chords with
`K₁ (γ + 1) ≤ K (γ + 1) + B (n + 4 K)` and the restoration rounds give `K' + 1 ≤ A (K₁ + 1)`,
then `K' (γ + 1) ≤ A ((K + 1) (γ + 1) + B (n + 4 K))`. -/
theorem level_bound {K K₁ K' A B n γ : ℕ} (h1 : K₁ * ztgj ≤ K * ztgj + B * ztbhx)
    (h2 : K' + 1 ≤ A * ztnmc) :
    K' * ztgj ≤ A * ztysh := by
  calc K' * ztgj ≤ ztnlz * ztgj := Nat.mul_le_mul_right _ (Nat.le_succ _)
    _ ≤ A * ztnmc * ztgj := Nat.mul_le_mul_right _ h2
    _ = A * (K₁ * ztgj + ztgj) := by_ring
    _ ≤ A * (K * ztgj + B * ztbhx + ztgj) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right h1 _)
    _ = A * ztysh := by_ring

/-! ## The transition -/

/-- **Lemma 2.3 for the top chain**: a `γ'_p`-canonical map of the top chain (`m = n - 1`, cap
`4`) has `K₀ (γ'_p + 1) ≤ 840 (2 (n - 1) + 1)` chords (the hypothesis of
`DownMath.cnt_trans`). -/
theorem trans_count (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hN : IsCanonicalNF ztc Q N γ 4) :
    (N.F ztc Q).ncard * ztgj ≤ 840 * ztyw := by
  obtain ⟨hNF, hdeg, hgran, -⟩ := hN
  have := lemma23_chain hP hNF.1 hdeg hgran
  omega
end
end DownMath
namespace Trans
@[expose] public section
open Set
open Chazelle.Chain (sidePt)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (coordBound)

/-- **The top chain** of `Q`. -/
structure Top (Q : Polygon) (C : Chain) : Prop where
  hP : C.P = Q
  hs : C.s = 0
  hm : C.m + 1 = Q.n
variable {Q : Polygon} {C : Chain}
theorem Top.n_pos (T : Top Q C) : 0 < Q.n := by have := T.hm; omega
theorem Top.edgeIdx (T : Top Q C) {k : ℕ} (hk : k < Q.n) : C.edgeIdx k = k := by
  unfold Chain.edgeIdx; rw [T.hs, zero_add, T.hP, Nat.mod_eq_of_lt hk]

/-- Chain vertex `k` is vertex `k` of `Q`. -/
theorem Top.vertex_eq (T : Top Q C) {k : ℕ} (hk : k < Q.n) : C.vertex k = Q.vtx k := by
  unfold Chain.vertex; rw [T.edgeIdx hk, T.hP]

/-- Chain edge `k` is edge `k` of `Q`. -/
theorem Top.chainEdge_eq' (T : Top Q C) {k : ℕ} (hk : k < C.m) : C.chainEdge k = Q.edge k := by
  unfold Chain.chainEdge; rw [T.edgeIdx (by have := T.hm; omega), T.hP]

/-- Every vertex of `Q` is at most as high as the top vertex. -/
theorem Top.vtx_le_top (T : Top Q C) {k : ℕ} (hk : k < Q.n) : (Q.vtx k).2 ≤ C.top.2 := by
  rw [← T.vertex_eq hk]; exact C.vertex_snd_le_top (by have := T.hm; omega)

/-- Every boundary point of `Q` is at most as high as the top vertex. -/
theorem Top.boundary_le_top (T : Top Q C) {z : Point} (hz : z ∈ Q.boundary) : z.2 ≤ C.top.2 := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hz
  have h1 := T.vtx_le_top hi
  have h2 := T.vtx_le_top (Nat.mod_lt ztg T.n_pos)
  zubi
  nlinarith

/-- **The filled polygon lies below the top vertex** (a point above it sees the far exterior along
an upward ray). -/
theorem Top.filled_below_top (hQ : Q.Simple) (T : Top Q C) {z : Point} (hz : z ∈ Q.filled) :
    z.2 ≤ C.top.2 := by
  zube

  set L : ℝ := coordBound Q + |z.2| + 1 with hL
  have hL0 : 0 ≤ L := by zvnlm; have := abs_nonneg z.2; have := C.coordBound_nonneg; rw [T.hP] at this; linarith
  set f : ℝ → Point := fun t => (z.1, z.2 + t) with hf
  have hpre : IsPreconnected (f '' Icc 0 L) :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous f).continuousOn
  have hsub : f '' Icc 0 L ⊆ Q.boundaryᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hb
    have := T.boundary_le_top hb
    grind
  have hw : f L ∉ Q.filled := Chazelle.Jordan.far_not_mem_filled Q (Or.inr (Or.inr (Or.inl (by
    grind))))
  have hzT : z ∈ f '' Icc 0 L := ⟨0, ⟨le_rfl, hL0⟩, by_simp_all⟩
  exact FactsInterior.subset_exterior hQ hpre hsub ⟨L, ⟨hL0, le_rfl⟩, rfl⟩ hw hzT hz

/-- The chain lies on the boundary of `Q`. -/
theorem Top.set_sub (T : Top Q C) : C.set ⊆ Q.boundary := by
  rintro z ⟨k, hk, hz⟩
  rw [T.chainEdge_eq' hk] at hz
  exact ⟨k, by have := T.hm; omega, hz⟩

/-- **The interior of `Q` lies in the domain of its top chain.** -/
theorem Top.interior_sub_dom (hQ : Q.Simple) (T : Top Q C) :
    Q.filled \ Q.boundary ⊆ C.dom := by
  rintro z ⟨hzf, hzb⟩
  refine C.mem_dom_iff.2 ⟨?_, fun hs => hzb (T.set_sub hs), fun hs => ?_⟩
  · have hsq := Chazelle.Jordan.filled_subset_square Q hzf
    have := C.coordBound_lt_radius
    zukpz
    exact ⟨lt_of_le_of_lt hsq.1 this, lt_of_le_of_lt hsq.2 this⟩
  · zufxy
    have h3 := T.filled_below_top hQ hzf
    have hzt : z = C.top := Prod.ext h1 (le_antisymm h3 h2)
    exact hzb (T.set_sub zttov)

/-- The last edge of `Q`. -/
theorem Top.last_edge (T : Top Q C) : Q.edge C.m = Chazelle.segment ztcpk ztccl := by
  zucrd
  rw [show ztbpj % Q.n = 0 by rw [T.hm, Nat.mod_self]]

/-- **The boundary of `Q` meets the domain of `C` only in the open part of `e_{n-1}`.** -/
theorem Top.boundary_dom (T : Top Q C) {z : Point} (hz : z ∈ Q.boundary) (hzD : z ∈ C.dom) :
    ∃ s ∈ Ioo (0 : ℝ) 1, z = lerp ztcpk ztccl s := by
  have hzs := C.not_mem_set_of_mem_dom hzD
  obtain ⟨i, hi, hzi⟩ := hz
  have him : i = C.m := by
    zumv
    exact hzs ⟨i, by have := T.hm; omega, by rw [T.chainEdge_eq' (by have := T.hm; omega)]; omega⟩
  subst him
  rw [T.last_edge] at hzi
  obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzi
  have hm0 : C.vertex C.m = Q.vtx C.m := T.vertex_eq by_omega
  have h00 : C.vertex 0 = Q.vtx 0 := T.vertex_eq T.n_pos
  refine ⟨s, ztcp, rfl⟩
  · zuvl
    · zubh
    · exfalso; subst h; rw [Chazelle.Geometry.lerp_zero, ← hm0] at hzs
      exact hzs (C.vertex_mem_set le_rfl)
  · zukmf
    · zubh
    · exfalso; subst h; rw [Chazelle.Geometry.lerp_one, ← h00] at hzs
      exact hzs (C.vertex_mem_set ztbg)
open Filter Topology Metric
open Chazelle.Chain (IsHChordIn)
open Chazelle.Jordan (offset nrm)
open Chazelle.Visibility (hseg)

/-- **Crossing an open non-horizontal edge horizontally**: for small `ε`, exactly one of the two
horizontal neighbours of a point of the open edge is in the filled polygon. -/
theorem cross_sides {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hh : (P.vtx i).2 ≠ (P.vtx ztwjy).2) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      ((((lerp ztdn ztwir t₀).1 - ε,
        (lerp ztdn ztwir t₀).2) : Point) ∈ P.filled ↔
      (((lerp ztdn ztwir t₀).1 + ε,
        (lerp ztdn ztwir t₀).2) : Point) ∉ P.filled) := by
  zuwz

  set w := lerp u v t₀ with hw
  obtain ⟨r, hr, hstrip⟩ := Chazelle.Jordan.strip hP hi ht₀
  have hcont1 : Continuous (fun δ : ℝ => offset u v t₀ δ) := by unfold offset; fun_prop
  have hcont2 : Continuous (fun δ : ℝ => offset u v t₀ (-δ)) := by unfold offset; fun_prop
  have h0 : offset u v t₀ 0 = w := by_simp_all
  have h0' : offset u v t₀ (-0) = w := by_simp_all
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t₀ δ ∈ ball w r :=
    (hcont1.tendsto 0).mono_left nhdsWithin_le_nhds (by zvmzn; exact ball_mem_nhds w hr)
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t₀ _ ∈ ball w r :=
    (hcont2.tendsto 0).mono_left nhdsWithin_le_nhds (by rw [h0']; exact ball_mem_nhds w hr)
  obtain ⟨δ, hδs, hδ1, hδ2, hδ0⟩ := ((Chazelle.Jordan.edge_sides hP hi ht₀).and
    (hev1.and ztqpz)).exists
  zuyx
  zukgk
  have hsq := Chazelle.Jordan.sqLen_pos huv
  -- the two half-disks
  set Hp := ball w r ∩ {x | 0 < (1 : ℝ) * Chazelle.det u v x} with hHp
  set Hm := ball w r ∩ {x | 0 < (-1 : ℝ) * Chazelle.det u v x} with hHm
  have hpre := fun σ =>
    ((convex_ball w r).inter (Chazelle.Jordan.convex_det_pos u v σ)).isPreconnected
  have hsub := (Chazelle.Jordan.side_subset_compl P hstrip)
  have hL : offset u v t₀ δ ∈ Hp := ⟨hδ1, by
    show 0 < 1 * Chazelle.det u v _
    zuoxn; nlinarith⟩
  have hR : offset u v t₀ _ ∈ Hm := ⟨hδ2, by
    show 0 < -1 * Chazelle.det u v _
    zuoxn; nlinarith⟩
  have hdw : Chazelle.det u v w = 0 := by
    zunft; exact Chazelle.Geometry.det_eq_zero_of_mem_segment
      (Chazelle.Geometry.lerp_mem_segment _ _ ht₀.1.le ht₀.2.le)
  refine ⟨r, hr, fun ε hε0 hεr => ?_⟩
  have hdist : ∀ σ : ℝ, ztdd → (ztojt : Point) ∈ ball w r := by
    intro σ hσ
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show w.1 + σ * ε - w.1 = σ * ε by ring, abs_mul, abs_of_pos hε0]
    rcases hσ with rfl | rfl <;> norm_num <;> exact by_grind
  have hdet : ∀ σ : ℝ, Chazelle.det u v (ztojt : Point) =
      -ztolb * ztgv := by
    intro σ
    have := hdw
    unfold Chazelle.det at this ⊢
    grind
  have hm := hdist _ ztbt
  have hp := hdist 1 ztp
  rw [show w.1 + -1 * ε = w.1 - ε by ring] at hm
  rw [show w.1 + 1 * ε = w.1 + ε by ring] at hp
  have hdm : Chazelle.det u v (ztkgv : Point) = ε * ztgv := by
    have := hdet (-1); grind
  have hdp : Chazelle.det u v (ztkgu : Point) = -(ε * ztgv) := by
    have := hdet 1; grind
  have hLR : offset u v t₀ δ ∈ P.filled ↔ offset u v t₀ _ ∉ P.filled := hδs
  rcases lt_or_gt_of_ne (sub_ne_zero.2 ztqaz) with hneg | hpos
  · -- `v.2 < u.2`: the right neighbour is on the positive side
    have hpH : (ztkgu : Point) ∈ Hp := ⟨hp, by
      show 0 < 1 * _; zuoxo; nlinarith⟩
    have hmH : (ztkgv : Point) ∈ Hm := ⟨hm, by
      show 0 < -1 * _; zuoxp; nlinarith⟩
    have e1 := FactsInterior.filled_iff_of_preconnected hP ztvvz ztvwg hpH hL
    have e2 := FactsInterior.filled_iff_of_preconnected hP ztvwa ztvwh hmH hR
    grind
  · -- `u.2 < v.2`: the left neighbour is on the positive side
    have hmH : (ztkgv : Point) ∈ Hp := ⟨hm, by
      show 0 < 1 * _; zuoxp; nlinarith⟩
    have hpH : (ztkgu : Point) ∈ Hm := ⟨hp, by
      show 0 < -1 * _; zuoxo; nlinarith⟩
    have e1 := FactsInterior.filled_iff_of_preconnected hP ztvvz ztvwg hmH hL
    have e2 := FactsInterior.filled_iff_of_preconnected hP ztvwa ztvwh hpH hR
    grind
variable {Q : Polygon} {C : Chain}

/-- **A sub-chord through an interior point**: inside a horizontal segment whose ends are off the
interior of `Q`, every interior point lies on an interior chord of `Q` contained in the segment. -/
theorem sub_chord {y a b x : ℝ} (hab : a ≤ x ∧ x ≤ b)
    (ha : (ztdv : Point) ∉ Q.filled \ Q.boundary) (hb : (ztdy : Point) ∉ Q.filled \ Q.boundary)
    (hx : (ztjw : Point) ∈ Q.filled \ Q.boundary) (hQ : Q.Simple) :
    ∃ a' b', a ≤ a' ∧ a' < x ∧ x < b' ∧ b' ≤ b ∧ IsHChordIn ztrx y a' b' := by
  have hDo : ztsbs := Chazelle.Jordan.isOpen_filled_sdiff_boundary hQ
  have hcont : Continuous (fun t : ℝ => (ztevw : Point)) := by fun_prop
  have hclo :=
    hDo.isClosed_compl.preimage hcont
  -- the left end
  set A := Icc a x ∩ {t : ℝ | (ztevw : Point) ∉ Q.filled \ Q.boundary} with hA
  have hAc : IsClosed A := isClosed_Icc.inter hclo
  have hAne : A.Nonempty := ⟨a, by_simp_all, ha⟩
  have hAbdd : BddAbove A := ⟨x, fun t ht => ht.1.2⟩
  have ha'A := hAc.csSup_mem hAne hAbdd
  set a' := sSup A with ha'
  have ha'x : a' < x := by_grind
  have hleft : ∀ t, a' < t → t ≤ x → (ztevw : Point) ∈ Q.filled \ Q.boundary := by
    zujbp
    zuhbw
    have : t ≤ a' := le_csSup hAbdd by_grind
    linarith
  -- the right end
  set B := Icc x b ∩ {t : ℝ | (ztevw : Point) ∉ Q.filled \ Q.boundary} with hB
  have hBc : IsClosed B := isClosed_Icc.inter hclo
  have hBne : B.Nonempty := ⟨b, by_grind, hb⟩
  have hBbdd : BddBelow B := ⟨x, fun t ht => ht.1.1⟩
  have hb'B := hBc.csInf_mem hBne hBbdd
  set b' := sInf B with hb'
  have hxb' : x < b' := by_grind
  have hright : ∀ t, x ≤ t → t < b' → (ztevw : Point) ∈ Q.filled \ Q.boundary := by
    zujbp
    zuhbw
    have : b' ≤ t := csInf_le hBbdd by_grind
    linarith
  refine ⟨a', b', ha'A.1.1, ha'x, hxb', hb'B.1.2,
    ⟨by_linarith, ha'A.2, hb'B.2, fun t ht1 ht2 => ?_⟩⟩
  grind

/-- **One piece per chord.**  A horizontal chord of the domain of the top chain contains at most
one interior chord of `Q`, when the last edge of `Q` is not horizontal. -/
theorem one_piece (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {y a b : ℝ} (hc : IsHChordIn C.dom y a b)
    {d₁ d₂ : Set Point} (hd₁ : d₁ ∈ (interiorModel Q).Adm) (hd₂ : d₂ ∈ (interiorModel Q).Adm)
    (h₁ : d₁ ⊆ hseg y a b) (h₂ : d₂ ⊆ hseg y a b) : d₁ = d₂ := by
  obtain ⟨y₁, a₁, b₁, hc₁, rfl⟩ := hd₁
  obtain ⟨y₂, a₂, b₂, hc₂, rfl⟩ := hd₂
  have hmem : ∀ {y' a' b' : ℝ}, IsHChordIn ztrx y' a' b' →
      hseg y' a' b' ⊆ hseg y a b → y' = y ∧ a ≤ a' ∧ b' ≤ b := by
    intro y' a' b' hc' hs
    have e1 := hs ztxrf
    have e2 := hs (show (ztjog : Point) ∈ hseg y' a' b' from ⟨rfl, hc'.lt.le, le_rfl⟩)
    exact ⟨e1.1, e1.2.1, e2.2.2⟩
  obtain ⟨hy₁, ha₁, hb₁⟩ := hmem hc₁ h₁
  obtain ⟨hy₂, ha₂, hb₂⟩ := hmem hc₂ h₂
  rw [hy₁] at hc₁ ⊢
  rw [hy₂] at hc₂ ⊢
  -- a boundary point of `Q` inside the chord lies on `e_{n-1}` at height `y`
  have hbd : ∀ e : ℝ, a < e → e < b → (ztcna : Point) ∉ Q.filled \ Q.boundary →
      (ztcna : Point) ∈ closure ztrx →
      ∃ s ∈ Ioo (0 : ℝ) 1, (ztcna : Point) = lerp ztcpk ztccl s := by
    intro e hae heb hnD hcl
    have hf :=
      closure_minimal by_grind ztuxn hcl
    have hbd : (ztcna : Point) ∈ Q.boundary := by
      grind
    exact T.boundary_dom hbd (hc.open_mem e hae heb)
  -- the parameter on `e_{n-1}` is determined by the height
  have hs_eq : ∀ e e' s s' : ℝ, (ztcna : Point) = lerp ztcpk ztccl s →
      ((e', y) : Point) = lerp ztcpk ztccl s' → s = s' ∧ e = e' := by
    intro e e' s s' h h'
    have h2 := congrArg Prod.snd h
    have h2' := congrArg Prod.snd h'
    zuftb
    have h1' := congrArg Prod.fst h'
    simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] at h1 h1' h2 h2'
    grind
  -- closure points
  have hclL : ∀ {a' b' : ℝ}, IsHChordIn ztrx y a' b' →
      (ztfpb : Point) ∈ closure ztrx := by
    zuyy

    refine ⟨(b' - m, y), hc'.open_mem _ by_linarith by_linarith, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show b' - (b' - m) = m by ring, abs_of_pos hm0]
    grind
  have hclR : ∀ {a' b' : ℝ}, IsHChordIn ztrx y a' b' →
      (ztfoz : Point) ∈ closure ztrx := by
    zuyy

    refine ⟨(a' + m, y), hc'.open_mem _ by_linarith by_linarith, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show a' - (a' + m) = -m by ring, abs_neg, abs_of_pos hm0]
    grind
  -- two distinct pieces would be separated by a crossing with the interior on both sides
  have key : ∀ {a₁ b₁ a₂ b₂ : ℝ}, IsHChordIn ztrx y a₁ b₁ →
      IsHChordIn ztrx y a₂ b₂ → a ≤ a₁ → b₂ ≤ b → b₁ ≤ a₂ → False := by
    intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁ hb₂ h12
    obtain ⟨s, hs, e⟩ := hbd b₁ ztjpv ztjpw hc₁.right_not
      (hclL hc₁)
    obtain ⟨s', hs', e'⟩ := hbd a₂ ztjpv ztjpw hc₂.left_not
      (hclR hc₂)
    obtain ⟨rfl, rfl⟩ := hs_eq _ _ _ _ e e'
    have hmn : C.m < Q.n := by have := T.hm; omega
    have hsucc : ztbpj % Q.n = 0 := by rw [T.hm, Nat.mod_self]
    have hh' : (Q.vtx C.m).2 ≠ (Q.vtx (ztbpj % Q.n)).2 := by_grind
    obtain ⟨ε₀, hε₀, hcross⟩ := cross_sides hQ hmn hs hh'
    rw [hsucc, ← e] at hcross
    set ε := min ztcop ztbne with hεd
    have hε0 : ztbad := lt_min by_linarith (lt_min ztjpv ztjpw)
    have hε1 : ztmxm := by have := min_le_left ztcop ztbne; linarith
    have hε2 : ε < b₁ - a₁ := by
      have := min_le_right ztcop ztbne
      have := min_le_left ztmyk ztmyl; grind
    have hε3 : ε < b₂ - b₁ := by
      have := min_le_right ztcop ztbne
      have := min_le_right ztmyk ztmyl; grind
    have hl := hc₁.open_mem (b₁ - ε) by_linarith by_linarith
    have hr := hc₂.open_mem (b₁ + ε) by_linarith by_linarith
    exact ((hcross ε hε0 hε1).1 hl.1) hr.1
  rcases lt_trichotomy a₁ a₂ with h | h | h
  · have hb₁a₂ : b₁ ≤ a₂ := by
      zuso
      exact hc₂.left_not (hc₁.open_mem a₂ h hlt)
    grind
  · zubst
    rcases lt_trichotomy b₁ b₂ with h' | h' | h'
    · exact absurd (hc₂.open_mem b₁ hc₁.lt h') hc₁.right_not
    · zuczu
    · exact absurd (hc₁.open_mem b₂ hc₂.lt h') hc₂.right_not
  · have hb₂a₁ : b₂ ≤ a₁ := by
      zuso
      exact hc₁.left_not (hc₂.open_mem a₁ h hlt)
    grind

/-- **The pieces** of a chain family: the interior chords of `Q` inside its chords. -/
def pieces (Q : Polygon) (F₀ : Set ztf) : Set ztf :=
  {d | d ∈ (interiorModel Q).Adm ∧ ∃ c ∈ F₀, d ⊆ c}

/-- **The pieces form a chord family of the interior model.** -/
theorem chordFamily_pieces (T : Top Q C) {F₀ : Set ztf}
    (hF₀ : (chainModel C).ChordFamily C.P F₀) (hQ : Q.Simple)
    (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2) :
    (interiorModel Q).ChordFamily Q ztcfd ∧ (pieces Q F₀).ncard ≤ F₀.ncard := by
  classical
  -- the chosen chord of a piece
  zudhn

  have hinj : Set.InjOn f ztcfd := by
    zukje
    obtain ⟨y, a, b, hc, -, hcab⟩ := hF₀.2.1 (hf d₁ h₁)
    have s1 := hfd d₁ h₁
    have s2 := hfd d₂ h₂
    zuemu

    exact one_piece hQ T hh hc h₁.1 h₂.1 s1 s2
  have hfin : (pieces Q F₀).Finite :=
    Set.Finite.of_finite_image (hF₀.1.subset by_grind) hinj
  refine ⟨⟨hfin, fun d hd => hd.1, fun d hd => ?_⟩, ?_⟩
  · obtain ⟨c, hc, hdc⟩ := hd.2
    obtain ⟨h, hh', a, b, rfl⟩ := hF₀.2.2 c hc
    obtain ⟨y', a', b', hc', rfl⟩ := hd.1
    have e := hdc ztxrf
    refine ⟨h, by rw [← T.hP]; omega, a', b', ?_⟩
    rw [show y' = (C.P.vtx h).2 from e.1, T.hP]
  · exact Set.ncard_le_ncard_of_injOn f by_omega hinj hF₀.1
open Chazelle.Chain (TouchesIn freeIn regionsIn)
theorem mem_piece (hQ : Q.Simple) (T : Top Q C) {F₀ : Set ztf}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {c : Set Point} (hc : c ∈ F₀) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ (interiorModel Q).D) : ∃ d ∈ pieces Q F₀, z ∈ d := by
  zudji
  zugpz
  zuheu
  have hz : (zthlk : Point) ∈ Q.filled \ Q.boundary := by
    rw [← hzy]; tauto
  obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord ⟨hza, hzb⟩
    ztgjd ztgje hz hQ
  refine ⟨hseg y a' b', ⟨ztcpc, hseg y a b, hc, fun p hp =>
    ⟨hp.1, by zuoxq, by linarith [hp.2.2]⟩⟩, hzy, ha'x.le, hxb'.le⟩

/-- **Every region of the pieces lies in a region of the chain family.** -/
theorem exists_chain_region (hQ : Q.Simple) (T : Top Q C) {F₀ : Set ztf}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {V : Set Point}
    (hV : V ∈ (interiorModel Q).regions ztcfd) :
    ∃ U ∈ (chainModel C).regions F₀, V ⊆ U := by
  zuov
  have hfree : V ⊆ freeIn (chainModel C).D F₀ := by
    zugh
    have hzV := Chazelle.Chain.regionsIn_subset hV hz
    refine ⟨T.interior_sub_dom hQ hzV.1, fun ⟨c, hc, hzc⟩ => ?_⟩
    obtain ⟨d, hd, hzd⟩ := mem_piece hQ T hF₀ hc hzc hzV.1
    exact hzV.2 ⟨d, hd, hzd⟩
  exact ⟨_, ztpgd,
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hfree⟩

/-- **(T2) The degree does not grow.** -/
theorem deg_le (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {F₀ : Set ztf} (hF₀ : (chainModel C).ChordFamily C.P F₀) {U V : Set Point}
    (hVU : V ⊆ U) :
    (interiorModel Q).deg ztcfd V ≤ (chainModel C).deg F₀ U := by
  classical
  zuhqm
  zudhn

  zuheu
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hF₀.1.subset fun c hc => hc.1)
  · rintro d ⟨hd, z, ⟨hzd, hzD⟩, hzcl⟩
    exact ⟨hf d hd, z, ⟨hfd d hd hzd, hdom hzD⟩, closure_mono hVU hzcl⟩
  · zukje
    obtain ⟨y, a, b, hc, -, hcab⟩ := hF₀.2.1 (hf d₁ h₁.1)
    have s1 := hfd d₁ h₁.1
    have s2 := hfd d₂ h₂.1
    zuemu

    exact one_piece hQ T hh hc h₁.1.1 h₂.1.1 s1 s2

/-- **(T2) The pieces of a conformal chain family are conformal.** -/
theorem degLe_pieces (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {F₀ : Set ztf} (hF₀ : (chainModel C).ChordFamily C.P F₀) {D : ℕ}
    (hD : (chainModel C).DegLe F₀ D) : (interiorModel Q).DegLe ztcfd D := by
  zudic

  exact (deg_le hQ T hh hF₀ hVU).trans (hD U hU)
open Chazelle.Chain (sideLeft sideLeftOf sideCcw)
open TourA (sA tourA)
open TourB (tourB)
def DistinctH (Q : Polygon) : Prop :=
  ∀ i j, i < Q.n → j < Q.n → i ≠ j → (Q.vtx i).2 ≠ (Q.vtx j).2

/-- **The up direction lies in one of the two corners** at a vertex above both neighbours. -/
theorem up_in_one_corner {a v b : Point} {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) (hb : b.2 < v.2) :
    sideCcw ztfd ztbdn ztgg ∨ sideCcw ztgg ztbdn ztfd := by
  rw [Brute.sideCcw_up hh ha hb.ne, Brute.sideCcw_up hh hb ha.ne]
  have e : Chazelle.det b v a = -Chazelle.det a v b := by unfold Chazelle.det; ring
  zui
  have hD : Chazelle.det a v b = ztdin * ztti - ztbco * ztdio := rfl
  rcases lt_trichotomy (Chazelle.det a v b) 0 with hd | hd | hd
  · by_cases h1 : v.1 < b.1 ∨ a.1 < v.1
    · simp_all
    · zumie
      zuhl
      refine ⟨by_linarith, ?_, ?_⟩
      · rcases h1.2.lt_or_eq with h2 | h2
        · zucvi
        · exfalso; zvmxx at hD; nlinarith
      · rcases h1.1.lt_or_eq with h2 | h2
        · zucvi
        · exfalso; rw [← h2] at hD; nlinarith
  · simp_all
  · by_cases h1 : v.1 < b.1 ∧ a.1 < v.1
    · simp_all
    · zurx
      refine ztkix
      by_contra h2; push Not at h1 h2
      rcases lt_or_ge v.1 b.1 with h3 | h3
      · have h4 := h1 h3
        have h5 : a.1 = v.1 := le_antisymm h2.1 h4
        zuiik
      · have h5 : b.1 = v.1 := le_antisymm h3 h2.2
        zuiik

/-- **The up direction is not in the corner of the interior walk at the top vertex.** -/
theorem up_not_corner (hQ : Q.Simple) (T : Top Q C) {p : ℕ} (hp : p < (interiorWalk Q).n)
    (hpv : (interiorWalk Q).vtx p = C.top) :
    ¬ sideCcw ((interiorWalk Q).vtx ztxlt - C.top)
      ztyy
      ((interiorWalk Q).vtx ((p + (interiorWalk Q).n - 1) % (interiorWalk Q).n) - C.top) := by
  zuchg
  zudg
  set W := interiorWalk Q with hW
  have hup : ∀ ε : ℝ, 0 < ε → sideLeft W p 0 (C.top + ε • ztyy) := by
    zudik
    zugtq
    zucfg
    rw [hpv, add_sub_cancel_left]
    have := BoxT.sideCcw_smul one_pos hε one_pos
      (W.vtx ztwjb - C.top) ztyy
      (W.vtx ztbvk - C.top)
    simp_all
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hp le_rfl zero_lt_one
  have hrad : C.top.2 < C.radius := C.top_snd_lt_radius
  set ε := rC / (2 * ztox) with hε
  have hε0 : ztbad := div_pos hrC by_linarith
  set y := C.top + ε • ztyy with hy
  have hy2 : y.2 = C.top.2 + ε * ztox := by
    rfl
  have hy1 : y.1 = C.top.1 := by
    show (C.top + ε • ztyy).1 = _
    zughd
    zunvm
    ring
  have hpos : 0 < ε * ztox := mul_pos hε0 by_linarith
  have hdist : dist y C.top = rC / 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy1, hy2, sub_self, abs_zero,
      show C.top.2 + ε * ztox - C.top.2 = ε * ztox by ring,
      abs_of_pos hpos, max_eq_right hpos.le, hε]
    have : C.radius - C.top.2 ≠ 0 := by_linarith
    field_simp
  have hpt : sidePt W p 0 = C.top := by rw [Chazelle.Chain.sidePt_zero, hpv]
  have hyb : y ∈ ball (sidePt W p 0) rC := by rw [hpt, mem_ball, hdist]; linarith
  have hyD : y ∈ Q.filled \ Q.boundary := by
    by_contra hyD
    exact hclean y hyb by_grind zttoq
  have := T.filled_below_top hQ hyD.1
  grind
theorem iw_n : (interiorWalk Q).n = Q.n := by
  zufdi
  · rfl
  · zuhcp
theorem iw_vtx_left (h : Mountain.LeftInside Q) (j : ℕ) : (interiorWalk Q).vtx j = Q.vtx j := by
  unfold interiorWalk; simp_all
theorem iw_vtx_right (h : ¬ Mountain.LeftInside Q) {j : ℕ} (hj : j < Q.n) :
    (interiorWalk Q).vtx j = Q.vtx ztjlj := by
  unfold interiorWalk; zumzf; exact FactsInterior.rev_vtx Q j hj

/-- The neighbours of the top vertex are strictly lower. -/
theorem Top.nbr_lt (T : Top Q C) (hD : DistinctH Q) {k : ℕ} (hk : k < Q.n) (hkT : k ≠ C.topIdx) :
    (Q.vtx k).2 < C.top.2 := by
  have hT : C.topIdx < Q.n := by have := C.topIdx_le; have := T.hm; omega
  have h1 := T.vtx_le_top hk
  have h2 : ztpiy := T.vertex_eq hT
  zvmxx at h1 ⊢
  exact lt_of_le_of_ne h1 (hD k C.topIdx hk hT hkT)

/-- **The tour start is not inside the inner side.** -/
theorem sA_inner (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q) :
    (Mountain.LeftInside Q → sA C C.sideBeta = 0 ∨ C.m ≤ sA C C.sideBeta) ∧
      (¬ Mountain.LeftInside Q → sA C C.sideBeta ≤ C.m) := by
  zumcp
  zukdv
  have hup : ztyy = ztflo := by
    zujrv
    · show C.slitTop.1 - C.top.1 = 0; zunvm; ring
    · rfl
  have hrad : ztixs := by have := C.top_snd_lt_radius; linarith
  zufwr
  -- the corner of the top vertex in `Q`'s own order, and reversed
  have hbeta := C.sideBeta_eq_true_iff
  unfold sA
  constructor
  · zumgs
    zudjk
    · zubqb
      zuiea
      · -- `β = true` with the top strictly inside: impossible
        zuho

        have h0 : ztphp := Nat.pos_of_ne_zero hcon.1
        have h1 : ztmsx := hcon.2
        have hc := hbeta.1 hb
        apply up_not_corner hQ T (p := C.topIdx) zthex
          (by zuorr; exact (hvT _ hTm).symm)
        rw [iw_n, iw_vtx_left hL, iw_vtx_left hL,
          Nat.mod_eq_of_lt (show C.topIdx + 1 < Q.n by omega),
          show (C.topIdx + Q.n - 1) % Q.n = C.topIdx - 1 by
            rw [show C.topIdx + Q.n - 1 = ztbap + Q.n by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt by_omega],
          ← hvT _ by_omega, ← hvT _ by_omega]
        exact hc
      · omega
      omega
    omega
  · zumgs
    rcases C.sideS_mod C.sideBeta with ⟨hs, -⟩ | ⟨hs, hT0, hb⟩
    · omega
    · zubqb
      zuho

      have h1 : ztmsx := by_omega
      -- the reversed corner contains the up direction
      have hnc : ¬ sideCcw ztydq ztyy
          ztydr := fun h => by
        simp_all
      have hlo1 : ztxsv := by
        zufnq
      have hlo2 : (C.vertex ztbao).2 < C.top.2 := by
        zufnq
      have hor := up_in_one_corner (v := C.top) hrad hlo1 hlo2
      rw [← hup] at hor
      have hrev := hor.resolve_left hnc
      apply up_not_corner hQ T (p := C.m - C.topIdx) zthex
        (by rw [iw_vtx_right hL by_omega, show Q.n - 1 - (C.m - C.topIdx) = C.topIdx by omega];
            exact (hvT _ hTm).symm)
      rw [iw_n, iw_vtx_right hL ztcv,
        iw_vtx_right hL ztcv,
        Nat.mod_eq_of_lt (show C.m - C.topIdx + 1 < Q.n by omega),
        show (C.m - C.topIdx + Q.n - 1) % Q.n = C.m - C.topIdx - 1 by
          rw [show C.m - C.topIdx + Q.n - 1 = ztpwo + Q.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt by_omega],
        show Q.n - 1 - (C.m - C.topIdx + 1) = C.topIdx - 1 by omega,
        show Q.n - 1 - ztpwo = C.topIdx + 1 by omega,
        ← hvT _ by_omega, ← hvT _ by_omega]
      omega

/-- **The inner side is one run of the chain walk.** -/
theorem exists_shift (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q) :
    ∃ c₀ : ℕ, 6 ≤ c₀ ∧ c₀ + C.m ≤ 2 * C.m + 6 ∧
      ∀ j, j ≤ C.m → (C.sideWalk C.sideBeta).vtx zthie = (interiorWalk Q).vtx j := by
  zukdv
  zubb
  zufwr
  obtain ⟨hL1, hL2⟩ := sA_inner hQ T hD
  zucla
  · have hs := hL1 hL
    have hlin : ∀ j, j < C.m → tourA C C.sideBeta j = tourA C C.sideBeta 0 + j := by
      zun
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [TourA.tourA_succ by_omega by_omega, ih by_omega]; ring
    refine ⟨tourA C C.sideBeta 0 + 6, by_omega, ?_, fun j hj => ?_⟩
    · have := TourA.tourA_lt (C := C) (β := C.sideBeta) ztdfi
      grind
    · zuorr
      zufzy
      · rw [show j + (tourA C C.sideBeta 0 + 6) = tourA C C.sideBeta j + 6 by
          zuokk; ring, TourA.vtx_tourA hj, hvT j hj.le]
      · have e := TourA.vtx_tourA_succ (C := C) (β := C.sideBeta) (k := C.m - 1) by_omega
        rw [Nat.sub_add_cancel hm1, C.sideWalk_next_tour _ (TourA.tourA_lt _),
          hlin _ by_omega] at e
        grind
  · have hs := hL2 hL
    have hlin : ∀ j, j < C.m → tourB C C.sideBeta ztpwn = tourB C C.sideBeta ztdfi + j := by
      zun
      induction j with
      | zero => rfl
      | succ j ih =>
        have := TourB.tourB_succ (C := C) (β := C.sideBeta) (k := C.m - 1 - ztl) by_omega
          by_omega
        rw [show C.m - 1 - ztl + 1 = C.m - 1 - j by omega, ih by_omega] at this
        zvmwk; ring
    refine ⟨tourB C C.sideBeta ztdfi + 6, by_omega, ?_, fun j hj => ?_⟩
    · have := TourB.tourB_lt (C := C) (β := C.sideBeta) (C.m - 1 - ztdfi)
      rw [hlin _ by_omega] at this; omega
    · rw [iw_vtx_right hL by_omega]
      zufzy
      · rw [show j + (tourB C C.sideBeta ztdfi + 6) = tourB C C.sideBeta ztpwn + 6 by
          zuokk; ring, TourB.vtx_tourB by_omega,
          show C.m - 1 - j + 1 = Q.n - 1 - j by omega, hvT _ by_omega]
      · have e := TourB.vtx_tourB_succ (C := C) (β := C.sideBeta) (k := 0) by_omega
        rw [C.sideWalk_next_tour _ (TourB.tourB_lt _)] at e
        have h0 := hlin ztdfi by_omega
        grind
