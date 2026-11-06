module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseExtractTop

/-!
# WP-M (X, part 14): the key correspondence along an arc

For an arc `(l, r)` of the region `R` and the host chain `C = hostChain Q S R g` of a chord gap
`g`, the piecewise linear key map `kmap` (breakpoints: the unwrapped host keys of the arc, image:
the side-`A` run of the arc on the chain walk) is an arc correspondence (`ArcT.ArcCorr`, result
`arcCorr`) between the chain model with any admissible family `F₁` and the interior model with
`S ∪ kept R F₁`.  Here the kept chords are those of `F₁` meeting `R`.

* The points of corresponding positions agree, and their left sectors are positively scaled
  (`pos_data`, `corner_inner`).
* A chord of `F₁` attached on side `A` is attached at the corresponding interior position, and it
  meets `R` there (`kept_of_attach`), so it is kept.
* Offsets agree up to a positive scaling, so facing transfers.
-/

namespace Chazelle.Core

namespace Extract

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset)
open Chazelle.Visibility (hseg)
open DownHost
open ArcT (wrapK NonVtx)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {g : ℕ}
  {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The kept chords** of a chain family: those meeting the region. -/
def kept (R : Set Point) (F₁ : Set (Set Point)) : Set (Set Point) :=
  {c | c ∈ F₁ ∧ (c ∩ R).Nonempty}

section
variable (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (g : ℕ) (h3 : 3 ≤ nk (interiorModel Q) S R)
include Q S R g h3
/-- The chain walk key of the start of the side-`A` run of an arc. -/
noncomputable def cStart (i_l : ℕ) : ℕ :=
  TourA.tourA (hostChain Q S R g h3) (hostChain Q S R g h3).sideBeta
    (kIdx (nk (interiorModel Q) S R) g i_l) + 6

/-- **The key map of an arc.** -/
noncomputable def kmap (i_l d : ℕ) : ℝ → ℝ :=
  ArcT.brk (ukey (interiorModel Q) S R i_l) d (cStart Q S R g h3 i_l : ℝ)


end

theorem brkInc (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData (interiorModel Q) S R l r i_l d) :
    ArcT.BrkInc (ukey (interiorModel Q) S R i_l) d := fun j hj =>
  ukey_mono (U := R) X.walkAx X.hFam.2.1 X.hFam.1 hA.hil (Nat.lt_succ_self j)
    (by have := hA.hdN; omega)

/-- **The keys just after a position inside an arc face the region.** -/
theorem faces_after {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r (p + t)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces p (t + s * (1 - t)) R := by
  have h1 := (Loc.tendsto_mul_const_nhdsGT (show 0 < 1 - t by linarith)).eventually
    (cyc_open hin)
  filter_upwards [h1, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s h1 hs1
  have hs0 : 0 < s := hs1.1
  refine harc.2.2.2.2.2.2 p _ hp (by nlinarith) (by nlinarith [hs1.2]) ?_
  grind

/-- A point of a horizontal segment near a given point of it. -/
theorem exists_near_mem {y₀ a b : ℝ} (hab : a < b) {P : Point} (hP : P ∈ hseg y₀ a b) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ y ∈ hseg y₀ a b, y ≠ P ∧ dist y P < ρ := by
  obtain ⟨hP2, hPa, hPb⟩ := hP
  rcases hPb.lt_or_eq with hPb | hPb
  · set ε := min (b - P.1) ρ / 2 with hεd
    have hε0 : 0 < ε := by simp_all
    have hε1 : ε < b - P.1 := by
      grind
    have hε2 : ε < ρ := by
      grind
    refine ⟨(P.1 + ε, y₀), ⟨rfl, by linarith, by linarith⟩, fun e => ?_, ?_⟩
    · grind
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      grind
  · 
    set ε := min (P.1 - a) ρ / 2 with hεd
    have hε0 : 0 < ε := by simp_all
    have hε1 : ε < P.1 - a := by
      grind
    
    refine ⟨(P.1 - ε, y₀), ⟨rfl, by linarith, by linarith⟩, fun e => ?_, ?_⟩
    all_goals (grind [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, abs_neg])

/-- **A chord attached at a position inside an arc meets the region.** -/
theorem kept_of_attach (X : Ctx Q S R) {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r)
    {c : Set Point} (hc : ∃ y₀ a b : ℝ, a < b ∧ c = hseg y₀ a b) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r (p + t)) (hA₂ : SideAttach (interiorModel Q).W c p t) :
    (c ∩ R).Nonempty := by
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec X.hQ
  have hncut : ¬ (interiorModel Q).IsCut S (p + t) := harc.2.2.2.2.2.1 _ hin
  obtain ⟨r₀, hr₀, hnear⟩ := Loc.near_sub_region X.hQ hF hfin hp ht0 ht1 hncut X.hR
    (faces_after harc hp ht0 ht1 hin)
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hp ht0 ht1
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA₂
  obtain ⟨y₀, a, b, hab, rfl⟩ := hc
  set ρ := min rA (min r₀ rC)
  have hρ : 0 < ρ := lt_min hrA (lt_min hr₀ hrC)
  obtain ⟨y, hyc, hne, hyd⟩ := exists_near_mem hab hmem hρ
  have hyA : dist y (sidePt (interiorModel Q).W p t) < rA :=
    lt_of_lt_of_le hyd (min_le_left _ _)
  have hy₀ : y ∈ ball (sidePt (interiorModel Q).W p t) r₀ :=
    lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hyC : y ∈ ball (sidePt (interiorModel Q).W p t) rC :=
    lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_right _ _))
  have hyl := hsec y hyc hne hyA
  have hyD : y ∈ (interiorModel Q).D := by
    by_contra hyD
    exact hclean y hyC (by rw [hWb, hWf]; exact hyD) hyl
  exact ⟨y, hyc, hnear y hy₀ hyD⟩

section
variable (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R) (hgc : ChordGap (interiorModel Q) S R g) {l r : ℝ} {i_l d : ℕ} (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData (interiorModel Q) S R l r i_l d)
include X hg hgc l r harc hA
/-- **The positions of an arc key**: its piece `j`, its interior walk edge `p` (mod `n`), its
chain walk edge and parameter. -/
theorem pos_data
    {x : ℝ} (hx : x ∈ Ioo (ukey (interiorModel Q) S R i_l 0) (ukey (interiorModel Q) S R i_l d)) :
    ∃ j p : ℕ, j < d ∧ p < 2 * (interiorModel Q).W.n ∧
      (p : ℝ) ≤ ukey (interiorModel Q) S R i_l j ∧ ukey (interiorModel Q) S R i_l j ≤ x ∧
      x < ukey (interiorModel Q) S R i_l (j + 1) ∧
      ukey (interiorModel Q) S R i_l (j + 1) ≤ p + 1 ∧
      ⌊kmap Q S R g h3 i_l d x⌋₊ = TourA.tourA (hostChain Q S R g h3)
        (hostChain Q S R g h3).sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6 ∧
      kmap Q S R g h3 i_l d x - ⌊kmap Q S R g h3 i_l d x⌋₊ =
        (x - ukey (interiorModel Q) S R i_l j) /
          (ukey (interiorModel Q) S R i_l (j + 1) - ukey (interiorModel Q) S R i_l j) ∧
      (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j) =
        lerp ((interiorModel Q).W.vtx (p % (interiorModel Q).W.n))
          ((interiorModel Q).W.vtx ((p % (interiorModel Q).W.n + 1) % (interiorModel Q).W.n))
          (ukey (interiorModel Q) S R i_l j - p) ∧
      (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j + 1) =
        lerp ((interiorModel Q).W.vtx (p % (interiorModel Q).W.n))
          ((interiorModel Q).W.vtx ((p % (interiorModel Q).W.n + 1) % (interiorModel Q).W.n))
          (ukey (interiorModel Q) S R i_l (j + 1) - p) ∧
      wrapK (interiorModel Q).W.n x = (((p % (interiorModel Q).W.n : ℕ)) : ℝ) + (x - p) := by
  have hinc := brkInc X hA
  have hd1 : 1 ≤ d := hA.hd0
  obtain ⟨hjd, hj1, hj2⟩ := ArcT.seg_spec hinc hd1 hx.1.le hx.2
  obtain ⟨p, hpn, hp1, hp2, hv0, hv1, -⟩ := piece (g := g) (h3 := h3) X hA hjd
  
  have hwn : 0 < (interiorModel Q).W.n := by
    omega
  have hlt : ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x) <
      ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x + 1) := by
    linarith
  have hκ : kmap Q S R g h3 i_l d x = (cStart Q S R g h3 i_l : ℝ) +
      (ArcT.seg (ukey (interiorModel Q) S R i_l) d x : ℕ) +
      (x - ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) /
        (ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x + 1) -
          ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) := rfl
  have hf0 : 0 ≤ (x - ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) /
      (ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x + 1) -
        ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) :=
    div_nonneg (by linarith) (by linarith)
  have hf1 : (x - ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) /
      (ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x + 1) -
        ukey (interiorModel Q) S R i_l (ArcT.seg (ukey (interiorModel Q) S R i_l) d x)) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hfl : ⌊kmap Q S R g h3 i_l d x⌋₊ =
      cStart Q S R g h3 i_l + ArcT.seg (ukey (interiorModel Q) S R i_l) d x := by
    rw [hκ, Nat.floor_eq_iff (by positivity)]
    grind
  have htour := tourA_arc (h3 := h3) X hg hgc harc hA hjd
  refine ⟨ArcT.seg (ukey (interiorModel Q) S R i_l) d x, p, hjd, hpn, hp1, hj1, hj2, hp2, ?_, ?_,
    hv0, hv1, wrapK_edge hwn hpn (le_trans hp1 hj1) (lt_of_lt_of_le hj2 hp2)⟩
  · rw [hfl, htour]; unfold cStart; ring
  · rw [hfl, hκ]; grind

/-- **The key correspondence of an arc** (`ArcT.ArcCorr`). -/
theorem arcCorr
    {F₁ : Set (Set Point)} (hF₁ : F₁ ⊆ (chainModel (hostChain Q S R g h3)).Adm)
    {U V : Set Point} (hVU : V ⊆ U) :
    ArcT.ArcCorr (chainModel (hostChain Q S R g h3)) (interiorModel Q) F₁ (S ∪ kept R F₁) U V
      (ukey (interiorModel Q) S R i_l 0) (ukey (interiorModel Q) S R i_l d)
      (kmap Q S R g h3 i_l d) := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  have hdN : d < nk (interiorModel Q) S R := hA.hdN
  have hd1 : 1 ≤ d := hA.hd0
  have hinc := brkInc X hA
  have hl0 : ukey (interiorModel Q) S R i_l 0 = l := by rw [ukey_zero hA.hil, hA.hl]
  have hlb : 0 ≤ l ∧ l < (interiorModel Q).W.n :=
    hA.hl ▸ hostKeys_bounds (hk_mem (U := R) hM hF hfin hA.hil)
  have hrb : 0 ≤ r ∧ r < (interiorModel Q).W.n :=
    hA.hr ▸ hostKeys_bounds (hk_mem (U := R) hM hF hfin (Nat.mod_lt _ (by omega)))
  have hwn : 0 < (interiorModel Q).W.n := by
    have : (0 : ℝ) < (interiorModel Q).W.n := lt_of_le_of_lt hlb.1 hlb.2
    simp_all
  have hP : (hostChain Q S R g h3).P.Simple := hostPts_simple X.hQ X.hFam X.hne X.hR
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    (fun j hj0 hjd => (hA.inner j hj0 hjd).2) hA.gaps
  have hwrap' : kIdx (nk (interiorModel Q) S R) g i_l + d ≤ (hostChain Q S R g h3).m := by
    show _ ≤ nk (interiorModel Q) S R - 1
    omega_nf
  have hbot : kmap Q S R g h3 i_l d (ukey (interiorModel Q) S R i_l 0) =
      (cStart Q S R g h3 i_l : ℝ) := ArcT.brk_bot hinc hd1
  have htop : kmap Q S R g h3 i_l d (ukey (interiorModel Q) S R i_l d) =
      (cStart Q S R g h3 i_l : ℝ) + d := ArcT.brk_top hinc hd1
  have hmono : StrictMonoOn (kmap Q S R g h3 i_l d)
      (Icc (ukey (interiorModel Q) S R i_l 0) (ukey (interiorModel Q) S R i_l d)) :=
    ArcT.brk_strictMonoOn hinc hd1
  have hcs : cStart Q S R g h3 i_l + d ≤ 2 * (hostChain Q S R g h3).m + 6 := by
    have h1 := tourA_arc (h3 := h3) X hg hgc harc hA (show d - 1 < d by omega)
    have h2 := TourA.tourA_lt (C := hostChain Q S R g h3) (β := (hostChain Q S R g h3).sideBeta)
      (kIdx (nk (interiorModel Q) S R) g i_l + (d - 1))
    unfold cStart; omega
  have hn₁ : (chainModel (hostChain Q S R g h3)).W.n = 2 * (hostChain Q S R g h3).m + 7 :=
    Chain.sideWalk_n _ _
  have hlr' : unwrapK (interiorModel Q).W.n l l < unwrapK (interiorModel Q).W.n l r := by
    rw [unwrapK_self, ← hA.hud, ← hl0]
    exact ukey_mono hM hF hfin hA.hil hA.hd0 hdN
  -- the interior position of a key of the arc lies inside the arc
  have hinarc : ∀ x ∈ Ioo (ukey (interiorModel Q) S R i_l 0) (ukey (interiorModel Q) S R i_l d),
      sideInArc l r (wrapK (interiorModel Q).W.n x) := by
    intro x hx
    rw [hl0, hA.hud] at hx
    have hx0 : 0 ≤ x := le_trans hlb.1 hx.1.le
    have hxl : x < l + (interiorModel Q).W.n := lt_trans hx.2 (unwrapK_bounds hlb hrb).2
    have hx2 : x < 2 * ((interiorModel Q).W.n : ℝ) := by grind
    have hw0 := ArcT.wrapK_nonneg (n := ((interiorModel Q).W.n : ℝ)) hx0 hx2
    have hwl := ArcT.wrapK_lt (show (0 : ℝ) < (interiorModel Q).W.n by grind) hx0 hx2
    rw [cyc_unwrap hlb hlb hrb ⟨hw0, hwl⟩ hlr', unwrapK_self,
      unwrapK_wrapK hlb.1 (by grind) hx.1.le hxl]
    exact hx
  refine ⟨?_, ?_, ?_, hmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · rw [hA.hud, hl0]; exact (unwrapK_bounds hlb hrb).2.le
  · -- range
    intro x hx
    have h1 := hmono.monotoneOn ⟨le_rfl, le_trans hx.1 hx.2⟩ hx hx.1
    have h2 := hmono.monotoneOn hx ⟨le_trans hx.1 hx.2, le_rfl⟩ hx.2
    rw [hbot] at h1
    rw [htop] at h2
    refine ⟨le_trans (Nat.cast_nonneg _) h1, lt_of_le_of_lt h2 ?_⟩
    rw [hn₁]
    exact_mod_cast (show cStart Q S R g h3 i_l + d < 2 * (hostChain Q S R g h3).m + 7 by omega)
  · -- onto
    intro y h1 h2
    rw [hbot] at h1
    rw [htop] at h2
    exact ArcT.brk_onto hinc hd1 h1 h2
  · -- vertices to vertices
    intro x hx hv k hk
    obtain ⟨j, hj, rfl⟩ := (ArcT.brk_int_iff hinc hd1 (c₀ := cStart Q S R g h3 i_l) hx.1.le
      hx.2).1 ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact lt_irrefl _ hx.1
    · obtain ⟨K, hK⟩ := ukey_inner_int X hA h0 hj
      exact hv K hK
  · -- vertex keys to vertex keys
    intro x hx hnv hnv'
    simp only [NonVtx, not_forall, not_not] at hnv
    obtain ⟨K, hK⟩ := hnv
    have hx' := hx
    rw [hl0, hA.hud] at hx'
    have hx0 : 0 ≤ x := le_trans hlb.1 hx'.1.le
    have hxl : x < l + (interiorModel Q).W.n := lt_trans hx'.2 (unwrapK_bounds hlb hrb).2
    have hx2 : x < 2 * ((interiorModel Q).W.n : ℝ) := by grind
    have hw0 := ArcT.wrapK_nonneg (n := ((interiorModel Q).W.n : ℝ)) hx0 hx2
    have hwl := ArcT.wrapK_lt (show (0 : ℝ) < (interiorModel Q).W.n by grind) hx0 hx2
    have hK2 : K < 2 * (interiorModel Q).W.n := by
      have : (K : ℝ) < ((2 * (interiorModel Q).W.n : ℕ) : ℝ) := by grind
      exact_mod_cast this
    obtain ⟨j, hj0, hjd, hjx⟩ := hA.vtx _ hw0 hwl (hinarc x hx)
      ⟨K % (interiorModel Q).W.n, by rw [hK, wrapK_nat hwn hK2]⟩
    have hu : ukey (interiorModel Q) S R i_l j = x := by
      rw [ukey_eq_unwrap hM hF hfin hA.hil (by omega), hA.hl, hjx,
        unwrapK_wrapK hlb.1 (by grind) hx'.1.le hxl]
    obtain ⟨k, hk⟩ := (ArcT.brk_int_iff hinc hd1 (c₀ := cStart Q S R g h3 i_l) hx.1.le
      hx.2).2 ⟨j, hjd, hu.symm⟩
    exact hnv' k hk
  · -- cuts
    rintro x hx ⟨c, hc, p₁, t₁, hA₁, he⟩
    obtain ⟨j, p, hjd, hpn, hp1, hj1, hj2, hp2, hfl, hfr, hv0, hv1, hwr⟩ :=
      pos_data (h3 := h3) X hg hgc harc hA hx
    set W := (interiorModel Q).W with hW
    set C := hostChain Q S R g h3 with hC
    set s := (x - ukey (interiorModel Q) S R i_l j) /
      (ukey (interiorModel Q) S R i_l (j + 1) - ukey (interiorModel Q) S R i_l j) with hs
    have hjj : ukey (interiorModel Q) S R i_l j < ukey (interiorModel Q) S R i_l (j + 1) := by
      linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hs1 : s < 1 := by rw [hs, div_lt_one (by linarith)]; linarith
    have hkm : kIdx (nk (interiorModel Q) S R) g i_l + j < C.m := by omega
    -- the chain position
    have hkey : ((p₁ : ℕ) : ℝ) + t₁ =
        ((TourA.tourA C C.sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6 : ℕ) : ℝ) + s := by
      rw [← he, ← hfl, ← hfr]; ring
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA₁.2.1 hA₁.2.2.1 hs0 hs1 hkey
    -- the interior position
    set p₂ := p % W.n with hp₂
    set t₂ := x - p with ht₂
    have hp₂n : p₂ < W.n := Nat.mod_lt _ hwn
    have ht₂0 : 0 ≤ t₂ := by grind
    have ht₂1 : t₂ < 1 := by grind
    have hpar : t₂ = (ukey (interiorModel Q) S R i_l j - p) +
        s * (ukey (interiorModel Q) S R i_l (j + 1) - ukey (interiorModel Q) S R i_l j) := by
      have hne : ukey (interiorModel Q) S R i_l (j + 1) - ukey (interiorModel Q) S R i_l j ≠ 0 :=
        sub_ne_zero.2 hjj.ne'
      grind
    -- the points agree
    have hpt : sidePt W p₂ t₂ = sidePt (C.sideWalk C.sideBeta)
        (TourA.tourA C C.sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6) s := by
      rw [TourA.sidePt_tourA hkm, hv0, hv1, lerp_lerp]
      unfold sidePt
      grind
    -- the sectors agree
    have hsec : ∀ y, sideLeft (C.sideWalk C.sideBeta)
        (TourA.tourA C C.sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6) s y →
        sideLeft W p₂ t₂ y := by
      intro y hy
      rcases hs0.lt_or_eq with hs0' | hs0'
      · -- inside a piece
        have ht₂0' : 0 < t₂ := by grind
        rw [TourA.sideLeft_tourA_edge hP hkm ⟨hs0', hs1⟩, hv0, hv1, ExtG.det_lerp_pair] at hy
        rw [Chazelle.Chain.sideLeft_edge (hM.nd p₂ hp₂n) ⟨ht₂0', ht₂1⟩]
        have hτ : 0 < ukey (interiorModel Q) S R i_l (j + 1) - p -
            (ukey (interiorModel Q) S R i_l j - p) := by linarith
        exact pos_of_mul_pos_right hy hτ.le
      · -- at an inner host key
        have hxj : x = ukey (interiorModel Q) S R i_l j := by
          grind
        have hj0 : 0 < j := by
          by_contra h0; push Not at h0
          have : j = 0 := by omega
          simp_all
        obtain ⟨P, hPn, hPkey, hvP, hcorner⟩ := corner_inner (g := g) (h3 := h3) X hA hj0 hjd
        have hP₂ : p₂ = P ∧ t₂ = 0 := by
          have e : ((p₂ : ℕ) : ℝ) + t₂ = ((P : ℕ) : ℝ) + 0 := by
            grind
          exact Chazelle.Chain.sideKey_inj ht₂0 ht₂1 le_rfl zero_lt_one e
        rw [← hs0'] at hy
        rw [TourA.sideLeft_tourA_vtx (by omega) hkm
          (no_split (h3 := h3) X hg hgc harc hA hj0 hjd)] at hy
        rw [hP₂.1, hP₂.2, ← hcorner]
        rwa [show kIdx (nk (interiorModel Q) S R) g i_l + j - 1 =
          kIdx (nk (interiorModel Q) S R) g i_l + (j - 1) by omega] at hy
    have hA₂ : SideAttach W c p₂ t₂ :=
      ExtG.attach_of_sector hpt hsec hp₂n ht₂0 ht₂1 hA₁
    -- the chord meets `R`
    have hcsh : ∃ y₀ a b : ℝ, a < b ∧ c = hseg y₀ a b := by
      obtain ⟨y₀, a, b, hh, -, e⟩ := hF₁ hc
      exact ⟨y₀, a, b, hh.lt, e⟩
    have hin2 : sideInArc l r (p₂ + t₂) := by rw [← hwr]; exact hinarc x hx
    have hmeet := kept_of_attach X harc hcsh hp₂n ht₂0 ht₂1 hin2 hA₂
    exact ⟨c, Or.inr ⟨hc, hmeet⟩, p₂, t₂, hA₂, hwr⟩
  · -- faces
    intro x hx hv hfa
    obtain ⟨j, p, hjd, hpn, hp1, hj1, hj2, hp2, hfl, hfr, hv0, hv1, hwr⟩ :=
      pos_data (h3 := h3) X hg hgc harc hA hx
    set W := (interiorModel Q).W with hW
    set C := hostChain Q S R g h3 with hC
    have hjj : ukey (interiorModel Q) S R i_l j < ukey (interiorModel Q) S R i_l (j + 1) := by
      linarith
    have hkm : kIdx (nk (interiorModel Q) S R) g i_l + j < C.m := by omega
    -- a non-vertex key is inside a piece
    have hxj : ukey (interiorModel Q) S R i_l j < x := by
      rcases hj1.lt_or_eq with h | h
      · exact h
      · exfalso
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0] at h; simp_all
        · obtain ⟨K, hK⟩ := ukey_inner_int X hA h0 hjd
          exact hv K (by rw [← h, hK])
    set t₂ := x - p with ht₂
    have ht₂0 : 0 ≤ t₂ := by grind
    have ht₂1 : t₂ < 1 := by grind
    have hfl2 : ⌊wrapK W.n x⌋₊ = p % W.n := by rw [hwr]; exact floor_add ht₂0 ht₂1
    have hfr2 : wrapK W.n x - ⌊wrapK W.n x⌋₊ = t₂ := by grind
    rw [hfr2, hfl2] at hfa
    rw [hfr, hfl]
    refine ExtG.faces_of_offset (c := ukey (interiorModel Q) S R i_l (j + 1) - p -
      (ukey (interiorModel Q) S R i_l j - p)) (by linarith) (fun δ => ?_) hVU hfa
    show Chazelle.Jordan.offset ((C.sideWalk C.sideBeta).vtx
        (TourA.tourA C C.sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6))
      ((C.sideWalk C.sideBeta).vtx
        ((TourA.tourA C C.sideBeta (kIdx (nk (interiorModel Q) S R) g i_l + j) + 6 + 1) %
          (C.sideWalk C.sideBeta).n)) _ δ = _
    rw [TourA.vtx_tourA hkm, TourA.vtx_tourA_succ hkm, hv0, hv1, ExtG.offset_lerp_pair]
    congr 1
    have hne : ukey (interiorModel Q) S R i_l (j + 1) - ukey (interiorModel Q) S R i_l j ≠ 0 :=
      sub_ne_zero.2 hjj.ne'
    grind
  · -- counted
    intro x hx _
    obtain ⟨j, p, hjd, -, -, -, -, -, hfl, -⟩ := pos_data (h3 := h3) X hg hgc harc hA hx
    rw [hfl]
    exact TourA.counted_tourA _


end

end

end Extract

end Chazelle.Core
