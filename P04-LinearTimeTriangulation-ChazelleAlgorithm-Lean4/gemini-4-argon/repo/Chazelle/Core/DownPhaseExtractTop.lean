module

public import Chazelle.Core.DownPhaseExtractPiece

/-!
# WP-M (X, part 13): side `A` along an arc is contiguous

Along an arc of the region `R`, the chain edges of the host chain are consecutive walk edges of
side `A` of the tour (`tourA_arc`).  The tour of side `A` is split only at the tour start, which
is the top vertex when the slit leaves on side `A` (`sideBeta = true`).  That cannot be an inner
vertex of an arc (`top_not_inner`).  Otherwise the slit direction would be in the left sector of
the interior walk there, so points just above the top would lie in `R`, which lies below the top
(`region_below_top`).
-/

namespace Chazelle.Core

namespace Extract

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw)
open Chazelle.Geometry (lerp)
open DownHost
open ArcT (wrapK)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {g : ℕ}
  {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- The previous index modulo `n`. -/
theorem prev_mod {n a : ℕ} (hn : 0 < n) : ((a + 1) % n + n - 1) % n = a % n := by
  rw [← Nat.mod_add_mod a n 1]
  have hb := Nat.mod_lt a hn
  rcases Nat.lt_or_ge (a % n + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, show a % n + 1 + n - 1 = a % n + n by omega, Nat.add_mod_right,
      Nat.mod_mod]
  · have e : a % n + 1 = n := by omega
    rw [e, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The integer part of a wrapped integer key. -/
theorem wrapK_nat {n K : ℕ} (_hn : 0 < n) (hK : K < 2 * n) :
    wrapK n (K : ℝ) = ((K % n : ℕ) : ℝ) := by
  unfold wrapK
  split_ifs with h
  · have : K < n := by exact_mod_cast h
    rw [Nat.mod_eq_of_lt this]
  · push Not at h
    have : n ≤ K := by exact_mod_cast h
    rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]
    push_cast [this]; ring

/-- **The corner at an inner host key**: the chain corner there is positively scaled from the
corner of the interior walk at the walk vertex. -/
theorem corner_inner (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData (interiorModel Q) S R l r i_l d) {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    ∃ P : ℕ, P < (interiorModel Q).W.n ∧
      (P : ℝ) = wrapK (interiorModel Q).W.n (ukey (interiorModel Q) S R i_l j) ∧
      (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j) =
        (interiorModel Q).W.vtx P ∧
      ∀ y, sideLeftOf ((hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + (j - 1)))
          ((hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j))
          ((hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j + 1)) y ↔
        sideLeft (interiorModel Q).W P 0 y := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  have hdN : d < nk (interiorModel Q) S R := hA.hdN
  have hb0 := hostKeys_bounds (hk_mem (U := R) hM hF hfin hA.hil)
  have hn : 0 < (interiorModel Q).W.n := by
    have : (0 : ℝ) < (interiorModel Q).W.n := lt_of_le_of_lt hb0.1 hb0.2
    exact_mod_cast this
  obtain ⟨K, hK⟩ := ukey_inner_int X hA hj0 hjd
  obtain ⟨p, hpn, hp1, hp2, hv0, hv1, -⟩ := piece (g := g) (h3 := h3) X hA hjd
  obtain ⟨p', hpn', hp1', hp2', hv0', hv1', -⟩ :=
    piece (g := g) (h3 := h3) X hA (show j - 1 < d by omega)
  have hlt := ukey_mono (U := R) hM hF hfin hA.hil (Nat.lt_succ_self j) (by omega)
  have hlt' := ukey_mono (U := R) hM hF hfin hA.hil (show j - 1 < j by omega) (by omega)
  obtain ⟨hpK, hp'K⟩ := piece_inner K hK hp1 hp2 hlt hp1' hp2' hlt' hj0
  have hkm1 : kIdx (nk (interiorModel Q) S R) g i_l + (j - 1) + 1 =
      kIdx (nk (interiorModel Q) S R) g i_l + j := by omega
  rw [hkm1, Nat.sub_add_cancel hj0] at hv1'
  set k := kIdx (nk (interiorModel Q) S R) g i_l + j
  set v := (hostChain Q S R g h3).vertex k
  set W := (interiorModel Q).W
  have hv : v = W.vtx (p % W.n) := by
    rw [hv0, hK, hpK, sub_self, Chazelle.Geometry.lerp_zero]
  have hτ₁ : 0 < ukey (interiorModel Q) S R i_l (j + 1) - p := by rw [hpK, ← hK]; linarith
  have hnext : (hostChain Q S R g h3).vertex (k + 1) - v =
      (ukey (interiorModel Q) S R i_l (j + 1) - p) • (W.vtx ((p % W.n + 1) % W.n) - v) := by
    rw [hv1, hv0, hK, hpK, sub_self, ExtG.lerp_sub_lerp, sub_zero,
      Chazelle.Geometry.lerp_zero]
  have hvB : v = W.vtx ((p' % W.n + 1) % W.n) := by
    rw [hv1', hK, ← hp'K]
    push_cast
    rw [show (p' : ℝ) + 1 - p' = 1 by ring, Chazelle.Geometry.lerp_one]
  have hτ₀ : 0 < 1 - (ukey (interiorModel Q) S R i_l (j - 1) - p') := by
    have : ukey (interiorModel Q) S R i_l j = (p' : ℝ) + 1 := by rw [hK, ← hp'K]; push_cast; ring
    linarith
  have hprev : (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + (j - 1)) - v =
      (1 - (ukey (interiorModel Q) S R i_l (j - 1) - p')) • (W.vtx (p' % W.n) - v) := by
    have hB : v = lerp (W.vtx (p' % W.n)) (W.vtx ((p' % W.n + 1) % W.n)) 1 := by
      rwa [Chazelle.Geometry.lerp_one]
    rw [hv0', hB, ExtG.lerp_sub_lerp, Chazelle.Geometry.lerp_one]
    apply Prod.ext <;> simp <;> ring
  have hPn : p % W.n < W.n := Nat.mod_lt _ hn
  have hPprev : (p % W.n + W.n - 1) % W.n = p' % W.n := by
    have hpp : p = p' + 1 := by rw [hpK, hp'K]
    rw [hpp, prev_mod hn]
  refine ⟨p % W.n, hPn, ?_, hv, fun y => ?_⟩
  · have hK2 : K < 2 * W.n := by rwa [← hpK]
    rw [hK, wrapK_nat hn hK2, hpK]
  · rw [Chazelle.Chain.sideLeft_zero, hPprev, ← hv]
    exact ExtG.sideLeftOf_scale hτ₀ hτ₁ hprev hnext

/-- **The top vertex is not an inner vertex of an arc when the slit leaves on side `A`.** -/
theorem top_not_inner (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData (interiorModel Q) S R l r i_l d)
    {j : ℕ} (hj0 : 0 < j) (hjd : j < d)
    (hT : kIdx (nk (interiorModel Q) S R) g i_l + j = (hostChain Q S R g h3).topIdx)
    (hb : (hostChain Q S R g h3).sideBeta = true) : False := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  have hdN : d < nk (interiorModel Q) S R := hA.hdN
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec X.hQ
  obtain ⟨P, hPn, hPkey, hvP, hsec⟩ := corner_inner (g := g) (h3 := h3) X hA hj0 hjd
  set C := hostChain Q S R g h3
  set W := (interiorModel Q).W
  set k := kIdx (nk (interiorModel Q) S R) g i_l + j with hkdef
  set v := C.vertex k with hvdef
  -- the slit direction is in the left sector
  have hbeta := (C.sideBeta_eq_true_iff).1 hb
  have htop : C.top = v := by
    rw [hvdef, hT]; rfl
  have hslit : sideLeftOf (C.vertex (kIdx (nk (interiorModel Q) S R) g i_l + (j - 1))) v (C.vertex (k + 1)) C.slitTop := by
    have e1 : C.topIdx + 1 = k + 1 := by rw [← hT]
    have e2 : C.topIdx - 1 = kIdx (nk (interiorModel Q) S R) g i_l + (j - 1) := by
      rw [← hT, hkdef]; omega
    unfold sideLeftOf
    rwa [← e1, ← e2, ← htop]
  have hup : ∀ ε : ℝ, 0 < ε → sideLeft W P 0 (v + ε • (C.slitTop - v)) := by
    intro ε hε
    rw [← hsec]
    unfold sideLeftOf at hslit ⊢
    rw [add_sub_cancel_left]
    have := BoxT.sideCcw_smul one_pos hε one_pos (C.vertex (k + 1) - v) (C.slitTop - v)
      (C.vertex (kIdx (nk (interiorModel Q) S R) g i_l + (j - 1)) - v)
    rw [one_smul, one_smul] at this
    exact this.2 hslit
  -- the vertex position is inside the arc
  have hkey : (P : ℝ) + 0 = hk (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R) := by
    rw [add_zero, hPkey, wrapK_ukey hM hF hfin hA.hil (by omega)]
  have hin := (hA.inner j hj0 hjd).2
  rw [← hkey] at hin
  have hncut : ¬ (interiorModel Q).IsCut S (P + 0) := harc.2.2.2.2.2.1 _ hin
  have hfU : ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces P (0 + s * (1 - 0)) R := by
    filter_upwards [cyc_open hin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s h1 hs1
    rw [zero_add, sub_zero, mul_one]
    rw [add_zero] at h1
    exact harc.2.2.2.2.2.2 P s hPn hs1.1 hs1.2 h1
  obtain ⟨r₀, hr₀, hnear⟩ := Loc.near_sub_region X.hQ hF hfin hPn le_rfl zero_lt_one hncut X.hR hfU
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hPn le_rfl zero_lt_one
  have hvP' : sidePt W P 0 = v := by rw [Chazelle.Chain.sidePt_zero, ← hvP]
  -- a point just above the top in `R`
  have hrad : v.2 < C.radius := by rw [← htop]; exact C.top_snd_lt_radius
  set ε := min r₀ rC / (2 * (C.radius - v.2)) with hε
  have hε0 : 0 < ε := div_pos (lt_min hr₀ hrC) (by linarith)
  set y := v + ε • (C.slitTop - v)
  have hy2 : y.2 = v.2 + ε * (C.radius - v.2) := by
    show (v + ε • (C.slitTop - v)).2 = _
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    rfl
  have hy1 : y.1 = v.1 := by
    show (v + ε • (C.slitTop - v)).1 = _
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    rw [show C.slitTop.1 = C.top.1 from rfl, htop]
    ring
  have hpos : 0 < ε * (C.radius - v.2) := mul_pos hε0 (by linarith)
  have hdist : dist y v = min r₀ rC / 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy1, hy2, sub_self, abs_zero,
      show v.2 + ε * (C.radius - v.2) - v.2 = ε * (C.radius - v.2) by ring,
      abs_of_pos hpos, max_eq_right hpos.le, hε]
    have : C.radius - v.2 ≠ 0 := by linarith
    field_simp
  have hyb₀ : y ∈ ball (sidePt W P 0) r₀ := by
    rw [hvP', mem_ball, hdist]; have := min_le_left r₀ rC; linarith
  have hybC : y ∈ ball (sidePt W P 0) rC := by
    rw [hvP', mem_ball, hdist]; have := min_le_right r₀ rC; linarith
  have hyD : y ∈ (interiorModel Q).D := by
    by_contra hyD
    exact hclean y hybC (by rwa [hWb, hWf]) (hup ε hε0)
  have hyR := hnear y hyb₀ hyD
  have := region_below_top (g := g) (h3 := h3) X.hQ X.hFam X.hne X.hR y hyR
  rw [htop, hy2] at this
  linarith

/-- **No split of side `A` inside an arc.** -/
theorem no_split (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData (interiorModel Q) S R l r i_l d)
    {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    kIdx (nk (interiorModel Q) S R) g i_l + j ≠
      TourA.sA (hostChain Q S R g h3) (hostChain Q S R g h3).sideBeta := by
  set C := hostChain Q S R g h3
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    (fun j hj0 hjd => (hA.inner j hj0 hjd).2) hA.gaps
  have hm : C.m = nk (interiorModel Q) S R - 1 := rfl
  have hwrap' : kIdx (nk (interiorModel Q) S R) g i_l + d ≤ C.m := by
    rw [hm]; unfold kIdx; exact hwrap
  have hTm := C.topIdx_le
  unfold TourA.sA
  rcases C.sideS_mod C.sideBeta with ⟨hs, hc⟩ | ⟨hs, hT0, -⟩
  · rw [hs]
    rcases hc with hb | hT | hT
    · exact fun hT => top_not_inner X harc hA hj0 hjd hT hb
    · omega
    · omega
  · rw [hs]; omega

/-- **Side `A` along an arc is contiguous.** -/
theorem tourA_arc (X : Ctx Q S R) (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hA : ArcData (interiorModel Q) S R l r i_l d)
    {j : ℕ} (hj : j < d) :
    TourA.tourA (hostChain Q S R g h3) (hostChain Q S R g h3).sideBeta
        (kIdx (nk (interiorModel Q) S R) g i_l + j) =
      TourA.tourA (hostChain Q S R g h3) (hostChain Q S R g h3).sideBeta
        (kIdx (nk (interiorModel Q) S R) g i_l) + j := by
  set C := hostChain Q S R g h3
  have hwrap := arc_chain X.hQ X.hFam hg hgc harc hA.hil hA.hd0 hA.hdN hA.hr
    (fun j hj0 hjd => (hA.inner j hj0 hjd).2) hA.gaps
  have hm : C.m = nk (interiorModel Q) S R - 1 := rfl
  have hwrap' : kIdx (nk (interiorModel Q) S R) g i_l + d ≤ C.m := by
    rw [hm]; unfold kIdx; exact hwrap
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show kIdx (nk (interiorModel Q) S R) g i_l + (j + 1) =
      kIdx (nk (interiorModel Q) S R) g i_l + j + 1 by ring,
      TourA.tourA_succ (C := C) (β := C.sideBeta) (k := kIdx (nk (interiorModel Q) S R) g i_l + j)
        (by have := C.one_le; omega)
        (show kIdx (nk (interiorModel Q) S R) g i_l + j + 1 ≠ _ from
          no_split (h3 := h3) X hg hgc harc hA (j := j + 1) (by omega) hj),
      ih (by omega)]
    ring

end

end Extract

end Chazelle.Core
