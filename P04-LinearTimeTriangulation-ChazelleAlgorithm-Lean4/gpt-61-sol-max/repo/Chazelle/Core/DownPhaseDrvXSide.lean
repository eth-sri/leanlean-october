module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvXCtx
public import Chazelle.Core.DownPhaseDrvXWalk

/-!
# Down phase, extraction (D6): chain walk positions and the host polygon

In the context `XCtx`, host point `k` of the region host is the vertex `sig k` of the host polygon
`G = hostPoly Q S R` (counterclockwise, interior `R`).  The tour of the chain walk runs over the
host points; the side whose direction is that of `G` (side `A` iff `li`) is the **inner** side.

* `inner_edge`, `inner_vtx`: at a regular inner position the chain walk position is a position of
  `G` with the same point, and its left sector lies in that of `G`;
* `outer_edge`, `outer_vtx`: at a regular outer position the left sector is disjoint from that of
  `G` at the same point;
* `box_ne`: box and slit positions are not points of `G`;
* `meet_of_attach`: a chord attached to `G` meets `R`.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set DownHost DownMath
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw)
open Chazelle.Geometry (lerp)
open BuildNF (buildNF)
open DrvR (regHost)

/-- The host key index of host point `k`. -/
def sig (li : Bool) (K i0 k : ℕ) : ℕ := (i0 + rho li K k) % K

theorem sig_lt (li : Bool) {K : ℕ} (hK : 0 < K) (i0 k : ℕ) : sig li K i0 k < K := Nat.mod_lt _ hK

section
variable {li : Bool} {K i0 k : ℕ} (hk : k < K)
include hk
/-- The next host point along the inner side is the next host key. -/
theorem sig_next (hn : kNext li k < K)
    (h0 : li = false → 1 ≤ k) : sig li K i0 (kNext li k) = (sig li K i0 k + 1) % K := by
  unfold sig rho kNext
  grind

/-- The previous host point along the inner side is the previous host key. -/
theorem sig_prev (hp : kPrev li k < K)
    (h0 : li = true → 1 ≤ k) : sig li K i0 (kPrev li k) = (sig li K i0 k + K - 1) % K := by
  unfold sig rho kPrev
  unfold kPrev at hp
  rw [show (i0 + (if li = true then k else K - 1 - k)) % K + K - 1 =
    (i0 + (if li = true then k else K - 1 - k)) % K + (K - 1) by omega, Nat.mod_add_mod]
  cases li
  · simp only [Bool.false_eq_true, ite_false] at hp ⊢
    rw [show i0 + (K - 1 - k) + (K - 1) = i0 + (K - 1 - (k + 1)) + K by omega, Nat.add_mod_right]
  · have := h0 rfl
    simp only [ite_true] at hp ⊢
    rw [show i0 + k + (K - 1) = i0 + (k - 1) + K by omega, Nat.add_mod_right]


end

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF} {i0 g : ℕ}

set_option quotPrecheck false in
local notation "xS" => (buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
  (Qof P)
set_option quotPrecheck false in
local notation "xK" => nk (interiorModel (Qof P)) xS (reg r)
set_option quotPrecheck false in
local notation "xG" => hostPoly (Qof P) xS (reg r)

theorem det_neg_of {a b x : Point} (h1 : 0 < det a b x) (h2 : 0 < det b a x) : False := by
  grind [Chazelle.Geometry.det_swap12]

namespace XCtx

variable (Y : XCtx P li L E reg r C NR i0 g)
include Y

theorem three : 3 ≤ xK := three_le_nk Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR

theorem hm : C.m = xK - 1 := by have := Y.X.hCm; have := Y.hn; omega

theorem gSimple : (xG).Simple := hostPts_simple Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR

omit Y in
theorem gn (_Y : XCtx P li L E reg r C NR i0 g) : (xG).n = xK := hostPoly_n

theorem cpSimple : C.P.Simple := Y.hfacts.1

/-- Host point `k` is the vertex `sig k` of the host polygon. -/
theorem vtx_sig {k : ℕ} (hk : k < xK) : C.P.vtx k = (xG).vtx (sig li xK i0 k) := Y.hvtx k hk

omit Y in
/-- The tour edge `p` joins host points `tK p` and `kNext (tK p)` (in range). -/
theorem kn_le (_Y : XCtx P li L E reg r C NR i0 g) {p : ℕ} :
    kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m)) (tK C.m C.topIdx C.sideBeta p) ≤ C.m ∧
      (decide (tU C.m C.topIdx C.sideBeta p < C.m) = false → 1 ≤ tK C.m C.topIdx C.sideBeta p) := by
  have hm1 := C.one_le
  have hu := tU_lt (T := C.topIdx) C.sideBeta hm1 p
  unfold kNext
  by_cases h : tU C.m C.topIdx C.sideBeta p < C.m
  · rw [decide_eq_true h, tK_eq_of_lt h]; simp_all
  · rw [decide_eq_false h, tK_eq_of_ge (not_lt.1 h)]
    grind

section
variable {p : ℕ} (h6 : 6 ≤ p)
include h6
/-- **Inner position inside a tour edge**: a position of `G` with the same left half-plane. -/
theorem inner_edge (hp : p < 2 * C.m + 6) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = li) :
    sidePt (C.sideWalk C.sideBeta) p t = sidePt xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) t ∧
      ∀ x, sideLeft (C.sideWalk C.sideBeta) p t x ↔
        sideLeft xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) t x := by
  have hm := Y.hm
  have h3 := Y.three
  obtain ⟨hkn, hk1⟩ := Y.kn_le (p := p)
  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp.le
  have hv1 := walk_next Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  have hse := walk_sector_edge Y.cpSimple Y.X.hCs Y.X.hCm C.sideBeta h6 hp ht
  generalize tK C.m C.topIdx C.sideBeta p = kc at hkn hk1 hkc_le hv0 hv1 hse ⊢
  rw [hA] at hkn hk1 hv1 hse
  have hsn := sig_next (i0 := i0) (show kc < xK by omega) (show kNext li kc < xK by omega) hk1
  rw [Y.vtx_sig (by omega)] at hv0
  rw [Y.vtx_sig (by omega), hsn] at hv1
  have hne : (xG).vtx (sig li xK i0 kc) ≠ (xG).vtx ((sig li xK i0 kc + 1) % (xG).n) :=
    Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple (by rw [Y.gn]; exact sig_lt li (by omega) _ _)
  refine ⟨?_, fun x => ?_⟩
  · unfold sidePt; rw [hv0, hv1, Y.gn]
  · rw [hse, Chazelle.Chain.sideLeft_edge hne ht, Y.vtx_sig (by omega), Y.vtx_sig (by omega), hsn,
      Y.gn]

/-- **Inner position at a tour vertex** (regular): a vertex position of `G`, sector inside. -/
theorem inner_vtx (hp : p ≤ 2 * C.m + 6)
    (hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0) (hum : tU C.m C.topIdx C.sideBeta p ≠ C.m)
    (hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = li) :
    sidePt (C.sideWalk C.sideBeta) p 0 = sidePt xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) 0 ∧
      ∀ x, sideLeft (C.sideWalk C.sideBeta) p 0 x →
        sideLeft xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) 0 x := by
  have hm := Y.hm
  have h3 := Y.three
  have hm1 := C.one_le
  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  have hk0 : tK C.m C.topIdx C.sideBeta p ≠ 0 := fun h => hu0 ((tK_eq_zero_iff _ hm1 p).1 h)
  have hkm : tK C.m C.topIdx C.sideBeta p ≠ C.m := fun h => hum ((tK_eq_m_iff _ hm1 p).1 h)
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  have hsv := fun x (hx : sideLeft (C.sideWalk C.sideBeta) p 0 x) =>
    walk_sector_vtx Y.cpSimple Y.X.hCs Y.X.hCm h6 hp hu0 hum hx
  generalize tK C.m C.topIdx C.sideBeta p = kc at hkc_le hk0 hkm hv0 hsv ⊢
  rw [hA] at hsv
  have hnx : kNext li kc ≤ C.m := by grind [kNext]
  have hpv : kPrev li kc ≤ C.m := by grind [kPrev]
  have hsn := sig_next (i0 := i0) (show kc < xK by omega) (show kNext li kc < xK by omega)
    (fun _ => by omega)
  have hsp := sig_prev (i0 := i0) (show kc < xK by omega) (show kPrev li kc < xK by omega)
    (fun _ => by omega)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, hv0, Y.vtx_sig (by omega)]
  · have h := hsv x hx
    rw [Y.vtx_sig (by omega), Y.vtx_sig (by omega), Y.vtx_sig (by omega), hsn, hsp] at h
    rw [Chazelle.Chain.sideLeft_zero, Y.gn]
    exact h

/-- **Outer position inside a tour edge**: the reversed position of `G`, opposite half-plane. -/
theorem outer_edge (hp : p < 2 * C.m + 6) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = !li) :
    sidePt (C.sideWalk C.sideBeta) p t = sidePt xG (sig li xK i0
      (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m)) (tK C.m C.topIdx C.sideBeta p))) (1 - t) ∧
      ∀ x, sideLeft (C.sideWalk C.sideBeta) p t x →
        ¬ sideLeft xG (sig li xK i0
          (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m)) (tK C.m C.topIdx C.sideBeta p)))
          (1 - t) x := by
  have hm := Y.hm
  have h3 := Y.three
  obtain ⟨hkn, hk1⟩ := Y.kn_le (p := p)
  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp.le
  have hv1 := walk_next Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  have hse := walk_sector_edge Y.cpSimple Y.X.hCs Y.X.hCm C.sideBeta h6 hp ht
  generalize tK C.m C.topIdx C.sideBeta p = kc at hkn hk1 hkc_le hv0 hv1 hse ⊢
  rw [hA] at hkn hk1 hv1 hse ⊢
  -- the edge from `kc` to `kn` is the edge of `G` from `sig kn` to `sig kc`
  have hback : kNext li (kNext (!li) kc) = kc := by
    unfold kNext
    cases li
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]; omega
    grind
  have hkn' : kNext (!li) kc < xK := by omega
  have hsn : sig li xK i0 kc = (sig li xK i0 (kNext (!li) kc) + 1) % xK := by
    conv_lhs => rw [← hback]
    refine sig_next hkn' (by omega) (fun hl => ?_)
    subst hl; unfold kNext; simp_all
  rw [Y.vtx_sig (by omega)] at hv0
  rw [Y.vtx_sig hkn'] at hv1
  have hne : (xG).vtx (sig li xK i0 (kNext (!li) kc)) ≠
      (xG).vtx ((sig li xK i0 (kNext (!li) kc) + 1) % (xG).n) :=
    Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple (by rw [Y.gn]; exact sig_lt li (by omega) _ _)
  have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by grind, by grind⟩
  refine ⟨?_, fun x hx hx' => ?_⟩
  · unfold sidePt; rw [hv0, hv1, Y.gn, ← hsn, ← Chazelle.Geometry.lerp_symm]
  · rw [hse, Y.vtx_sig (by omega), Y.vtx_sig hkn'] at hx
    rw [Chazelle.Chain.sideLeft_edge hne ht', Y.gn, ← hsn] at hx'
    exact det_neg_of hx hx'

/-- **Outer position at a tour vertex** (regular): the sector is disjoint from that of `G`. -/
theorem outer_vtx (hp : p ≤ 2 * C.m + 6)
    (hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0) (hum : tU C.m C.topIdx C.sideBeta p ≠ C.m)
    (hA : decide (tU C.m C.topIdx C.sideBeta p < C.m) = !li) :
    sidePt (C.sideWalk C.sideBeta) p 0 = sidePt xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) 0 ∧
      ∀ x, sideLeft (C.sideWalk C.sideBeta) p 0 x →
        ¬ sideLeft xG (sig li xK i0 (tK C.m C.topIdx C.sideBeta p)) 0 x := by
  have hm := Y.hm
  have h3 := Y.three
  have hm1 := C.one_le
  have hkc_le := tK_le C.sideBeta C.one_le p (T := C.topIdx)
  have hk0 : tK C.m C.topIdx C.sideBeta p ≠ 0 := fun h => hu0 ((tK_eq_zero_iff _ hm1 p).1 h)
  have hkm : tK C.m C.topIdx C.sideBeta p ≠ C.m := fun h => hum ((tK_eq_m_iff _ hm1 p).1 h)
  have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp
  have hsv := fun x (hx : sideLeft (C.sideWalk C.sideBeta) p 0 x) =>
    walk_sector_vtx Y.cpSimple Y.X.hCs Y.X.hCm h6 hp hu0 hum hx
  generalize tK C.m C.topIdx C.sideBeta p = kc at hkc_le hk0 hkm hv0 hsv ⊢
  rw [hA] at hsv
  have e1 : kPrev (!li) kc = kNext li kc := by core_grind
  have e2 : kNext (!li) kc = kPrev li kc := by core_grind
  have hnx : kNext li kc ≤ C.m := by grind [kNext]
  have hpv : kPrev li kc ≤ C.m := by grind [kPrev]
  have hsn := sig_next (i0 := i0) (show kc < xK by omega) (show kNext li kc < xK by omega)
    (fun _ => by omega)
  have hsp := sig_prev (i0 := i0) (show kc < xK by omega) (show kPrev li kc < xK by omega)
    (fun _ => by omega)
  have hσ : sig li xK i0 kc < (xG).n := by rw [Y.gn]; exact sig_lt li (by omega) _ _
  refine ⟨?_, fun x hx hx' => ?_⟩
  · rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, hv0, Y.vtx_sig (by omega)]
  · have h := hsv x hx
    rw [e1, e2, Y.vtx_sig (by omega), Y.vtx_sig (by omega), Y.vtx_sig (by omega), hsn, hsp] at h
    rw [Chazelle.Chain.sideLeft_zero, Y.gn] at hx'
    have hns := FactsInterior.corner_nonSpike Y.gSimple hσ
    have hB : (xG).vtx ((sig li xK i0 kc + 1) % (xG).n) - (xG).vtx (sig li xK i0 kc) ≠ 0 :=
      sub_ne_zero.2 (Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple hσ).symm
    unfold Chazelle.Jordan.prevIdx at hns
    rw [Y.gn] at hns hB
    unfold sideLeftOf at h hx'
    exact Chazelle.Chain.sideCcw_asymm hB hns hx' h


end

/-- The points of `G` are below the top vertex and inside the coordinate square of `C.P`. -/
theorem g_bound {q : ℕ} (hq : q < xK) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(sidePt xG q s).1| ≤ Chazelle.Jordan.coordBound C.P ∧
      |(sidePt xG q s).2| ≤ Chazelle.Jordan.coordBound C.P ∧ (sidePt xG q s).2 ≤ C.top.2 := by
  have hm := Y.hm
  have h3 := Y.three
  have hmem : sidePt xG q s ∈ C.P.boundary := by
    rw [Y.hbd]
    exact ⟨q, by rw [Y.gn]; exact hq, Chazelle.Geometry.lerp_mem_segment _ _ hs0 hs1⟩
  obtain ⟨h1, h2⟩ := Chazelle.Jordan.abs_le_coordBound_of_mem_boundary C.P hmem
  refine ⟨h1, h2, ?_⟩
  obtain ⟨i, hi, hz⟩ := hmem
  obtain ⟨τ, hτ0, hτ1, hz'⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hz
  have hn := Y.hn
  have hv : ∀ k, k < C.P.n → (C.P.vtx k).2 ≤ C.top.2 := by
    intro k hk
    rw [← chain_vertex_eq Y.X.hCs hk]
    exact C.topIdx_spec.2 k (by omega)
  have a1 := hv i hi
  have a2 := hv ((i + 1) % C.P.n) (Nat.mod_lt _ (by omega))
  rw [hz', Chazelle.Geometry.lerp_snd]
  nlinarith

/-- **Box and slit positions are not points of `G`.** -/
theorem box_ne {p : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hp : p ≤ 5 ∨ (p = 2 * C.m + 6 ∧ 0 < t)) {q : ℕ} (hq : q < xK) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : sidePt xG q s ≠ sidePt (C.sideWalk C.sideBeta) p t := by
  intro he
  obtain ⟨h1, h2, h3⟩ := Y.g_bound hq hs0 hs1.le
  rw [he] at h1 h2 h3
  rcases walk_box C.sideBeta ht0 ht1 hp with h | h | h <;> linarith

end XCtx

/-- **A chord attached to the host polygon meets the region.** -/
theorem meet_of_attach (Y : XCtx P li L E reg r C NR i0 g) {c : Set Point}
    (hc : ∃ y a b : ℝ, a < b ∧ c = Chazelle.Visibility.hseg y a b) {q : ℕ} {s : ℝ}
    (hA : SideAttach xG c q s) : (c ∩ reg r).Nonempty := by
  have hG := Y.gSimple
  have hMH : WalkAx (interiorModel xG) := walkAx_interiorModel hG
  have hW : (interiorModel xG).W = xG :=
    DownDrv.interiorWalk_hostPoly Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
  have hReq := DownDrv.region_eq_intHost Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
  obtain ⟨hq, hs0, hs1, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨r', hr', hcl⟩ := hMH.clean q (by grind) s hs0 hs1
  rw [hW] at hcl
  obtain ⟨y₀, a, b, hab, rfl⟩ := hc
  obtain ⟨x, hxc, hne, hxd⟩ := Extract.exists_near_mem hab hmem (lt_min hrA hr')
  have hxl := hsec x hxc hne (lt_of_lt_of_le hxd (min_le_left _ _))
  have hxD : x ∈ (interiorModel xG).D := by
    by_contra hxD
    exact hcl x (show dist x _ < r' from lt_of_lt_of_le hxd (min_le_right _ _)) hxD hxl
  refine ⟨x, hxc, ?_⟩
  rw [hReq]; exact hxD

end

end

end DrvX

end Chazelle.Core
