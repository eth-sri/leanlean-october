module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.ShootCutDyDn

section
set_option hygiene false
local macro "zqbdh" : tactic => `(tactic| have hIn : ztcfx := Trans.iw_n)
local macro "zqbdi" : tactic => `(tactic| have hh' := hD C.m 0 by_omega by_omega by_omega)
local macro "zqbdj" : tactic => `(tactic| (set j := p - c0 C li with hj
                                           have hjm : j < C.m := by_omega
                                           have hpj : p = j + c0 C li := by_omega))
local macro "zqbdk" : tactic => `(tactic| have hmn := T.hm)
local macro "zqbdl" : tactic => `(tactic| (obtain ⟨y, a, b, hch, hcab, hy, heL, heR⟩ := rec_chord hcA hatt
                                           obtain ⟨hAL, hAR⟩ := hatt))
local macro "zqbdm" : tactic => `(tactic| (rintro ⟨h1, h2, h3⟩
                                           refine ⟨h1, h2, fun ⟨h4, h5⟩ => h3 ⟨h4, ?_⟩⟩))
local macro "zqbdn" : tactic => `(tactic| (set t := (chainModel C).param Q ⟨p, h + 1⟩ with ht
                                           have hA' := hA))
local macro "zqbdo" : tactic => `(tactic| have hwrap : ztbpj % (interiorWalk Q).n = 0 := by_simp_all)
local macro "zqbdp" : tactic => `(tactic| rw [show x = ((x.1, y) : Point) from Prod.ext rfl hxy])
local macro "zqbdq" : tactic => `(tactic| obtain ⟨h1, h2, h3⟩ := (innerE_iff hQ T hD hli hx).1 hk')
local macro "zqbdr" : tactic => `(tactic| rw [show z = (zthlk : Point) from Prod.ext rfl hzy])
local macro "zqbds" : tactic => `(tactic| refine ⟨b' - a', by_linarith, fun z hz hze hzd => ?_⟩)
local macro "zqbdt" : tactic => `(tactic| obtain ⟨rfl, -, -⟩ := piece_bounds hQ T hD hli hch' hsub)
set_option hygiene true

/-!
# Down-phase transition (D2), part 3: the piece of one chord record (T-R1, T-R2)

The RAM filter of the transition reads the chord records `(h, lp, rp)` of the canonical normal
form of the top chain `C` (chain model) and decides, by index arithmetic only:

* `innerE`: an end at chain walk edge `p` is **inner** if `c₀ ≤ p < c₀ + m` and it is not the
  interior walk vertex `w₀` (`p = c₀` with height vertex `h = idxI 0`);
* `keepT`: a record is kept iff one of its ends is inner;
* `mapE`: an end is mapped to the interior walk edge `p - c₀` (on the inner run) or to the last
  edge `m` (the edge `e_{n-1}`, which the chord crosses, or the vertex `w_m`);
* `trT`: the mapped triple `(h, mapE lp, mapE rp)`.

**`rec_kept`**: the mapped triple of a kept record describes an interior chord of `Q` inside the
chain chord (its piece, `Trans.pieces`), correctly attached.  **`rec_dropped`**: a dropped
record contains no interior chord.

Proof: an inner end is attached on the interior walk at the shifted position
(`Trans.Shift.sec_eq`), so it carries a piece (`Trans.piece_of_attach`, `piece_at_inner`); the
other end of the piece is the other end of the chord or a point of the open last edge
(`Trans.Top.boundary_dom`), and the mapped position has exactly that point (`other_end`, with
`inner_of_interior` for the ends of the chord that see the interior); attachment at a position
with the right point follows from the uniqueness of positions of the simple interior walk
(`attach_int`).
-/
namespace Chazelle.Core
namespace DrvT
@[expose] public section
open Set Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)

/-! ## The index functions of the filter -/

/-- An end at chain walk edge `p` (height vertex `h`) is an inner end. -/
def innerE (li : Bool) (n c₀ h p : ℕ) : Bool :=
  decide (c₀ ≤ p ∧ p < c₀ + ztkl ∧ ¬ (p = c₀ ∧ h = idxI li n 0))

/-- The interior walk edge of an end. -/
def mapE (n c₀ p : ℕ) : ℕ := if c₀ ≤ p ∧ p < c₀ + ztkl then p - c₀ else n - 1

/-- A record is kept iff one of its ends is inner. -/
def keepT (li : Bool) (n c₀ : ℕ) (x : ℕ × ℕ × ℕ) : Bool :=
  innerE li n c₀ x.1 x.2.1 || innerE li n c₀ x.1 x.2.2

/-- The mapped triple. -/
def trT (n c₀ : ℕ) (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1, mapE n c₀ x.2.1, mapE n c₀ x.2.2)

/-! ## Parameters and points -/
theorem paramI_succ (Q : Polygon) (q h : ℕ) :
    (interiorModel Q).param Q ztgph =
      if ((interiorWalk Q).vtx q).2 = ((interiorWalk Q).vtx ztxlr).2
      then 0
      else ((Q.vtx h).2 - ((interiorWalk Q).vtx q).2) /
        (((interiorWalk Q).vtx ztxlr).2 - ((interiorWalk Q).vtx q).2) :=
  rfl
theorem paramC_succ (C : Chain) (Q : Polygon) (q h : ℕ) :
    (chainModel C).param Q ztgph =
      if ((C.sideWalk C.sideBeta).vtx q).2 =
          ((C.sideWalk C.sideBeta).vtx ztwtw).2 then 0
      else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx q).2) /
        (((C.sideWalk C.sideBeta).vtx ztwtw).2 -
          ((C.sideWalk C.sideBeta).vtx q).2) :=
  rfl

/-- The chord of a triple, in terms of the walk points. -/
theorem toSet_recOf (M : Model) (Q : Polygon) (x : ℕ × ℕ × ℕ) :
    (recOf x).toSet M Q = hseg (Q.vtx x.1).2 (sidePt M.W x.2.1 (M.param Q ztrex)).1
      (sidePt M.W x.2.2 (M.param Q ztrey)).1 := rfl

/-- The parameter of a point of a non-horizontal walk edge at a vertex height. -/
theorem param_of_lerp (M : Model) (Q : Polygon) {q h : ℕ} {s : ℝ}
    (hne : (M.W.vtx q).2 ≠ (M.W.vtx ztxls).2)
    (hy : (lerp (M.W.vtx q) (M.W.vtx ztxls) s).2 = (Q.vtx h).2) :
    M.param Q ztgph = s := by
  show (if (M.W.vtx q).2 = (M.W.vtx ztxls).2 then 0
      else ((Q.vtx h).2 - (M.W.vtx q).2) /
        ((M.W.vtx ztxls).2 - (M.W.vtx q).2)) = s
  rw [ite_eq_right hne, ← hy, Chazelle.Geometry.lerp_snd]
  grind

/-- A horizontal segment inside another. -/
theorem hseg_sub {y a b y' a' b' : ℝ} (hab' : a' ≤ b') (h : hseg y' a' b' ⊆ hseg y a b) :
    y' = y ∧ a ≤ a' ∧ b' ≤ b := by
  have h1 := h (show (ztdtr : Point) ∈ hseg y' a' b' from ⟨rfl, le_rfl, hab'⟩)
  have h2 := h (show (ztjog : Point) ∈ hseg y' a' b' from ⟨rfl, hab', le_rfl⟩)
  exact ⟨h1.1, h1.2.1, h2.2.2⟩

/-- A point of a horizontal segment off its open part is an end. -/
theorem hseg_end {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) {e : Point}
    (he : e ∈ hseg y a b) (heD : e ∉ D) : e = (ztdv : Point) ∨ e = (ztdy : Point) := by
  obtain ⟨hy, ha, hb⟩ := he
  zucoq
  · zukkw
    · exfalso; apply heD
      rw [show e = ((e.1, y) : Point) from Prod.ext rfl hy]
      exact h.open_mem _ ha' hb'
    grind
  grind

/-- **Attachment of an interior chord at a position with the right point.** -/
theorem attach_int {Q : Polygon} (hQ : Q.Simple) {y a b : ℝ}
    (h : IsHChordIn ztrx y a b) {q : ℕ} {u : ℝ} (hq : q < Q.n)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hpt : sidePt ztkb q u = (ztdv : Point) ∨
      sidePt ztkb q u = (ztdy : Point)) :
    SideAttach ztkb ztbiq q u := by
  zudg
  zqbdh
  have h' : IsHChordIn ((interiorWalk Q).filled \ (interiorWalk Q).boundary) y a b := by
    simp_all
  obtain ⟨ha, hb⟩ := FactsInterior.hchord_end_mem_boundary h'
  have hopen := FactsInterior.hchord_open h'
  zuglx
  have hseg_eq := FactsChain.hseg_eq_segment (y := y) h.lt.le
  have key : ∀ {e e' : Point}, WalkEnd ztkb ztbiq e →
      sidePt ztkb q u = e → SideAttach ztkb ztbiq q u := by
    intro e e' hE hqe
    obtain ⟨p, t, hAt, hpt'⟩ := hE.1
    obtain ⟨hp, ht0, ht1, -⟩ := id hAt
    obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hWs hp by_omega ht0 ht1 hu0 hu1
      (hpt'.trans hqe.symm)
    omega
  rcases hpt with hpt | hpt
  · refine key (e' := (ztdy : Point)) ?_ hpt
    rw [hseg_eq]; exact FactsInterior.walkEnd hWs hWo hab ha hopen
  · refine key (e' := (ztdv : Point)) ?_ hpt
    rw [hseg_eq, Chazelle.Geometry.segment_comm]
    exact FactsInterior.walkEnd hWs hWo hab.symm hb ztjnr
variable {Q : Polygon} {C : Chain}
variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli
omit hQ T hD hli in
/-- The interior walk vertices `0` and `m` are the ends of the last edge. -/
theorem iw_ends (_hQ : Q.Simple) (T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    ((interiorWalk Q).vtx 0 = Q.vtx 0 ∨ (interiorWalk Q).vtx 0 = Q.vtx C.m) ∧
      ((interiorWalk Q).vtx C.m = Q.vtx 0 ∨ (interiorWalk Q).vtx C.m = Q.vtx C.m) := by
  zqbdk
  rw [iw_vtx_idx hli by_omega, iw_vtx_idx hli by_omega]
  zulbu
  grind
variable {h p : ℕ} {c : Set Point} {y a b : ℝ} {x : ℕ × ℕ × ℕ}
/-- **(E1) On the inner run** the interior parameter and point are the chain ones. -/
theorem inner_param (hp1 : c0 C li ≤ p) (hp2 : p < c0 C li + C.m) :
    (interiorModel Q).param Q ⟨p - c0 C li, h + 1⟩ = (chainModel C).param Q ztdw ∧
      sidePt ztkb (p - c0 C li) ztwom =
        sidePt ztcs p ztwom := by
  zqbdk
  zubfr

  zqbdh
  zuhxv
  zqbdj
  have e1 : (C.sideWalk C.sideBeta).vtx p = (interiorWalk Q).vtx j := by
    rw [hpj]; exact vtx_c0 hQ T hD hli hjm.le
  have e2 : (C.sideWalk C.sideBeta).vtx ztwqw =
      (interiorWalk Q).vtx ztytb := by
    rw [hWn, Nat.mod_eq_of_lt (by unfold c0 at *; omega), hIn, Nat.mod_eq_of_lt by_omega,
      show p + 1 = ztl + c0 C li by omega]
    exact vtx_c0 hQ T hD hli hjm
  zujx
  · rw [paramI_succ, paramC_succ, e1, e2]
  · zuikk

/-- The interior walk edges are not horizontal. -/
theorem iw_edge_ne {q : ℕ} (hq : q < Q.n) :
    ((interiorWalk Q).vtx q).2 ≠ ((interiorWalk Q).vtx ztxlr).2 := by
  zudov
  zqbdh
  rw [hIn]
  refine iw_snd_ne hQ T hD hli hq ztcv ?_
  zuq
  rcases (show q + 1 < Q.n ∨ q + 1 = Q.n by omega) with h1 | h1
  · zuhkh
  · rw [h1, Nat.mod_self] at h; omega

/-- **The `w₀` test**: the chain parameter at `c₀` vanishes iff the height vertex is `w₀`. -/
theorem paramC_c0_zero_iff {h : ℕ} (hh : h < Q.n) :
    (chainModel C).param Q ⟨c0 C li, h + 1⟩ = 0 ↔ h = idxI li Q.n 0 := by
  zqbdk
  zubb
  zqbdh
  obtain ⟨e1, -⟩ := inner_param hQ T hD hli (h := h) (p := c0 C li) le_rfl by_omega
  rw [← e1, Nat.sub_self, paramI_succ, ite_eq_right ztili]
  have hd : ((interiorWalk Q).vtx _).2 -
      ((interiorWalk Q).vtx 0).2 ≠ 0 :=
    sub_ne_zero.2 (Ne.symm ztili)
  rw [div_eq_zero_iff, or_iff_left hd, sub_eq_zero, iw_vtx_idx hli by_omega]
  constructor
  · zuhgj
    zuct
    exact hD _ _ hh (idxI_lt by_omega) hne h'
  simp_all

/-- **The test of the filter**: an inner end in geometric terms. -/
theorem innerE_iff (hh : h < Q.n) :
    innerE li Q.n ztpe h p = true ↔
      (c0 C li ≤ p ∧ p < c0 C li + C.m ∧
        ¬ ztxlh) := by
  zqbdk
  unfold innerE
  rw [decide_eq_true_iff, show Q.n - 1 = C.m by omega]
  constructor
  · zqbdm
    rw [h4] at h5
    exact (paramC_c0_zero_iff hQ T hD hli hh).1 h5
  · zqbdm
    zujic
    exact (paramC_c0_zero_iff hQ T hD hli hh).2 h5
omit hQ T hD hli in
theorem mapE_eq (_hQ : Q.Simple) (T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (_hli : li = true ↔ Mountain.LeftInside Q) (p : ℕ) :
    mapE Q.n ztpe p = if c0 C li ≤ p ∧ p < c0 C li + C.m then p - c0 C li else C.m := by
  zqbdk
  unfold mapE
  grind

/-- **A piece at an inner end.** -/
theorem piece_at_inner (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach ztcs c p t) (hp1 : c0 C li ≤ p)
    (hp2 : p < c0 C li + C.m) (hp3 : ¬ ztfts) :
    ∃ y a b, IsHChordIn ztrx y a b ∧ hseg y a b ⊆ c ∧
      (sidePt ztcs p t = (ztdv : Point) ∨
        sidePt ztcs p t = (ztdy : Point)) := by
  zubwg
  zulir
  zqbdk
  zubfr

  zqbdh
  zqbdj
  obtain ⟨hp, ht0, ht1, -⟩ := id hA
  have hsj : t = 0 → 1 ≤ j := fun h0 => by
    grind
  have hpt : sidePt ztkb j t = sidePt ztcs p t := by
    zuikk
  have hAI : SideAttach ztkb c j t := by
    refine ExtG.attach_of_sector hpt ztjwp by_omega ht0 ht1 hA
    rw [hpj] at hx
    exact (H.sec_eq T hQ hjm ht0 ht1 hsj x).1 hx
  have hnD : sidePt ztkb j t ∉ C.dom := by
    zvmxe; exact hMC.trace p hp t ht0 ht1.le
  obtain ⟨d, ⟨⟨y, a, b, hch, rfl⟩, c', hc', hdc⟩, hAd⟩ :=
    Trans.piece_of_attach hQ T (F₀ := {c}) (fun _ h => by_grind)
      ztmmn hAI hnD
  rw [mem_singleton_iff.1 hc'] at hdc
  refine ⟨y, a, b, hch, hdc, ?_⟩
  zuezz
  exact hseg_end hch hAd.2.2.2.1 (fun h => hnD (T.interior_sub_dom hQ h))

/-- **The ends of the chord that see the interior but are not inner** are `w₀` or `w_m`. -/
theorem special_end (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach ztcs c p t)
    (hnear : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt ztcs p t →
      dist x ztyfq < r → x ∈ Q.filled \ Q.boundary)
    (hnI : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m ∧ ¬ ztfts)) :
    (p = c0 C li ∧ t = 0 ∧ sidePt ztcs p t = (interiorWalk Q).vtx 0) ∨
      (p = c0 C li + C.m ∧ t = 0 ∧
        sidePt ztcs p t = (interiorWalk Q).vtx C.m) := by
  obtain ⟨h1, h2, h3⟩ := inner_of_interior hQ T hD hli hc hA hnear
  zudt
  · have h4 : ztmwi := by
      simp_all
    obtain ⟨rfl, rfl⟩ := h4
    left
    refine ⟨rfl, rfl, ?_⟩
    zudti
    have := vtx_c0 hQ T hD hli ztbg
    simp_all
  · have ht := h3 h2
    zucfb
    right
    refine ⟨h2, rfl, ?_⟩
    rw [Chazelle.Chain.sidePt_zero, h2]
    have := vtx_c0 hQ T hD hli le_rfl
    grind

/-- **The point of the open last edge** at a vertex height is at the mapped position `m`. -/
theorem last_edge_pt {h : ℕ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : (lerp ztcpk ztccl s).2 = (Q.vtx h).2) :
    0 ≤ (interiorModel Q).param Q ztdqg ∧ (interiorModel Q).param Q ztdqg < 1 ∧
      sidePt ztkb C.m ((interiorModel Q).param Q ztdqg) =
        lerp ztcpk ztccl s := by
  zqbdk
  zqbdh
  zqbdo
  have hne := iw_edge_ne hQ T hD hli (q := C.m) by_omega
  have hv0 := iw_vtx_idx hli (j := 0) by_omega
  have hvm := iw_vtx_idx hli (j := C.m) by_omega
  unfold idxI at hv0 hvm
  zufrc
  · rw [ite_eq_left hl] at hv0 hvm
    have hpar : (interiorModel Q).param Q ztdqg = s := by
      zukno
      show (lerp ztifd ((interiorWalk Q).vtx (ztbpj %
        (interiorWalk Q).n)) s).2 = _
      simp_all
    zueyf
    refine ⟨hs.1.le, hs.2, ?_⟩
    zujrb
  · rw [ite_eq_right hl, show Q.n - 1 - 0 = C.m by omega] at hv0
    rw [ite_eq_right hl, show Q.n - 1 - C.m = 0 by omega] at hvm
    have hrev : lerp ztcpk ztccl s = lerp ztccl ztcpk zteb := by
      apply Prod.ext <;> zuowg <;> ring
    have hpar : (interiorModel Q).param Q ztdqg = 1 - s := by
      zukno
      show (lerp ztifd ((interiorWalk Q).vtx (ztbpj %
        (interiorWalk Q).n)) _).2 = _
      simp_all
    zueyf
    refine ⟨by_grind, by_simp_all, ?_⟩
    zujrb

/-- **The mapped position of an end that is not inner** has the point of the corresponding
end of the piece: the end of the chord itself (if the chord sees the interior there) or the
crossing with the open last edge. -/
theorem other_end (hc : hseg y a b ∈ (chainModel C).Adm) {h : ℕ} (_hh : h < Q.n)
    (hy : (Q.vtx h).2 = y) {p : ℕ}
    (hA : SideAttach ztcs ztbiq p ztwom)
    (hnI : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m ∧
      ¬ ztxlh))
    {z : Point} (hzy : z.2 = y)
    (hcase : (z = sidePt ztcs p ztwom ∧
        ∃ r > 0, ∀ x ∈ hseg y a b, x ≠ z → dist x z < r → x ∈ Q.filled \ Q.boundary) ∨
      (z ∈ C.dom ∧ z ∈ Q.boundary)) :
    0 ≤ (interiorModel Q).param Q ztwpi ∧
      (interiorModel Q).param Q ztwpi < 1 ∧
      sidePt ztkb ztzmz
        ztbanp = z := by
  zqbdk
  zubb
  zqbdh
  rw [mapE_eq hQ T hD hli]
  zqbdn
  obtain ⟨hp, ht0, ht1, hmem, -⟩ := hA'
  rcases hcase with ⟨rfl, hnear⟩ | ⟨hzD, hzb⟩
  · rcases special_end hQ T hD hli hc hA hnear hnI with ⟨rfl, -, hpt⟩ | ⟨rfl, ht0', hpt⟩
    · zubek
      obtain ⟨e1, e2⟩ := inner_param hQ T hD hli (h := h) le_rfl by_omega
      simp_all
    · zufa
      zqbdo
      have hpar : (interiorModel Q).param Q ztdqg = 0 := by
        refine param_of_lerp _ Q ztili ?_
        show (lerp ztifd ((interiorWalk Q).vtx (ztbpj %
          (interiorWalk Q).n)) 0).2 = _
        rw [Chazelle.Geometry.lerp_zero, hy, ← hpt]
        omega
      rw [hpar, Chazelle.Chain.sidePt_zero, ← hpt]
      simp
  · obtain ⟨s, hs, rfl⟩ := T.boundary_dom hzb hzD
    zqbdi
    obtain ⟨hne1, hne2, -⟩ := lerp_snd_ne hh' hs
    have hJ : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m) := by
      zubf
      have h3 : ztmwi := by
        simp_all
      obtain ⟨rfl, ht0'⟩ := h3
      have hpt : sidePt ztcs ztpe t = (interiorWalk Q).vtx 0 := by
        rw [ht0', Chazelle.Chain.sidePt_zero]
        have := vtx_c0 hQ T hD hli ztbg
        simp_all
      have hy0 : ((interiorWalk Q).vtx 0).2 = y := by zvnbr; exact hmem.1
      rcases (iw_ends hQ T hD hli).1 with e | e <;> zvmwe at hy0
      · simp_all
      simp_all
    rw [ite_eq_right hJ]
    exact last_edge_pt hQ T hD hli hs by_simp_all
omit hQ T hD hli in
/-- The piece of a chord of the chain model, as a horizontal segment. -/
theorem piece_bounds (_hQ : Q.Simple) (_T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (_hli : li = true ↔ Mountain.LeftInside Q) {y a b y' a' b' : ℝ}
    (hch' : IsHChordIn ztrx y' a' b')
    (hsub : hseg y' a' b' ⊆ hseg y a b) : y' = y ∧ a ≤ a' ∧ b' ≤ b :=
  hseg_sub hch'.lt.le hsub
omit hQ T hD in
omit hli in
/-- The end of a piece is a boundary point of `Q`. -/
theorem piece_ends_bd (_hQ : Q.Simple) (_T : Trans.Top Q C) (_hD : Trans.DistinctH Q) {y a b : ℝ}
    (hch : IsHChordIn ztrx y a b) :
    (ztdv : Point) ∈ Q.boundary ∧ (ztdy : Point) ∈ Q.boundary :=
  FactsInterior.hchord_end_mem_boundary hch

/-- **The mapped end of a record**: for a piece `[a', b'] × {y}` of the chord of a record and
an end of the record, the mapped position has the point of the corresponding end of the
piece.  `hcorr` says which end: the end `e` of the chord and the end `z` of the piece, with the
part of the chord between them outside the piece. -/
theorem mapped_end (hc : hseg y a b ∈ (chainModel C).Adm)
    (hch : IsHChordIn C.dom y a b) {h : ℕ} (hh : h < Q.n) (hy : (Q.vtx h).2 = y) {p : ℕ}
    (hA : SideAttach ztcs ztbiq p ztwom)
    {a' b' : ℝ} (hch' : IsHChordIn ztrx y a' b')
    (hsub : hseg y a' b' ⊆ hseg y a b) {z : Point}
    (hz : z = (ztfoz : Point) ∧ sidePt ztcs p
        ztwom = (ztdv : Point) ∨
      z = (ztfpb : Point) ∧ sidePt ztcs p
        ztwom = (ztdy : Point)) :
    0 ≤ (interiorModel Q).param Q ztwpi ∧
      (interiorModel Q).param Q ztwpi < 1 ∧
      sidePt ztkb ztzmz
        ztbanp = z := by
  zqbdk
  zubb
  zqbdi
  obtain ⟨-, ha', hb'⟩ := piece_bounds hQ T hD hli hch' hsub
  zudoq

  zqbdn
  obtain ⟨hp, ht0, ht1, -⟩ := hA'
  by_cases hI : c0 C li ≤ p ∧ p < c0 C li + C.m ∧ ¬ ztfts
  · -- an inner end: the piece there is this piece
    zugpb
    obtain ⟨y'', a'', b'', hch'', hsub'', hend⟩ := piece_at_inner hQ T hD hli hc hA h1 h2 h3
    have heq := Trans.one_piece hQ T hh' hch ⟨y'', a'', b'', hch'', rfl⟩ ztcpc
      hsub'' hsub
    obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hch''.lt.le heq
    rw [mapE_eq hQ T hD hli, ite_eq_left by_omega]
    obtain ⟨e1, e2⟩ := inner_param hQ T hD hli (h := h) h1 h2
    grind
  · -- not inner: the chord's end or the crossing with the last edge
    refine other_end hQ T hD hli hc hh hy hA hI ?_ ?_
    · grind
    rcases hz with ⟨rfl, hpt⟩ | ⟨rfl, hpt⟩
    · rcases ha'.lt_or_eq with hlt | heq
      · right
        exact ⟨hch.open_mem a' hlt by_linarith, hzbA⟩
      · left
        zufpx
        refine ⟨hpt.symm, b' - a, by_linarith, fun x hx hxe hxd => ?_⟩
        obtain ⟨hxy, hxa, -⟩ := hx
        have hx1 : x.1 ≠ a := by_grind
        have hd : |x.1 - a| < b' - a := by
          have := hxd
          zuhkm

        zujhl
        zqbdp
        zulfj
    · rcases hb'.lt_or_eq with hlt | heq
      · right
        exact ⟨hch.open_mem b' by_linarith hlt, hzbB⟩
      · left
        zufpx
        refine ⟨hpt.symm, b' - a', by_linarith, fun x hx hxe hxd => ?_⟩
        obtain ⟨hxy, -, hxb⟩ := hx
        have hx1 : x.1 ≠ b' := by_grind
        have hd : |x.1 - b'| < b' - a' := by
          have := hxd
          zuhkm

        zujhm
        zqbdp
        zulfk
omit hQ T hD hli in
/-- The chord of a record of the chain model, with its two ends. -/
theorem rec_chord
    (hcA : (recOf x).toSet ztc Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached ztc Q) :
    ∃ y a b, IsHChordIn C.dom y a b ∧ (recOf x).toSet ztc Q = hseg y a b ∧
      (Q.vtx x.1).2 = y ∧
      sidePt ztcs x.2.1 ztcgk =
        (ztdv : Point) ∧
      sidePt ztcs x.2.2 ztcgl =
        (ztdy : Point) := by
  obtain ⟨y, a, b, hch, -, hcab⟩ := hcA
  have hcab' := hcab
  rw [toSet_recOf] at hcab'
  obtain ⟨hy, ha, hb⟩ := Merge.hseg_inj hch.lt.le hcab'.symm
  obtain ⟨⟨-, -, -, hmL, -⟩, ⟨-, -, -, hmR, -⟩⟩ := hatt
  zvmyh at hmL hmR
  refine ⟨y, a, b, hch, hcab, hy.symm, Prod.ext ha.symm hmL.1, Prod.ext hb.symm hmR.1⟩

/-- **A kept record**: its mapped triple is a correctly attached interior chord inside its
chord. -/
theorem rec_kept (hx : x.1 < Q.n)
    (hcA : (recOf x).toSet ztc Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached ztc Q) (hk : keepT li Q.n ztpe x = true) :
    (recOf ztxov).toSet ztd Q ∈ (interiorModel Q).Adm ∧
      (recOf ztxov).toSet ztd Q ⊆
        (recOf x).toSet ztc Q ∧
      (recOf ztxov).Attached ztd Q := by
  zqbdl
  zvmyh at hAL hAR hcA
  -- a piece, at an inner end
  have hpiece : ∃ a' b', IsHChordIn ztrx y a' b' ∧
      hseg y a' b' ⊆ hseg y a b := by
    have hk' : innerE li Q.n ztpe x.1 x.2.1 = true ∨
        innerE li Q.n ztpe x.1 x.2.2 = true := by
      unfold keepT at hk; simp_all
    rcases hk' with hk' | hk'
    · zqbdq
      obtain ⟨y', a', b', hch', hsub, -⟩ := piece_at_inner hQ T hD hli hcA hAL h1 h2 h3
      zqbdt
      grind
    · zqbdq
      obtain ⟨y', a', b', hch', hsub, -⟩ := piece_at_inner hQ T hD hli hcA hAR h1 h2 h3
      zqbdt
      grind
  obtain ⟨a', b', hch', hsub⟩ := hpiece
  obtain ⟨hl0, hl1, hlpt⟩ := mapped_end hQ T hD hli hcA hch hx hy (p := x.2.1) hAL hch' hsub
    (Or.inl ⟨rfl, heL⟩)
  obtain ⟨hr0, hr1, hrpt⟩ := mapped_end hQ T hD hli hcA hch hx hy (p := x.2.2) hAR hch' hsub
    (Or.inr ⟨rfl, heR⟩)
  have hset : (recOf ztxov).toSet ztd Q = hseg y a' b' := by
    rw [toSet_recOf]
    show hseg (Q.vtx x.1).2 (sidePt ztkb (mapE Q.n _ x.2.1)
      ((interiorModel Q).param Q ⟨mapE Q.n _ x.2.1, x.1 + 1⟩)).1
      (sidePt ztkb (mapE Q.n _ x.2.2)
      ((interiorModel Q).param Q ⟨mapE Q.n _ x.2.2, x.1 + 1⟩)).1 = _
    simp_all
  have hmapLt : ∀ p, mapE Q.n ztpe p < Q.n := fun p => by
    have := T.hm
    unfold mapE; grind
  refine ⟨by rw [hset]; exact ztcpc, by_simp_all, ?_, ?_⟩
  · show SideAttach _ _ _ _
    zucju
    exact attach_int hQ hch' ztvvp hl0 hl1 (Or.inl hlpt)
  · show SideAttach _ _ _ _
    zucju
    exact attach_int hQ hch' ztvvp hr0 hr1 (Or.inr hrpt)

/-- **A dropped record** contains no interior chord. -/
theorem rec_dropped (hx : x.1 < Q.n)
    (hcA : (recOf x).toSet ztc Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached ztc Q) (hk : keepT li Q.n ztpe x = false)
    {d : Set Point} (hd : d ∈ (interiorModel Q).Adm)
    (hdc : d ⊆ (recOf x).toSet ztc Q) : False := by
  zqbdk
  zubb
  zqbdi
  zqbdl
  zvmyh at hAL hAR hcA hdc
  replace hAL : SideAttach ztcs ztbiq x.2.1
      ztcgk := hAL
  replace hAR : SideAttach ztcs ztbiq x.2.2
      ztcgl := hAR
  obtain ⟨y', a', b', hch', rfl⟩ := hd
  obtain ⟨hyy, ha', hb'⟩ := piece_bounds hQ T hD hli hch' hdc
  rw [hyy] at hch' hdc
  zudoq

  have hkL : ¬ (c0 C li ≤ x.2.1 ∧ x.2.1 < c0 C li + C.m ∧
      ¬ (x.2.1 = c0 C li ∧ (chainModel C).param Q ztrex = 0)) := by
    zudvo

  have hkR : ¬ (c0 C li ≤ x.2.2 ∧ x.2.2 < c0 C li + C.m ∧
      ¬ (x.2.2 = c0 C li ∧ (chainModel C).param Q ztrey = 0)) := by
    zudvo

  -- an end of the piece inside the chord is on the open last edge
  have hlast : ∀ e : ℝ, a < e → e < b → (ztcna : Point) ∈ Q.boundary →
      ∃ s ∈ Ioo (0 : ℝ) 1, (ztcna : Point) = lerp _ _ s :=
    fun e h1 h2 hb => T.boundary_dom hb (hch.open_mem e h1 h2)
  -- an end of the piece at an end of the chord is `w₀` or `w_m`
  have hvL : a' = a → (ztdv : Point) = (interiorWalk Q).vtx 0 ∨
      (ztdv : Point) = (interiorWalk Q).vtx C.m := by
    zudii
    zufpx
    have hnear : ∃ r > 0, ∀ z ∈ hseg y a' b, z ≠ sidePt ztcs x.2.1
        ztcgk →
        dist z (sidePt ztcs x.2.1
          ztcgk) < r → z ∈ Q.filled \ Q.boundary := by
      rw [heL]
      zqbds
      obtain ⟨hzy, hza, -⟩ := hz
      have hz1 : z.1 ≠ a' := by_grind
      have hd : |z.1 - a'| < b' - a' := by
        zuhkl

      zujhl
      zqbdr
      zulfj
    rcases special_end hQ T hD hli hcA (p := x.2.1) hAL hnear hkL with ⟨-, -, hpt⟩ | ⟨-, -, hpt⟩
    · grind
    grind
  have hvR : b' = b → (ztdy : Point) = (interiorWalk Q).vtx 0 ∨
      (ztdy : Point) = (interiorWalk Q).vtx C.m := by
    zudii
    zufpx
    have hnear : ∃ r > 0, ∀ z ∈ hseg y a b', z ≠ sidePt ztcs x.2.2
        ztcgl →
        dist z (sidePt ztcs x.2.2
          ztcgl) < r → z ∈ Q.filled \ Q.boundary := by
      rw [heR]
      zqbds
      obtain ⟨hzy, -, hzb⟩ := hz
      have hz1 : z.1 ≠ b' := by_grind
      have hd : |z.1 - b'| < b' - a' := by
        zuhkl

      zujhm
      zqbdr
      zulfk
    rcases special_end hQ T hD hli hcA (p := x.2.2) hAR hnear hkR with ⟨-, -, hpt⟩ | ⟨-, -, hpt⟩
    · grind
    grind
  -- heights
  have hends := iw_ends hQ T hD hli
  have hyv : ∀ v : Point, (v = (interiorWalk Q).vtx 0 ∨ v = (interiorWalk Q).vtx C.m) →
      v.2 = (Q.vtx 0).2 ∨ v.2 = (Q.vtx C.m).2 := by
    grind
  have hnot : ∀ e : ℝ, a < e → e < b → (ztcna : Point) ∈ Q.boundary →
      y ≠ (Q.vtx 0).2 ∧ y ≠ (Q.vtx C.m).2 := by
    intro e h1 h2 hb
    obtain ⟨s, hs, hes⟩ := hlast e h1 h2 hb
    obtain ⟨hn1, hn2, -⟩ := lerp_snd_ne hh' hs
    grind
  rcases ha'.lt_or_eq with haL | haL <;> rcases hb'.lt_or_eq with hbR | hbR
  · -- both ends of the piece on the open last edge: the same point
    obtain ⟨s, hs, hes⟩ := hlast a' haL by_linarith hzbA
    obtain ⟨s', hs', hes'⟩ := hlast b' by_linarith hbR hzbB
    have h2 := congrArg Prod.snd hes
    have h2' := congrArg Prod.snd hes'
    simp only [Chazelle.Geometry.lerp_snd] at h2 h2'
    grind
  · -- the piece reaches the right end only
    grind
  · grind
  · -- both ends of the chord are `w₀` or `w_m`
    have hL := hvL haL.symm
    have hR := hvR hbR
    have hab : ztxfd := by_grind
    grind
end
end DrvT
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqblm" : tactic => `(tactic| (set I := interiorModel Q
                                           set N := nk I S R
                                           zulk
                                           zubl

                                           have h3 : ztkzq := three_le_nk hQ hFam hne hR))
local macro "zqbln" : tactic => `(tactic| have hsj : ztymd := Nat.mod_lt _ by_omega)
local macro "zqblo" : tactic => `(tactic| have hsi : ztzrc := Nat.mod_lt _ by_omega)
set_option hygiene true

/-!
# Down phase, math (H-R1): the cyclic structure of the host keys of a region

Around a region `R` of the interior family `S` (walk order of the host keys `hk 0 < … < hk (N-1)`):

* `exit_chord_side`: an exit chord of `R` attached at the host key `hk i` is attached at a
  neighbouring host key, through a chord gap;
* `end_chord`: after the end of an arc of `R` comes a chord gap, along every exit chord attached
  at the end;
* `two_chords_vertex`: two distinct chords attached at one walk position meet at a walk vertex;
* `junction` (distinct heights): a host key between two chord gaps is a walk vertex, and the key
  after the second chord gap starts an arc gap — so between two arcs there is at most one
  junction point;
* `arc_run`: the inner host keys of an arc `(l, r)` are the walk vertices `⌊l⌋ + 1, …` in order,
  the end `r` lies on the walk edge of the last of them or is the next walk vertex, and an arc has
  at most `n - 1` inner vertices.
-/
namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn sideLeft IsHChordIn)
open DownHost
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **Two distinct chords attached at one position meet at a walk vertex.** -/
theorem two_chords_vertex (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {c c' : Set Point} (hc : c ∈ S) (hc' : c' ∈ S) (hcc : c ≠ c') {p : ℕ} {t : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hA' : SideAttach (interiorModel Q).W c' p t) :
    t = 0 := by
  zuhm
  zubdo
  zubl

  by_contra ht0
  have ht : ztbxd := ⟨lt_of_le_of_ne hA.2.1 ztqbb, hA.2.2.1⟩
  have hWs : I.W.Simple := (FactsInterior.interiorWalk_spec hQ).1
  have hn3 := Chazelle.Jordan.simple_three_le hWs
  zuerz
  have hne : I.W.vtx p ≠ I.W.vtx (ztr % I.W.n) := by
    zuq
    have := Chazelle.Jordan.simple_vtx_inj hWs hp ztcv h
    by_cases h1 : p + 1 < I.W.n
    · zufu
    · rw [show p + 1 = I.W.n by omega, Nat.mod_self] at this; omega
  set y := sidePt I.W p t with hy
  have hyD := hM.trace p hp t hA.2.1 hA.2.2.1.le
  obtain ⟨Y, a, b, hch, rfl⟩ := hF hc
  obtain ⟨Y', a', b', hch', rfl⟩ := hF hc'
  have hyc : y ∈ Visibility.hseg Y a b := hA.2.2.2.1
  have hyc' := hA'.2.2.2.1
  -- `y` is an endpoint of both chords
  have hend : ∀ {Y a b : ℝ}, IsHChordIn I.D Y a b → y ∈ Visibility.hseg Y a b →
      y.1 = a ∨ y.1 = b := by
    intro Y a b hch hyc
    zubq

    apply hyD
    have := hch.open_mem y.1 (lt_of_le_of_ne hyc.2.1 (Ne.symm h.1))
      (lt_of_le_of_ne hyc.2.2 h.2)
    rwa [show (ztueo : Point) = y from Prod.ext rfl hyc.1.symm] at this
  have hYY := hyc.1.symm.trans hyc'.1
  subst hYY
  obtain ⟨r, hr, hsec⟩ := hA.2.2.2.2
  obtain ⟨r', hr', hsec'⟩ := hA'.2.2.2.2
  set ε := min zteuc ztxlb / 2 with hε
  have hba := hch.lt
  have hba' := hch'.lt
  have hε0 : ztbad := by
    positivity
  have hεr : ztiee := by
    have := min_le_left zteuc ztxlb
    have := min_le_left r r'; linarith
  have hεr' : ε < r' := by
    have := min_le_left zteuc ztxlb
    have := min_le_right r r'; linarith
  have hεb : ε < b - a := by
    have := min_le_right zteuc ztxlb
    have := min_le_left zthu ztdgl; linarith
  have hεb' : ε < b' - a' := by
    have := min_le_right zteuc ztxlb
    have := min_le_right zthu ztdgl; linarith
  have hyY : y = ztueo := Prod.ext rfl hyc.1
  set zp : Point := (y.1 + ε, Y) with hzp
  set zm : Point := (y.1 - ε, Y) with hzm
  have hdp : dist zp y = ε := by
    zugtz
    simp [hzp, hyc.1, abs_of_pos hε0, hε0.le]
  have hdm : dist zm y = ε := by
    zugtz
    simp [hzm, hyc.1, abs_of_pos hε0, hε0.le]
  have hzpy : zp ≠ y := by
    grind
  have hzmy : zm ≠ y := by
    grind
  -- the determinant of the edge at `y ± ε`
  have hdet0 : det ztmbg ztxce y = 0 := by
    rw [hy]; unfold sidePt det Geometry.lerp; grind
  have hsum : det ztmbg ztxce zp +
      det ztmbg ztxce zm =
        2 * det ztmbg ztxce y := by
    rw [hyY]; unfold det; grind
  rw [hdet0] at hsum
  have hleft : ∀ {z : Point}, sideLeft I.W p t z → 0 < det _ _ z :=
    (Chazelle.Chain.sideLeft_edge hne ht _).1
  have hcommon : ∀ z, z ∈ Visibility.hseg Y a b → z ∈ Visibility.hseg Y a' b' → z ∈ I.D → False :=
    fun z hz hz' hzD => chord_disj hM hF hfin hc hc' hcc hz hz' hzD
  rcases hend hch hyc with e1 | e1 <;> rcases hend hch' hyc' with e2 | e2
  · -- both to the right
    apply hcommon zp ztbci ztbci
    zulfl
  · -- `c` to the right, `c'` to the left
    have h1 := hleft (hsec zp ztbci hzpy by_grind)
    have h2 := hleft (hsec' zm ztbci hzmy by_grind)
    linarith
  · -- `c` to the left, `c'` to the right
    have h1 := hleft (hsec zm ztbci hzmy by_grind)
    have h2 := hleft (hsec' zp ztbci hzpy by_grind)
    linarith
  · -- both to the left
    apply hcommon zm ztbci ztbci
    zulfl

/-- Attachment points of a chord of `S` are at the height of the chord. -/
theorem attach_height (hFam : (interiorModel Q).ChordFamily Q S) {c : Set Point} (hc : c ∈ S)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach (interiorModel Q).W c p t)
    (hA' : SideAttach (interiorModel Q).W c p' t') :
    (sidePt (interiorModel Q).W p t).2 = (sidePt (interiorModel Q).W p' t').2 := by
  obtain ⟨h0, -, a, b, rfl⟩ := hFam.2.2 c hc
  exact hA.2.2.2.1.1.trans hA'.2.2.2.1.1.symm

/-- Distinct heights pass to the interior walk. -/
theorem walk_distinct (hdh : DistinctHeights Q) {k k' : ℕ} (hk : k < Q.n) (hk' : k' < Q.n)
    (h : ((interiorWalk Q).vtx k).2 = ((interiorWalk Q).vtx k').2) : k = k' := by
  classical
  have hli : decide _ = true ↔ Mountain.LeftInside Q := decide_eq_true_iff
  rw [walk_vtx hli hk, walk_vtx hli hk'] at h
  zuct
  exact hdh _ _ (ivB_lt _ hk) (ivB_lt _ hk') (fun e => hne (ivB_inj _ hk hk' e)) h

/-- **Two attachment keys of one chord are on different walk edges.** -/
theorem attach_floor_ne (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hdh : DistinctHeights Q) {c : Set Point} (hc : c ∈ S) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hA' : SideAttach (interiorModel Q).W c p' t')
    (hne : (p : ℝ) + t ≠ p' + t') : p ≠ p' := by
  zunq
  have hy := attach_height hFam hc hA hA'
  zuerz
  zuixi
  zukti
  zudhw
  zuhzr
  have hd : ((interiorWalk Q).vtx p).2 ≠ ((interiorWalk Q).vtx ztwqx).2 := by
    zuq
    have := walk_distinct hdh hp hp1 h
    zuhso
    · zufu
    · zudko
  unfold sidePt at hy
  change (Geometry.lerp ztbwp ztwkf t).2 =
    (Geometry.lerp ztbwp ztwkf t').2 at hy
  rw [walk_n] at hy
  zufav
  grind
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
variable {i : ℕ}
/-- **An exit chord attached at a host key is attached at a neighbouring host key**, through a
chord gap. -/
theorem exit_chord_side (hi : i < nk ztd S R) {c : Set Point} (hc : c ∈ S)
    (ht : TouchesIn (interiorModel Q).D c R) {p : ℕ} {t : ℝ}
    (hA : SideAttach (interiorModel Q).W c p t) (hx : hk ztd S R i = p + t) :
    (ChordGap ztd S R i ∧ ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
        hk ztd S R ztwkg = p' + t') ∨
      (ChordGap ztd S R ztbajx ∧
        ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
          hk ztd S R ztbajx = p' + t') := by
  zqblm
  obtain ⟨j, hj, pa, pb, ta, tb, hAa, hAb, ea, eb, hne', -⟩ :=
    exit_chordGap hM hF hfin hR by_omega hc ht
  zuddf

  zqbln
  zuhfb
  have hxa : ztmvu := ⟨p, t, hA, hx⟩
  zuffr

  have hcases : ztbakj := by
    zuqk

    all_goals first
      | exact Or.inl (e0.trans e1.symm)
      | exact Or.inr (e0.trans e2.symm)
      | exact by_grind
  zukld
  · have := hk_inj hM hF hfin hi hj e
    zumo
    zulef
  · have := hk_inj hM hF hfin hi hsj e
    zumo
    rw [prevIdx_succ hj]
    tauto

/-- **After the end of an arc comes a chord gap**, along every exit chord attached at the end. -/
theorem end_chord (hi : i < nk ztd S R)
    (hx : hk ztd S R i ∈ exitKeys ztd S R)
    (hA : ArcGap ztd S R ztbajx) :
    ChordGap ztd S R i ∧
      ∀ c ∈ S, TouchesIn (interiorModel Q).D c R → ∀ (p : ℕ) (t : ℝ),
        SideAttach (interiorModel Q).W c p t → hk ztd S R i = p + t →
        ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
          hk ztd S R ztwkg = p' + t' := by
  zubwf
  zukh
  have hpl := prevIdx_lt (N := nk ztd S R) (i := i) by_omega
  have key : ∀ c ∈ S, TouchesIn (interiorModel Q).D c R → ∀ (p : ℕ) (t : ℝ),
      SideAttach (interiorModel Q).W c p t → hk ztd S R i = p + t →
      ChordGap ztd S R i ∧ ∃ (p' : ℕ) (t' : ℝ), SideAttach (interiorModel Q).W c p' t' ∧
        hk ztd S R ztwkg = p' + t' := by
    intro c hc ht p t hAt hxt
    rcases exit_chord_side hQ hFam hne hR hi hc ht hAt hxt with h | ⟨hC, -⟩
    · zubh
    · exact absurd hC (not_arc_and_chord hM hFam.2.1 hFam.1 by_omega hpl hA)
  obtain ⟨c, hc, ht, p, t, hAt, hxt⟩ := hx
  grind

/-- **A host key between two chord gaps is a walk vertex.** -/
theorem vertex_of_two_gaps {j : ℕ} (hj : j < nk ztd S R)
    (hC1 : ChordGap ztd S R (prevIdx ztwiy j))
    (hC2 : ChordGap ztd S R j) :
    hk ztd S R j = ⌊hk ztd S R j⌋₊ := by
  zqblm
  have hpl : prevIdx N j < N := prevIdx_lt by_omega
  zqbln
  obtain ⟨c', hc', p1, p2, t1, t2, hA1, hA2, e1, e2, -⟩ := hC1
  rw [succ_prevIdx hj] at e2
  obtain ⟨c'', hc'', q1, q2, s1, s2, hB1, hB2, f1, f2, -⟩ := hC2
  -- the two chords are distinct
  have hcc : c' ≠ c'' := by
    zunq
    obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM ztesy
    have m0 := hsub (show hk I S R _ ∈ DownDrv.attachKeys I c' from ⟨p1, t1, hA1, e1⟩)
    have m1 := hsub (show hk I S R j ∈ DownDrv.attachKeys I c' from ⟨p2, t2, hA2, e2⟩)
    have m2 := hsub (show hk I S R ztwwp ∈ DownDrv.attachKeys I c' from ⟨q2, s2, hB2, f2⟩)
    have d01 : hk I S R zttwk ≠ hk I S R j := by
      have := hk_succ_ne hM hF hfin by_omega hpl
      rwa [succ_prevIdx hj] at this
    have d12 := hk_succ_ne hM hF hfin by_omega hj
    have d02 : hk I S R zttwk ≠ hk I S R ztwwp := by
      zuq
      have := hk_inj hM hF hfin hpl hsj h
      have e := succ_prevIdx hj
      unfold prevIdx at this e
      by_cases h1 : j + 1 < N
      · zvnnn at this
        zuzo
        · simp_all
        · rw [show j + N - 1 = zthv + N by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega] at this
          omega
      · rw [show j + 1 = N by omega, Nat.mod_self, show j + N - 1 = zthv + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt by_omega] at this
        omega
    simp only [mem_insert_iff, mem_singleton_iff] at m0 m1 m2
    rcases m0 with e0 | e0 <;> rcases m1 with e1' | e1' <;> rcases m2 with e2' | e2'
    all_goals first
      | exact d01 (e0.trans e1'.symm)
      | exact d12 (e1'.trans e2'.symm)
      | exact by_simp_all
  -- both are attached at `hk j`
  obtain ⟨rfl, rfl⟩ := DownHost.key_inj hA2.2.1 hA2.2.2.1 hB1.2.1 hB1.2.2.1 (e2.symm.trans f1)
  have ht := two_chords_vertex hQ hFam hc' hc'' hcc hA2 hB1
  simp_all

/-- **Junctions** (distinct heights): a host key after a chord gap that does not start an arc
gap is a walk vertex, and the key after it starts an arc gap. -/
theorem junction (hdh : DistinctHeights Q) {i : ℕ} (hi : i < nk ztd S R)
    (hC : ChordGap ztd S R ztbajx)
    (hnA : ¬ ArcGap ztd S R i) :
    hk ztd S R i = ⌊hk ztd S R i⌋₊ ∧
      ArcGap ztd S R ztwkg := by
  zqblm
  zqblo
  have hCi :=
    (gap_cases hM hF hfin hne hR by_omega hi).resolve_left hnA
  have hv := vertex_of_two_gaps hQ hFam hne hR hi hC hCi
  zumks
  by_contra hnA2
  have hCi2 : ChordGap I S R _ :=
    (gap_cases hM hF hfin hne hR by_omega hsi).resolve_left hnA2
  have hv2 := vertex_of_two_gaps hQ hFam hne hR hsi (by rw [prevIdx_succ hi]; omega) hCi2
  obtain ⟨c, hc, q1, q2, s1, s2, hB1, hB2, f1, f2, -⟩ := hCi
  have hs1 : s1 = 0 := by
    have h1 := floor_add (p := q1) hB1.2.1 hB1.2.2.1
    grind
  have hs2 : s2 = 0 := by
    have h1 := floor_add (p := q2) hB2.2.1 hB2.2.2.1
    grind
  subst hs1 hs2
  have hy := attach_height hFam hc hB1 hB2
  simp only [Chazelle.Chain.sidePt_zero] at hy
  have hWn := walk_n Q
  have hq1 := hWn ▸ hB1.1
  have hq2 := hWn ▸ hB2.1
  have := walk_distinct hdh hq1 hq2 hy
  zumo
  exact hk_succ_ne hM hF hfin by_omega hi by_simp_all

/-- **One step along an arc gap**: the next key is the next walk vertex or on the same walk
edge. -/
theorem arcGap_step (hi : i < nk ztd S R)
    (hA : ArcGap ztd S R i) :
    (hk ztd S R ztwkg =
        ⌊hk ztd S R ztwkg⌋₊ →
      hk ztd S R ztwkg =
        (((⌊hk ztd S R i⌋₊ + 1) % Q.n : ℕ) : ℝ)) ∧
    (hk ztd S R ztwkg ≠
        ⌊hk ztd S R ztwkg⌋₊ →
      ⌊hk ztd S R ztwkg⌋₊ =
        ⌊hk ztd S R i⌋₊) := by
  zqblm
  zqblo
  zudhk

  zvnux at hbx hby
  have hnoint : ∀ k : ℕ, k < Q.n → ¬ sideInArc ztjxy (hk I S R ztxan) k :=
    fun k hk => arcGap_noInt hQ hFam hne hR hi hA k by_grind
  rcases noInt_cases hbx.1 hbx.2 hby.1 hby.2 (hk_succ_ne hM hF hfin by_omega hi) hnoint with
    ⟨hlt, hfl⟩ | hyv
  · refine ⟨fun hint => ?_, by_omega⟩
    exfalso
    zuman
    grind
  simp_all
omit hQ hFam hne hR in
/-- The gaps of an arc are arc gaps. -/
theorem arcData_gap (_hQ : Q.Simple) (_hFam : (interiorModel Q).ChordFamily Q S) (_hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r)
    (hD : ArcData ztd S R l r i_l d) {j : ℕ} (hj : j < d) :
    ArcGap ztd S R ztwsr := by
  refine ⟨l, r, harc, fun x hx0 hxn hin => hD.gaps j hj x hx0 hxn ?_⟩
  grind

/-- **The run of an arc**: the inner host keys of an arc `(l, r)` are the walk vertices
`⌊l⌋ + j` (mod `n`), `0 < j < d`; the end `r` is the walk vertex `⌊l⌋ + d` or lies on the walk
edge `⌊l⌋ + d - 1`; and `d ≤ n`. -/
theorem arc_run (hdh : DistinctHeights Q) {l r : ℝ} {i_l d : ℕ}
    (harc : (interiorModel Q).IsArc S R l r) (hD : ArcData ztd S R l r i_l d) :
    (∀ j, 0 < j → j < d →
      hk ztd S R ztwsr =
        ((ztpev % Q.n : ℕ) : ℝ)) ∧
    (ztezx ∨ ztxba) ∧
    d ≤ Q.n := by
  zuceu

  zulk
  zubl

  zukh
  have hWn : ztpkh := walk_n Q
  zudhw
  zumdn
  zumdi
  zuixv
  have hlb : 0 ≤ l ∧ l < Q.n := by
    have := hostKeys_bounds (hk_mem hM hF hfin hil); rw [hD.hl, hWn] at this; omega
  have hfl : ⌊l⌋₊ < Q.n := by
    have  := lt_of_le_of_lt ztvae hlb.2
    simp_all
  have hmod : ∀ j, ztzm % N < N := fun j => Nat.mod_lt _ by_omega
  have hsucc : ∀ j, (ztzm % N + 1) % N = ztwwf % N :=
    by grind
  -- the inner keys
  have hinner : ∀ j, 0 < j → j < d → hk I S R ztytg = ((ztpev % Q.n : ℕ) : ℝ) := by
    zumhb
    induction j with
    | zero => omega
    | succ j ih =>
      have hA := arcData_gap hQ hFam hne hR harc hD (show j < d by omega)
      obtain ⟨hint, -⟩ := arcGap_step hQ hFam hne hR ztvvq hA
      rw [hsucc j] at hint
      obtain ⟨k, hkk⟩ := (hD.inner _ hj0 hjd).1
      have hkI : hk I S R ztbaof = ⌊hk I S R ztbaof⌋₊ := by
        rw [hkk, Nat.floor_natCast]
      rw [hint hkI]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [add_zero, Nat.mod_eq_of_lt hil, hD.hl]
      · rw [ih hj by_omega, Nat.floor_natCast, Existence.mod_add_one_mod]
  -- the floor of the key before the end
  have hlast : ⌊hk I S R (ztyrb % N)⌋₊ = (⌊l⌋₊ + ztku) % Q.n := by
    rcases Nat.eq_zero_or_pos ztku with h0 | h0
    · rw [h0, add_zero, add_zero, Nat.mod_eq_of_lt hil, hD.hl, Nat.mod_eq_of_lt hfl]
    simp_all
  have hend : ztezx ∨
      ztxba := by
    have hA := arcData_gap hQ hFam hne hR harc hD ztmnv
    obtain ⟨hint, hni⟩ := arcGap_step hQ hFam hne hR (hmod _) hA
    rw [hsucc, show d - 1 + 1 = d by omega, hD.hr, hlast] at hint hni
    by_cases hr : r = ⌊r⌋₊
    · left
      refine ztuic
      have := hint hr
      rw [this, Nat.floor_natCast, Existence.mod_add_one_mod, Nat.sub_add_cancel by_grind]
    simp_all
  refine ⟨hinner, hend, ?_⟩
  -- at most `n` gaps
  by_contra hdn
  push Not at hdn
  have hinj : ∀ j j', j < N → j' < N → hk I S R ztytg = hk I S R ((i_l + j') % N) →
      j = j' := by
    intro j j' hj hj' h
    have := hk_inj hM hF hfin ztvvq (hmod j') h
    exact Existence.rot_index_inj hj hj' this
  -- two inner keys coincide if `d > n + 1`
  have hd1 : d = Q.n + 1 := by
    by_contra hne1
    zuivd
    have h2 := hinner zthcb by_omega by_omega
    rw [show ⌊l⌋₊ + zthcb = ztpeu + Q.n * 1 by ring, Nat.add_mul_mod_self_left] at h2
    have := hinj 1 _ by_omega by_omega ztmkm
    omega
  subst hd1
  -- the vertex `⌊l⌋` is the inner key `n`
  have hvn := hinner Q.n by_omega by_omega
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hfl] at hvn
  have hlni : l ≠ ⌊l⌋₊ := by
    zuq
    have e : hk I S R ((i_l + 0) % N) = hk I S R (zttpd % N) := by
      rw [add_zero, Nat.mod_eq_of_lt hil, hD.hl, hvn]; exact h
    have := hinj 0 Q.n by_omega by_omega e
    omega
  rcases hend with ⟨hr, hrv⟩ | ⟨hrni, hrfl⟩
  · -- `r` would be the inner key `1`
    rw [show ⌊l⌋₊ + zthcb = ztpeu + Q.n * 1 by ring, Nat.add_mul_mod_self_left] at hrv
    zuivd
    have e : hk I S R ((i_l + 1) % N) = hk I S R ztcrv := by
      rw [h1, hD.hr, hr, hrv]
    have := hinj 1 _ by_omega by_omega e
    omega
  · -- `l` and `r` are on one walk edge: the chord after `r` returns to that edge
    rw [Nat.add_sub_cancel, Nat.add_mod_right, Nat.mod_eq_of_lt hfl] at hrfl
    set p := ⌊l⌋₊ with hp
    have hrb : 0 ≤ r ∧ r < Q.n := by
      have := hostKeys_bounds (hk_mem hM hF hfin (hmod zthcb))
      rw [hD.hr, hWn] at this; omega
    have hlp := lt_of_le_of_ne ztvae (Ne.symm hlni)
    have hlp1 := Nat.lt_floor_add_one l
    have hrp : (p : ℝ) < r := by
      zuoro; exact lt_of_le_of_ne (Nat.floor_le hrb.1) (Ne.symm hrni)
    have hrp1 : r < p + 1 := by zuoro; exact Nat.lt_floor_add_one r
    -- the arc wraps: `r < l`
    have hrl : r < l := by
      zubq

      obtain ⟨k, hkk⟩ := (hD.inner 1 one_pos by_omega).1
      have hin := (hD.inner 1 one_pos by_omega).2
      rw [hkk] at hin
      have hlr := lt_of_le_of_ne h (WalkAx.arc_cuts hne harc).2.2
      zubix
      rw [ite_eq_left hlr] at hin
      have h1 : ztixl := by_grind
      zujyj
      have h1' : p < k := by exact_mod_cast h1
      zucgf
      omega
    -- the exit chord at `r`
    have hiN : (i_l + zthcb) % N < N := hmod _
    have hx : hk I S R ztcrv ∈ exitKeys I S R := by
      obtain ⟨c, ⟨hc, ht⟩, p', t', hA', he⟩ := hM.exists_exit_at_end hF hfin hne hR harc
      exact ⟨c, hc, ht, p', t', hA', by zuowq; exact he⟩
    have hprev : prevIdx N ztcrv = zttpd % N := by
      rw [← hsucc Q.n, prevIdx_succ (hmod Q.n)]
    have hAprev : ArcGap I S R (prevIdx N ztcrv) := by
      rw [hprev]; exact arcData_gap hQ hFam hne hR harc hD by_omega
    obtain ⟨-, hnext⟩ := end_chord hQ hFam hne hR hiN hx hAprev
    obtain ⟨c, ⟨hc, ht⟩, pr, tr, hAr, her⟩ := hM.exists_exit_at_end hF hfin hne hR harc
    obtain ⟨pz, tz, hAz, hez⟩ := hnext c hc ht pr tr hAr (by zuowq; omega)
    set z := hk I S R _ with hz
    have hzr : r ≠ z := by
      rw [← hD.hr]; exact hk_succ_ne hM hF hfin by_omega hiN
    -- `z` is a cut, so not inside the arc: `r < z ≤ l`
    have hzcut : I.IsCut S z := ztkjp
    have hzin : ¬ sideInArc l r z := fun h => harc.2.2.2.2.2.1 _ h hzcut
    unfold sideInArc at hzin
    rw [ite_eq_right (not_lt.2 hrl.le)] at hzin
    push Not at hzin
    have hrz : r < z := by_grind
    have hzfl : ⌊z⌋₊ = p := by
      rw [Nat.floor_eq_iff by_linarith]
      grind
    have hpz : pz = p := by rw [← hzfl, hez, floor_add hAz.2.1 hAz.2.2.1]
    have hpr : pr = p := by rw [← hrfl, her, floor_add hAr.2.1 hAr.2.2.1]
    exact attach_floor_ne hQ hFam hdh hc hAr hAz by_grind
      by_omega
end
end
end DownMath
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbip" : tactic => `(tactic| simp (disch := omega) only [upd_other, upd_same])
local macro "zqbiq" : tactic => `(tactic| (simp only [wr, Bool.and_eq_true] at h; simp only [wr2, ihs h.1, iht h.2, Bool.and_self]))
local macro "zqbir" : tactic => `(tactic| simp only [BhalfS, Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr)
local macro "zqbis" : tactic => `(tactic| refine spec_ifLtN_false by_omega ?_)
local macro "zqbit" : tactic => `(tactic| rw [ite_eq_right ztmjm, ite_eq_right hk])
set_option hygiene true

/-!
# WP-C (BuildNF), RAM part 2: the comparator of the event sort

The event codes `c < 2K` have records of four words at `T + 4 c` (`RecsAt`): the walk position
`wposOf L c` (edge, height code), the parity `c mod 2` and the chord `c / 2`.  `evCmp` compares
the codes in `sr 0`, `sr 1` (the registers of `SortR`) and writes into `sr 2` the bit of the
total preorder `evLeB` (`evCmp_exec`): the order `codeLe` (key, then tie bit) on codes below `2K`,
the codes below `2K` before the others, and the natural order on the others.  Each key comparison
is `keyDec` after the direction procedure of the query edge (`halfS`).
-/
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (codeLe wposOf tieBit)
@[expose] public section
open Classical in
/-- **The order of the sort**: `codeLe` on the codes below `N`, those before the others, the
natural order on the others. -/
noncomputable def evLeB (M : Model) (Q : Polygon) (L : List zte) (N a b : ℕ) : Bool :=
  if a < N then (if b < N then decide ztpaf else true)
  else (if b < N then false else decide (a ≤ b))
theorem evLeB_total (M : Model) (Q : Polygon) (L : List zte) (N a b : ℕ) :
    (evLeB M Q L N a b || evLeB M Q L N b a) = true := by
  unfold evLeB
  split_ifs <;> simp_all
  · rcases BuildNF.codeLe_total M Q L a b with h | h <;> zumxk
  · omega
theorem evLeB_trans (M : Model) (Q : Polygon) (L : List zte) (N a b c : ℕ)
    (h1 : evLeB M Q L N a b = true) (h2 : evLeB M Q L N b c = true) :
    evLeB M Q L N a c = true := by
  unfold evLeB at *
  split_ifs at h1 h2 ⊢ <;> simp_all
  · exact BuildNF.codeLe_trans M Q L h1 h2
  · omega

/-! ## The records -/

/-- **The event records** at `T`: the walk position, the parity and the chord of each code. -/
def RecsAt (m : ℕ → ℕ) (T : ℕ) (L : List zte) : Prop :=
  ∀ c, c < 2 * L.length → m ztjne = (wposOf L c).edge ∧
    m zthcu = (wposOf L c).hgt ∧ m zthcv = c % 2 ∧ m ztcly = c / 2

/-! ## The program -/

/-- Load the record of the code in `src` (address register `ad`): edge, code and parity into
`o`, `o + 1`, `o + 2`; `r42102 = 1`. -/
def loadRec (src ad o : ℕ) : Stmt :=
  block [.addN ad src src, .addN ad ad ad, .addN ad ad 42000, .loadN o ad, .addN ad ad 42102,
    .loadN ztbql ad, .addN ad ad 42102, .loadN ztdvm ad]

/-- The tie bit of parity `par` with direction code `dd` into `dst` (`r42102 = 1`,
`r42104 = 2`). -/
def tbS (dd par dst : ℕ) : Stmt :=
  .ifLtN dd 42104 ztovz
    (.ifLtN 42104 dd ztovz (.instr (.subN dst 42102 par)))

/-- Both codes in range. -/
def inCmp : Stmt :=
  .seq (block [.constN 42102 1, .constN 42104 2])
    (.seq (loadRec 30000 42101 42110) (.seq (loadRec 30001 42103 42113)
      (.seq (halfS 42113 42114 42110 42111 42116 42117)
        (.seq (halfS 42110 42111 42113 42114 42118 42119)
          (.seq ztrxk (.seq ztrxj
            (.ifLtN 42117 42102 ztlr
              (.ifLtN 42119 42102 ztjo
                ztzaa))))))))

/-- **The comparator** of the event sort. -/
def evCmp : Stmt :=
  .ifLtN 30000 42001
    (.ifLtN 30001 42001 inCmp ztjo)
    (.ifLtN 30001 42001 ztlr
      ztxft)

/-! ## The mathematics of the comparison -/
section math
variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)}
theorem wposOf_hgt (L : List zte) (c : ℕ) :
    (wposOf L c).hgt = (L.getD ztbek ztt).1 + 1 := by
  unfold wposOf; split_ifs <;> rfl

/-- The walk positions of the events are positions of the walk proper. -/
theorem properPos_ev (hL : ChordTriplesOK M zta L) {c : ℕ} (hc : c < 2 * L.length) :
    ProperPos M zta P.n ztbbg := by
  have hA := BuildNF.attach_wposOf hL hc
  zubgd
  have hh := hL.2.2.2 _ (BuildOrder.getD_mem hi)
  zubp
  refine ztrcq
  rw [wposOf_hgt]
  omega
theorem edge_lt (hL : ChordTriplesOK M zta L) {c : ℕ} (hc : c < 2 * L.length) :
    (wposOf L c).edge < M.W.n := (BuildNF.attach_wposOf hL hc).1

/-- The machine decision against an event position is the order of keys. -/
theorem keyDec_ev (hL : ChordTriplesOK M zta L) {a b : ℕ} (ha : a < 2 * L.length)
    (hb : b < 2 * L.length) :
    keyDec zta P.n ztfvf (dirCode M (wposOf L b).edge) ztdwl = true ↔
      M.key zta ztdwl ≤ M.key zta ztfvf := by
  rw [keyDec_iff (properPos_ev hL hb) (properPos_ev hL ha)]
  unfold KeyPred
  rw [ite_eq_right (by rw [wposOf_hgt]; omega)]

/-- The tie bit from the direction code. -/
theorem tieBit_eq (M : Model) (L : List zte) (c : ℕ) :
    tieBit M L c = (if dirCode M (wposOf L c).edge = 2 then 1 - c % 2 else c % 2) := by
  unfold tieBit dirCode
  by_cases h1 : (M.wa (wposOf L c).edge).2 < (M.wb (wposOf L c).edge).2
  · grind
  grind
theorem dirCode_le (M : Model) (e : ℕ) : dirCode M e ≤ 2 := by
  zuhal
end math

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}

/-- Loading a record. -/
theorem loadRec_exec (d : Config) (hw : WordsBounded W d) {src ad o : ℕ} {c T : ℕ}
    (hs : d.nreg src = c) (hT : d.nreg 42000 = T) (h1 : d.nreg 42102 = 1)
    (_hsrc : src ≠ ad) (hsT : ad ≠ 42000) (h102 : ad ≠ 42102) (hc : T + 4 * c + 2 ≤ W)
    (ho : o ≠ ad ∧ o + 1 ≠ ad ∧ o + 2 ≠ ad) (ho2 : 42102 < o ∨ o + 2 < 42102) :
    ∃ d' k, Exec P W (loadRec src ad o) d d' k ∧ k = 8 ∧
      d'.nreg o = d.nmem ztjne ∧ d'.nreg ztbql = d.nmem zthcu ∧
      d'.nreg ztdvm = d.nmem zthcv ∧
      (∀ r, r ≠ ad → r ≠ o → r ≠ o + 1 → r ≠ o + 2 → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output ∧
      d'.nreg ad = T + 4 * c + 2 := by
  zugqi
  unfold loadRec
  exec_block
  · omega
  · config_simp; omega
  · config_simp
    zuro
    omega
  · config_simp
    zqbip
    omega
  · config_simp
    zqbip
    omega
  · refine ⟨rfl, ?_, ?_, ?_, fun r r1 r2 r3 r4 => ?_, rfl, rfl, rfl, rfl, ?_⟩
    · zqbip
      grind
    · zqbip
      grind
    · zqbip
      grind
    · simp_all
    · zqbip
      omega

/-- The tie bit on the machine. -/
theorem tbS_exec (d : Config) (hw : WordsBounded W d) {dd par dst : ℕ} (h1 : d.nreg 42102 = 1)
    (h2 : d.nreg 42104 = 2) (hd : d.nreg dd ≤ 2) :
    ∃ d' k, Exec P W (tbS dd par dst) d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = (if d.nreg dd = 2 then 1 - d.nreg par else d.nreg par) := by
  unfold tbS
  by_cases a1 : d.nreg dd < 2
  · refine spec_ifLtN_true by_omega
      ztxcs
    zumb
  · have : d.nreg dd = 2 := by_omega
    refine spec_ifLtN_false by_omega
      (spec_ifLtN_false by_omega
        (spec_instr ztbbq fun _ => zteh))
    simp_all

/-- The final decision of `inCmp`. -/
theorem final_exec (d : Config) (hw : WordsBounded W d) (h1 : d.nreg 42102 = 1) :
    ∃ d' k, Exec P W (.ifLtN 42117 42102 ztlr
      (.ifLtN 42119 42102 ztjo
        ztzaa)) d d' k ∧
      k ≤ 7 ∧ d'.nreg 30002 = (if d.nreg 42117 < 1 then 0 else if d.nreg 42119 < 1 then 1 else
        if d.nreg 42121 < d.nreg 42120 then 0 else 1) := by
  by_cases a1 : d.nreg 42117 < 1
  · exact spec_ifLtN_true by_omega (spec_instr (Exec.constN hw _ _ (by
      omega)) by_simp_all)
  zqbis
  by_cases a2 : d.nreg 42119 < 1
  · exact spec_ifLtN_true by_omega (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) by_simp_all)
  zqbis
  by_cases a3 : d.nreg 42121 < d.nreg 42120
  · exact spec_ifLtN_true a3 (spec_instr (Exec.constN hw _ _ (by
      omega)) by_simp_all)
  · exact spec_ifLtN_false a3 (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 42102; omega)) by_simp_all)

/-- The registers `inCmp` writes. -/
def BinCmp (r : ℕ) : Bool :=
  decide ztdev || decide ztngj ||
    decide (42100 ≤ r ∧ r < 42200) || decide ztkdj
theorem wr_inCmp : wr BinCmp inCmp = true := by
  have h1 : ∀ qe qh se sh dd dst : ℕ, 42100 ≤ dd → dd < 42200 → 42100 ≤ dst → dst < 42200 →
      wr BinCmp ztdhn = true := fun _ _ _ _ _ _ h1 h2 h3 h4 =>
    wr_mono (fun r hr => by
      zqbir
      simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq]; omega) wr_halfS
  have e1 := h1 42113 42114 42110 42111 42116 42117 by_norm_num by_norm_num by_norm_num
    by_norm_num
  have e2 := h1 42110 42111 42113 42114 42118 42119 by_norm_num by_norm_num by_norm_num
    by_norm_num
  simp only [inCmp, wr, block, loadRec, tbS, wrOK, e1, e2, Bool.and_true, Bool.true_and]
  decide

/-- The write set of a tie-bit step. -/
theorem wr_tbS1 : wr (fun r => decide (r = 42120)) ztrxk = true := by_decide
theorem wr_tbS2 : wr (fun r => decide (r = 42121)) ztrxj = true := by_decide
open Classical in
/-- The comparison bit from the four machine bits. -/
theorem codeLe_bits {M : Model} {Q : Polygon} {L : List zte} {a b : ℕ} {x y ta tb : ℕ}
    (hx : x = if M.key Q ztdwl ≤ M.key Q ztfvf then 1 else 0)
    (hy : y = if M.key Q ztfvf ≤ M.key Q ztdwl then 1 else 0)
    (hta : ta = tieBit M L a) (htb : tb = tieBit M L b) :
    (if x < 1 then 0 else if y < 1 then 1 else if tb < ta then 0 else 1) =
      (if codeLe M Q L a b then 1 else 0) := by
  zului
  grind
open Classical in
/-- **Both codes in range**: the comparison bit of `codeLe`. -/
theorem inCmp_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config) (hw : WordsBounded W d)
    {M : Model} {L : List zte} {D T : ℕ} (hD : d.nreg 40000 = D) (hDW : D + 6 ≤ W)
    (hCW : LocChainWF P W d.nmem D) (hM : ModelDescAt d.nmem D zta M)
    (hL : ChordTriplesOK M zta L) (hT : d.nreg 42000 = T) (hR : RecsAt d.nmem T L)
    (hTW : T + 8 * L.length ≤ W) (ha : d.nreg 30000 < 2 * L.length)
    (hb : d.nreg 30001 < 2 * L.length) :
    ∃ d' k, Exec P W inCmp d d' k ∧ k ≤ 11000 ∧
      d'.nreg 30002 = (if codeLe M zta L ztqlm ztqln then 1 else 0) ∧
      FrameB BinCmp d d' := by
  set a := d.nreg 30000 with hadef
  set b := d.nreg 30001 with hbdef
  zukap
  -- constants
  obtain ⟨d₀, k₀, x₀, hk₀, r₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 42102 1, .constN 42104 2]) d
      d₀ k₀ ∧ k₀ = 2 ∧ d₀ = { d with nreg := upd (upd d.nreg 42102 1) 42104 2 } := by
    have y1 := Exec.constN (P := P) hw 42102 1 by_omega
    have y2 := Exec.constN (P := P) y1.wb_right 42104 2 by_omega
    exact ⟨_, _, .seq y1 ztffc, rfl, rfl⟩
  zugnw
  have g₀ : ∀ r, r ≠ 42102 → r ≠ 42104 → d₀.nreg r = d.nreg r := by_simp_all
  have o₀ : d₀.nreg 42102 = 1 := by_simp_all
  have t₀ : d₀.nreg 42104 = 2 := by_simp_all
  have m₀ : d₀.nmem = d.nmem := by rw [r₀]
  -- record of `a`
  obtain ⟨ha1, ha2, ha3, -⟩ := hR a ha
  obtain ⟨hb1, hb2, hb3, -⟩ := hR b hb
  obtain ⟨d₁, k₁, x₁, hk₁, e₁, h₁, p₁, g₁, m₁, -, -, -⟩ := loadRec_exec (P := P) d₀ w₀
    (src := 30000) (ad := 42101) (o := 42110) (c := a) (T := T)
    by_simp_all by_simp_all
    o₀ by_norm_num by_norm_num by_norm_num by_omega by_norm_num by_norm_num
  zubcr
  obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, p₂, g₂, m₂, -, -, -⟩ := loadRec_exec (P := P) d₁ w₁
    (src := 30001) (ad := 42103) (o := 42113) (c := b) (T := T)
    by_simp_all
    by_simp_all
    by_simp_all
    by_norm_num by_norm_num by_norm_num by_omega by_norm_num by_norm_num
  zuboj
  have mm₂ : ztmvn := by_grind
  -- register values after the loads
  have g₂₁ : ∀ r, r ≠ 42101 → r ≠ 42103 → r ≠ 42102 → r ≠ 42104 → (r < 42110 ∨ 42115 < r) →
      d₂.nreg r = d.nreg r := fun r i1 i2 i3 i4 i5 => by
    rw [g₂ r i2 by_omega by_omega by_omega, g₁ r i1 by_omega by_omega by_omega,
      g₀ r i3 i4]
  have v10 : d₂.nreg 42110 = (wposOf L a).edge := by
    grind
  have v11 : d₂.nreg 42111 = (wposOf L a).hgt := by
    grind
  have v12 : d₂.nreg 42112 = a % 2 := by
    grind
  have v13 : d₂.nreg 42113 = (wposOf L b).edge := by_grind
  have v14 : d₂.nreg 42114 = (wposOf L b).hgt := by_grind
  have v15 : d₂.nreg 42115 = b % 2 := by_grind
  have o₂ : d₂.nreg 42102 = 1 := by
    grind
  have t₂ : d₂.nreg 42104 = 2 := by
    grind
  have D₂ : ztuty := by
    rw [g₂₁ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hD]
  have ppa := properPos_ev hL ha
  have ppb := properPos_ev hL hb
  zubp
  -- first half: key a ≤ key b
  obtain ⟨d₃, k₃, x₃, hk₃, dd₃, dst₃, f₃⟩ := halfS_exec (P := P) hG hW d₂ w₂
    (qe := 42113) (qh := 42114) (se := 42110) (sh := 42111) (dd := 42116) (dst := 42117)
    by_decide by_decide by_decide by_omega by_grind
    (M := M) by_grind (by rw [v13]; exact edge_lt hL hb)
    (by zuowc; exact ppb.2.2)
  zuchd
  zuepy
  have mm₃ : ztpoi := by rw [f₃.2.2.1, mm₂]
  have D₃ : d₃.nreg 40000 = D := by rw [g₃ _ by_decide, D₂]
  -- second half: key b ≤ key a
  obtain ⟨d₄, k₄, x₄, hk₄, dd₄, dst₄, f₄⟩ := halfS_exec (P := P) hG hW d₃ w₃
    (qe := 42110) (qh := 42111) (se := 42113) (sh := 42114) (dd := 42118) (dst := 42119)
    by_decide by_decide by_decide by_omega by_grind
    (M := M) by_grind (by rw [g₃ _ by_decide, v10]; exact edge_lt hL ha)
    (by rw [g₃ _ by_decide, v11]; exact ppa.2.2)
  zujah
  zudna
  -- tie bits
  have o₄ : d₄.nreg 42102 = 1 := by rw [g₄ _ by_decide, g₃ _ by_decide, o₂]
  have t₄ : d₄.nreg 42104 = 2 := by rw [g₄ _ by_decide, g₃ _ by_decide, t₂]
  obtain ⟨d₅, k₅, x₅, hk₅, v₅⟩ := tbS_exec (P := P) d₄ w₄ (dd := 42118) (par := 42112)
    (dst := 42120) o₄ t₄ (by rw [dd₄]; exact dirCode_le _ _)
  zumga
  have f₅ := exec_frameB x₅ wr_tbS1
  have o₅ : d₅.nreg 42102 = 1 := by rw [f₅.1 _ by_decide, o₄]
  have t₅ : d₅.nreg 42104 = 2 := by rw [f₅.1 _ by_decide, t₄]
  obtain ⟨d₆, k₆, x₆, hk₆, v₆⟩ := tbS_exec (P := P) d₅ w₅ (dd := 42116) (par := 42115)
    (dst := 42121) o₅ t₅ (by rw [f₅.1 _ by_decide, g₄ _ by_decide, dd₃]; exact dirCode_le _ _)
  have w₆ := x₆.wb_right
  have f₆ := exec_frameB x₆ wr_tbS2
  have o₆ : d₆.nreg 42102 = 1 := by rw [f₆.1 _ by_decide, o₅]
  obtain ⟨d₇, k₇, x₇, hk₇, v₇⟩ := final_exec (P := P) d₆ w₆ o₆
  have X : Exec P W inCmp d d₇ _ :=
    .seq x₀ (.seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ x₇))))))
  refine ⟨d₇, _, X, by_omega, ?_, exec_frameB X wr_inCmp⟩
  zumpd
  apply codeLe_bits
  · rw [f₆.1 _ by_decide, f₅.1 _ by_decide, g₄ _ by_decide, dst₃, v13, v14, v10, v11]
    have := keyDec_ev hL ha hb
    by_cases hk : M.key zta ztdwl ≤ M.key zta ztfvf
    · zuedi
    · zqbit
  · rw [f₆.1 _ by_decide, f₅.1 _ by_decide, dst₄, g₃ _ by_decide, g₃ _ by_decide,
      g₃ _ by_decide, g₃ _ by_decide, v13, v14, v10, v11]
    have := keyDec_ev hL hb ha
    by_cases hk : M.key zta ztfvf ≤ M.key zta ztdwl
    · zuedi
    · zqbit
  · rw [f₆.1 _ by_decide, v₅, dd₄, g₄ _ by_decide, g₃ _ by_decide, g₃ _ by_decide, v10, v12,
      tieBit_eq]
  · rw [v₆, f₅.1 _ by_decide, f₅.1 _ by_decide, g₄ _ by_decide, g₄ _ by_decide, dd₃,
      g₃ _ by_decide, v13, v15, tieBit_eq]
end exec

/-! ## Separate write sets for natural and real registers -/

/-- The instruction writes a natural register accepted by `BN` or a real one accepted by `BR`. -/
def wrOK2 (BN BR : ℕ → Bool) : Instr → Bool
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => BN r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => BR r
  | .loadR r _ | .readX r _ | .readY r _ => BR r
  | _ => false

/-- Every instruction of the statement satisfies `wrOK2 BN BR`. -/
def wr2 (BN BR : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOK2 BN BR i
  | .seq s t => wr2 BN BR s && wr2 BN BR t
  | .ifLtN _ _ t e => wr2 BN BR t && wr2 BN BR e
  | .ifLtR _ _ t e => wr2 BN BR t && wr2 BN BR e
  | .whileLtN _ _ b => wr2 BN BR b
  | .whileLtR _ _ b => wr2 BN BR b

/-- The real registers outside `BR` are unchanged. -/
theorem exec_frameR {P : Polygon} {W : ℕ} {BN BR : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wr2 BN BR s = true) :
    ∀ r, BR r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact by_simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [wr2] at hs
    cases ins <;> simp only [wrOK2, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wr2, Bool.and_eq_true] at hs
    zufeo
  | ifLtN_true _ _ ih =>
    zufcg
  | ifLtN_false _ _ ih =>
    zufch
  | ifLtR_true _ _ ih =>
    zufcg
  | ifLtR_false _ _ ih =>
    zufch
  | whileLtN_false _ _ => exact by_simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj
  | whileLtR_false _ _ => exact by_simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj

/-- A single write set gives both. -/
theorem wr2_of_wr {B BN BR : ℕ → Bool} (hN : ∀ r, B r = true → BN r = true)
    (hR : ∀ r, B r = true → BR r = true) {s : Stmt} (h : wr B s = true) : wr2 BN BR s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    zvnhu at h
    simp only [wr2]
    cases i <;> simp only [wrOK] at h <;> simp only [wrOK2] <;>
      zueft
  | seq s t ihs iht =>
    zqbiq
  | ifLtN a b s t ihs iht =>
    zqbiq
  | ifLtR a b s t ihs iht =>
    zqbiq
  | whileLtN a b s ih => zvnhu at h; zunze
  | whileLtR a b s ih => zvnhu at h; zunze

/-- The real registers the comparator may write: bands `bSign` and `bBuild`. -/
def BRb (r : ℕ) : Bool := decide (bandOf r = bSign ∨ bandOf r = bBuild)
theorem wr2_evCmp : wr2 BinCmp BRb evCmp = true := by
  have h1 : ∀ qe qh se sh dd dst : ℕ, 42100 ≤ dd → dd < 42200 → 42100 ≤ dst → dst < 42200 →
      wr2 BinCmp BRb ztdhn = true := fun _ _ _ _ _ _ h1 h2 h3 h4 =>
    wr2_of_wr
      (fun r hr => by
        zqbir
        simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq]; omega)
      (fun r hr => by
        zqbir
        rw [BRb, decide_eq_true_iff]; unfold bandOf bSign bBuild
        omega) wr_halfS
  have e1 := h1 42113 42114 42110 42111 42116 42117 by_norm_num by_norm_num by_norm_num
    by_norm_num
  have e2 := h1 42110 42111 42113 42114 42118 42119 by_norm_num by_norm_num by_norm_num
    by_norm_num
  simp only [evCmp, inCmp, wr2, block, loadRec, tbS, wrOK2, e1, e2, Bool.and_true, Bool.true_and]
  decide

/-! ## The comparator contract -/

/-- The invariant of the comparator during the sort: descriptor, record table and code bound in
their registers, memory below `A₀` as at entry. -/
def EvJ (m₀ : ℕ → ℕ) (A₀ D T N : ℕ) (R : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 40000 = D ∧ d.nreg 42000 = T ∧ d.nreg 42001 = N ∧ ztecz ∧
    ∀ r, 43000 ≤ r → r < 44000 → d.nreg r = R r

/-- The invariant is insensitive to the writes of the sort. -/
theorem evJ_stable (m₀ : ℕ → ℕ) (A₀ D T N : ℕ) (R : ℕ → ℕ) :
    SortR.JStable (EvJ m₀ A₀ D T N R) A₀ := by
  intro c c' ⟨h1, h2, h3, h4, h5⟩ hr _ hm _ _
  refine ⟨?_, ?_, ?_, by_simp_all, fun r r1 r2 => ?_⟩
  · zuhlv
  · zuhlw
  · zuhlx
  · rw [hr _ ztfgf ztu, h5 r r1 r2]
theorem binCmp_band {r : ℕ} (h : BinCmp r = true) : bandOf r ∈ ({bSign, bBuild} : Finset ℕ) ∨
    r = 30002 := by
  simp only [BinCmp, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSign, bBuild]
  omega

/-- **The comparator contract** of the event sort. -/
theorem evCmp_ok {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hWn : hostWords P.n ≤ W)
    {m₀ : ℕ → ℕ} {A₀ D T : ℕ} {M : Model} {L : List zte} (hAW : A₀ ≤ W)
    (hwf : ModelDescWF P A₀ m₀ D) (hM : ModelDescAt m₀ D zta M)
    (hL : ChordTriplesOK M zta L) (hR : RecsAt m₀ T L) (hTA : T + 8 * L.length ≤ A₀)
    (R : ℕ → ℕ) : SortR.CmpOK P W evCmp {bSign, bBuild} (EvJ m₀ A₀ D T ztpu R)
      ztzep 11010 := by
  intro d hw ⟨j1, j2, j3, j4, j5⟩
  have hW1 : ztbla := by unfold hostWords at hWn; omega
  have hW : ztmd := by unfold hostWords at hWn; omega
  -- the frame part, from the write set
  have wr_ev : wr BinCmp evCmp = true := by
    simp only [evCmp, wr, wr_inCmp, Bool.true_and]; decide
  have wr2_ev := wr2_evCmp
  suffices H : ∃ d' k, Exec P W evCmp d d' k ∧ k ≤ 11010 ∧
      d'.nreg 30002 = (if evLeB M _ L _ _ _ = true
        then 1 else 0) by
    zuwp
    have f := exec_frameB x wr_ev
    refine ⟨d', k, x, hk, ⟨?_, ?_, ?_, fun a ha => ?_, fun r r1 r2 => ?_⟩, hv, fun r r0 r1 r2 hr => ?_,
      fun r hr => exec_frameR x wr2_ev r (by simpa [BRb, Finset.mem_insert, Finset.mem_singleton] using hr), f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · rw [f.1 _ by_decide, j1]
    · rw [f.1 _ by_decide, j2]
    · rw [f.1 _ by_decide, j3]
    · zunkg; simp_all
    · rw [f.1 r (by simp only [BinCmp, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
        j5 r r1 r2]
    · apply f.1
      zuldq
      rcases binCmp_band (Bool.not_eq_false _ ▸ hb) with h | h
      · zubbc
        · simp_all
        · zvnel at h; simp [bandOf, ALLOC, bSign, bBuild] at h
      omega
  unfold evCmp evLeB
  by_cases ha : d.nreg 30000 < 2 * L.length
  · zudd
    zuhbo
    · zudd
      have hm := j4
      obtain ⟨hM', hwf'⟩ := desc_agree hwf hM hm
      obtain ⟨hDW, hCW⟩ := locChainWF_of hwf' hAW hWn
      have hR' : RecsAt d.nmem T L := fun c hc => by
        obtain ⟨e1, e2, e3, e4⟩ := hR c hc
        grind
      obtain ⟨d', k, x, hk, hv, -⟩ := inCmp_exec hG hW d hw j1 hDW hCW hM' hL j2 hR'
        by_omega ha hb
      grind
    · refine spec_ifLtN_false by_omega (spec_instr ztpxv
        fun _ => zteh)
      simp_all
  · zqbis
    zuhbo
    · refine spec_ifLtN_true by_omega (spec_instr ztbbp
        fun _ => zteh)
      simp_all
    · zqbis
      by_cases hc : d.nreg 30001 < d.nreg 30000
      · refine spec_ifLtN_true hc (spec_instr ztbbp
          fun _ => zteh)
        simp [ha, hb, not_le.2 hc]
      · refine spec_ifLtN_false hc (spec_instr ztpxv
          fun _ => zteh)
        simp_all
end
end BuildRam
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbhj" : tactic => `(tactic| (zvmwo at hr
                                           zunwm; omega))
local macro "zqbhk" : tactic => `(tactic| rw [r₃ _ by_decide, f₂.1 _ by_decide, r₁ _ by_decide by_decide by_decide])
local macro "zqbhl" : tactic => `(tactic| (obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec w₁ 120114 0 by_omega
                                           obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec hq12 e₂))
local macro "zqbhm" : tactic => `(tactic| (have hmem := h.fr.2.2.1
                                           have hf1 : c.nreg 120114 = 1 := by have := h.f_le; omega
                                           have hw := h.wb))
local macro "zqbhn" : tactic => `(tactic| obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec hw 120114 0 by_omega)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), RAM part 7: the scan of a cluster

`clusS` scans the cluster of the node `c` (register `120110`): all nodes `u < μ` with the label
of `c`.  The preprocessing stores the nodes sorted by label (`ORD`) and the position of each node
in that order (`RK`); the nodes with the label `l` of `c` form a block of `ORD` around `RK[c]`:
the program walks left from `RK[c]` to the start of the block, then scans the block with
`nodeScanS`.

Registers `120110 … 120118`.  Main result: `clusS_exec`.
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
section Ord
variable (m : ℕ → ℕ) (V : QV)

/-- The label of node `u`. -/
def lab (u : ℕ) : ℕ := m ztnqb

/-- The node at position `i` of the order. -/
def ordAt (i : ℕ) : ℕ := m ztjnn

/-- The position of node `u` in the order. -/
def rkOf (u : ℕ) : ℕ := m ztnqd
end Ord

/-- **The order by label in memory.** -/
structure OrdOK (m : ℕ → ℕ) (V : QV) (W : ℕ) : Prop where
  μ_le : V.μ ≤ W
  lt : ∀ i, i < V.μ → ordAt m V i < V.μ
  inj : ∀ i j, i < V.μ → j < V.μ → ordAt m V i = ordAt m V j → i = j
  rk : ∀ u, u < V.μ → rkOf m V u < V.μ ∧ ordAt m V (rkOf m V u) = u
  sorted : ∀ i j, i ≤ j → j < V.μ → lab m V ztrud ≤ lab m V ztcdk
  ORD_le : V.ORD + V.μ ≤ W
  RK_le : V.RK + V.μ ≤ W
  LAB_le : V.LAB + V.μ ≤ W

/-- The points of the nodes with label `l`. -/
def clusPts (m : ℕ → ℕ) (V : QV) (C : Chain) (l : ℕ) : Set Point :=
  {x | ∃ u, u < V.μ ∧ lab m V u = l ∧ x ∈ nodePts m V C u}

/-- The number of nodes with label `l`. -/
noncomputable def clusSize (m : ℕ → ℕ) (V : QV) (l : ℕ) : ℕ :=
  ((Finset.range V.μ).filter fun u => lab m V u = l).card

/-! ## The program -/

/-- Read the label and the position of `c`. -/
def clusHead : Stmt := block [.addN 120111 120033 120110, .loadN 120112 120111,
  .addN 120111 120037 120110, .loadN 120113 120111, .constN 120114 1]

/-- One step left: move to `i - 1` if its node has the label, else stop. -/
def leftBody : Stmt :=
  .ifLtN 120012 120113
    (.seq (block [.subN 120115 120113 120011, .addN 120116 120036 120115, .loadN 120117 120116,
        .addN 120116 120033 120117, .loadN 120118 120116])
      (ifEq 120118 120112 (.instr (.copyN 120113 120115)) ztdsa))
    ztdsa

/-- One step right: scan the node at `i` if it has the label, else stop. -/
def fwdBody : Stmt :=
  .ifLtN 120113 120049
    (.seq (block [.addN 120116 120036 120113, .loadN 120090 120116, .addN 120116 120033 120090,
        .loadN 120118 120116])
      (ifEq 120118 120112 (.seq nodeScanS (.instr (.addN 120113 120113 120011)))
        ztdsa))
    ztdsa

/-- **The scan of the cluster of node `c`** (register `120110`). -/
def clusS : Stmt :=
  .seq clusHead (.seq (.whileLtN 120012 120114 leftBody)
    (.seq (.instr (.constN 120114 1)) (.whileLtN 120012 120114 fwdBody)))

/-- The registers written by `clusS`. -/
def BC (r : ℕ) : Bool := BN r || decide ztogh || decide (120111 ≤ r ∧ r ≤ 120118)
theorem BC_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BC r = false := by
  simp only [BC, BN, BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-! ## The block of a label -/
section Block
variable {m : ℕ → ℕ} {V : QV} {W : ℕ}

/-- Left of the start of the block, the labels are different. -/
theorem lab_ne_left (hO : OrdOK m V W) {lo l : ℕ} (hlo : lo < V.μ) (hl : lab m V (ordAt m V lo) = l)
    (hstop : lo = 0 ∨ lab m V (ordAt m V ztkah) ≠ l) {j : ℕ} (hj : j < lo) :
    lab m V ztcdk ≠ l := by
  zukmh
  · omega
  · have h1 := hO.sorted ztkah lo by_omega hlo
    have h2 := hO.sorted j ztkah by_omega by_omega
    omega

/-- Right of the end of the block, the labels are different. -/
theorem lab_ne_right (hO : OrdOK m V W) {j' hi l : ℕ} (hj' : j' < hi)
    (hl : lab m V (ordAt m V j') = l) (hstop : hi = V.μ ∨ lab m V (ordAt m V hi) ≠ l) {j : ℕ}
    (hj : hi ≤ j) (hjμ : j < V.μ) : lab m V ztcdk ≠ l := by
  zukmh
  · omega
  · have h1 := hO.sorted j' hi by_omega by_omega
    have h2 := hO.sorted hi j hj hjμ
    omega

/-- The number of positions with label `l` from `i` on. -/
noncomputable def cntFrom (m : ℕ → ℕ) (V : QV) (l i : ℕ) : ℕ :=
  ((Finset.Ico i V.μ).filter fun j => lab m V ztcdk = l).card

/-- The number of positions with label `l` before `i`. -/
noncomputable def cntBelow (m : ℕ → ℕ) (V : QV) (l i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => lab m V ztcdk = l).card
variable {l i : ℕ}
theorem cntFrom_succ (hi : i < V.μ) (hl : lab m V ztrud = l) :
    cntFrom m V l i = cntFrom m V l ztg + 1 := by
  unfold cntFrom
  have e : (Finset.Ico i V.μ).filter (fun j => lab m V ztcdk = l) =
      insert i ((Finset.Ico ztg V.μ).filter fun j => lab m V ztcdk = l) := by
    grind
  simp_all
theorem cntBelow_pred (hi : 0 < i) (hl : lab m V (ordAt m V ztei) = l) :
    cntBelow m V l i = cntBelow m V l ztei + 1 := by
  zujqi
  have e : Finset.range i = insert ztei (Finset.range ztei) := by
    grind
  rw [e, Finset.filter_insert, ite_eq_left hl, Finset.card_insert_of_notMem by_simp]

/-- The positions with label `l` correspond to the nodes with label `l`. -/
theorem card_positions (hO : OrdOK m V W) (l : ℕ) :
    ((Finset.range V.μ).filter fun j => lab m V ztcdk = l).card = clusSize m V l := by
  unfold clusSize
  rw [← Finset.card_image_of_injOn
    (fun i hi j hj h => hO.inj i j by_simp_all
      by_simp_all h)]
  zucr
  ext u
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hl⟩, rfl⟩; exact ⟨hO.lt i hi, hl⟩
  · rintro ⟨hu, hl⟩
    exact ⟨rkOf m V u, ⟨(hO.rk u hu).1, by rw [(hO.rk u hu).2]; exact hl⟩, (hO.rk u hu).2⟩
theorem cntFrom_le (l i : ℕ) : cntFrom m V l i ≤
    ((Finset.range V.μ).filter fun j => lab m V ztcdk = l).card := by
  unfold cntFrom
  zulcz
  grind
theorem cntBelow_le (l i : ℕ) (hi : i ≤ V.μ) : cntBelow m V l i ≤
    ((Finset.range V.μ).filter fun j => lab m V ztcdk = l).card := by
  zujqi
  zulcz
  grind
end Block

/-! ## The left walk -/

/-- **The invariant of the left walk.** -/
structure LInv (P : Polygon) (W : ℕ) (V : QV) (c₀ : Config) (l r0 : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  fr : FrameB ztijt c₀ c
  rl : c.nreg 120112 = l
  f_le : c.nreg 120114 ≤ 1
  i_le : c.nreg 120113 ≤ r0
  blk : ∀ j, c.nreg 120113 ≤ j → j ≤ r0 → lab c₀.nmem V ztftq = l
  stop : c.nreg 120114 = 0 → c.nreg 120113 = 0 ∨
    lab c₀.nmem V (ordAt c₀.nmem V (c.nreg 120113 - 1)) ≠ l
variable {P : Polygon}
theorem leftBody_inv {W : ℕ} {V : QV} {c₀ : Config} {l r0 : ℕ}
    (hq : QConst P V c₀) (hO : OrdOK c₀.nmem V W) (hr0 : r0 < V.μ) {c : Config}
    (h : LInv P W V c₀ l r0 c) (ht : c.nreg 120012 < c.nreg 120114) :
    ∃ c' k, Exec P W leftBody c c' k ∧ LInv P W V c₀ l r0 c' ∧
      13 * (cntBelow c₀.nmem V l ztvgc + c'.nreg 120114) + k + 2 ≤
        13 * (cntBelow c₀.nmem V l ztccr + c.nreg 120114) := by
  have hq' := hq.frame h.fr by_grind
  zqbhm
  have stopF : ∀ c' : Config, Exec P W leftBody c c' 1 → True := by_simp_all
  by_cases hi0 : 0 < ztccr
  swap
  · -- at the left end
    zqbhn
    refine ⟨c₁, _, .ifLtN_false by_omega e₁, ⟨e₁.wb_right, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (FrameB.mono (exec_frameB e₁ (B := fun r => decide zthjz)
        by_decide) by_simp_all)
    · zvmww; exact h.rl
    · omega
    · simp_all
    · intro j hj; zvmww at hj; exact h.blk j hj
    · simp_all
    grind
  have hir := h.i_le
  have hu : ordAt c₀.nmem V (ztccr - 1) < V.μ := hO.lt _ by_omega
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 120115 120113 120011,
      .addN 120116 120036 120115, .loadN 120117 120116, .addN 120116 120033 120117,
      .loadN 120118 120116]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 120115 = ztccr - 1 ∧ c₁.nreg 120118 = lab c₀.nmem V ztyjv ∧
        (∀ r, r < 120115 ∨ 120118 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hORD := hO.ORD_le
    have hLAB := hO.LAB_le
    exec_block
    · config_simp; rw [hq'.ORD, hq'.one]; omega
    · config_simp; zunth
      zujvx

    · refine ztfwy
      · config_simp; rw [hq'.one]
      · config_simp; zunth; rfl
      · config_simp; upd_solve
  obtain ⟨x115, x118, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  zud
  have fr₁ : FrameB ztijt c c₁ :=
    FrameB.mono (exec_frameB e₁ (B := fun r => decide (120115 ≤ r ∧ r ≤ 120118)) by_decide)
      fun r hr => by_grind
  by_cases heq : lab c₀.nmem V ztyjv = l
  · -- move left
    have hq12 : ztsfz := by
      rw [x118, r₁ _ by_omega, h.rl, heq]
    obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec w₁ 120113 120115
    rw [x115] at v₂
    refine ⟨c₂, _, .ifLtN_true by_omega (.seq e₁ (ifEq_eq_exec hq12 e₂)),
      ⟨e₂.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (fr₁.trans (FrameB.mono (exec_frameB e₂ (B := fun r => decide zttxm)
        by_decide) by_simp_all))
    · simp_all
    · simp_all
    · omega
    · intro j hj hjr
      rw [v₂] at hj
      rcases Nat.eq_or_lt_of_le hj with e | e
      · simp_all
      · exact h.blk j by_omega hjr
    · simp_all
    · rw [v₂, r₂ _ by_decide, r₁ _ by_omega, cntBelow_pred hi0 heq]; omega
  · -- stop
    have hq12 : ztsga := by
      rw [x118, r₁ _ by_omega, h.rl]; omega
    zqbhl
    refine ⟨c₂, _, .ifLtN_true by_omega ztsqc,
      ⟨e₂.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (fr₁.trans (FrameB.mono (exec_frameB e₂ (B := fun r => decide zthjz)
        by_decide) by_simp_all))
    · rw [r₂ _ by_decide, r₁ _ by_omega]; exact h.rl
    · omega
    · simp_all
    · intro j hj; rw [r₂ _ by_decide, r₁ _ by_omega] at hj; exact h.blk j hj
    · simp_all
    grind

/-! ## The forward walk -/

/-- **The invariant of the forward walk.** -/
structure FInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (l lo : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  fr : FrameB BC c₀ c
  rl : c.nreg 120112 = l
  f_le : c.nreg 120114 ≤ 1
  lo_le : lo ≤ c.nreg 120113
  i_le : c.nreg 120113 ≤ V.μ
  blk : ∀ j, lo ≤ j → j < c.nreg 120113 → lab c₀.nmem V ztftq = l
  stop : c.nreg 120114 = 0 → c.nreg 120113 = V.μ ∨
    lab c₀.nmem V ztxok ≠ l
  hit : Sweep.FirstHitOpt (S ∪ {x | ∃ j, lo ≤ j ∧ j < c.nreg 120113 ∧
      x ∈ nodePts c₀.nmem V C ztftq}) z (sgnOf V.σb)
    ztwmd
theorem fwdBody_inv {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point}
    {l lo NC : ℕ} (hm : QMem V c₀.nmem W) (hO : OrdOK c₀.nmem V W)
    (hNC : ∀ u, u < V.μ → nodeCost c₀.nmem V u ≤ NC) {c : Config}
    (h : FInv P W C V z c₀ S l lo c) (ht : c.nreg 120012 < c.nreg 120114) :
    ∃ c' k, Exec P W fwdBody c c' k ∧ FInv P W C V z c₀ S l lo c' ∧
      zthbo * cntFrom c₀.nmem V l ztvgc + 60 * c'.nreg 120114 + k + 2 ≤
        zthbo * cntFrom c₀.nmem V l ztccr + 60 * c.nreg 120114 := by
  zqbhm
  have fconst : ∀ (c₂ : Config) (e₂ : Exec P W ztdsa c c₂ 1),
      FrameB BC c c₂ := fun c₂ e₂ => FrameB.mono (exec_frameB e₂ (B := fun r => decide zthjz)
        by_decide) fun r hr => by
          zqbhj
  by_cases hiμ : c.nreg 120113 < V.μ
  swap
  · zqbhn
    have f₁ := fconst c₁ e₁
    refine ⟨c₁, _, .ifLtN_false zthep e₁, ⟨e₁.wb_right, h.q.frame f₁ BC_const,
      ?_, h.fr.trans f₁, by zvmww; exact h.rl, by_omega,
      by zvmww; exact h.lo_le, by zvmww; exact h.i_le,
      by zvmww; exact h.blk, fun _ => by
        left; zvmww; have := h.i_le; omega, ?_⟩, ?_⟩
    · zucku
      zuniv; exact h.b
    · have hbo : ztguc := by
        zubqh
      rw [hbo, r₁ _ by_decide]; exact h.hit
    simp_all
  have hu : ordAt c₀.nmem V _ < V.μ := hO.lt _ hiμ
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 120116 120036 120113,
      .loadN 120090 120116, .addN 120116 120033 120090, .loadN 120118 120116]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 120090 = ordAt c₀.nmem V ztccr ∧
        c₁.nreg 120118 = lab c₀.nmem V ztxok ∧
        (∀ r, r ≠ 120090 → r ≠ 120116 → r ≠ 120118 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hORD := hO.ORD_le
    have hLAB := hO.LAB_le
    exec_block
    · rw [h.q.ORD]; omega
    · config_simp; zunzx
      zujvx

    · refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [h.q.ORD, hmem]; rfl
      · config_simp; zunzx; rfl
      simp_all
  obtain ⟨x90, x118, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  zud
  have fr₁ : ztukq :=
    FrameB.mono (exec_frameB e₁ (B := fun r => decide ztogh || decide (r = 120116) ||
      decide (r = 120118)) by_decide) fun r hr => by
        zufw
        zunwm; omega
  have hq₁ := h.q.frame fr₁ BC_const
  have hbo₁ : ztguc := by
    zubqh
  have hb₁ : ztiyc := by
    zucku
    rw [r₁ 120050 by_decide by_decide by_decide, r₁ 120051 by_decide by_decide
      by_decide, r₁ 120052 by_decide by_decide by_decide]; exact h.b
  by_cases heq : lab c₀.nmem V ztxok = l
  · have hq12 : ztsfz := by
      rw [x118, r₁ _ by_decide by_decide by_decide, h.rl, heq]
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := nodeScan_exec hG hW hs c₁ w₁ hq₁ hb₁
      by_simp_all
      ztgfu
    rw [x90, m₁, hmem] at hk₂ hit₂
    have hq₂ := hq₁.frame f₂ BN_const
    have x113 : c₂.nreg 120113 = ztccr :=
      (f₂.1 _ by_decide).trans by_simp_all
    obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec e₂.wb_right 120113 120113 120011
      (by rw [x113, hq₂.one]; have := hO.μ_le; omega)
    rw [x113, hq₂.one] at v₃
    have f₂' : ztpkc := FrameB.mono f₂ fun r hr => by
      simp only [BC, hr, Bool.true_or]
    have f₃ : ztukr := FrameB.mono (exec_frameB e₃ (B := fun r => decide zttxm)
      by_decide) fun r hr => by
        zqbhj
    have ex : Exec P W _ c₁ c₃ _ :=
      .seq e₂ e₃
    refine ⟨c₃, _, .ifLtN_true zthep (.seq e₁ (ifEq_eq_exec hq12 ex)),
      ⟨e₃.wb_right, hq₂.frame f₃ BC_const, ?_, h.fr.trans (fr₁.trans (f₂'.trans f₃)), ?_, ?_,
        by rw [v₃]; have := h.lo_le; omega, by_omega, ?_, ?_, ?_⟩, ?_⟩
    · zucku
      zuniu; exact hb₂
    · zqbhk
      simp_all
    · zqbhk
      omega
    · intro j hj hji
      rw [v₃] at hji
      rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h' | rfl
      · exact h.blk j hj h'
      omega
    · zuhgo
      rw [r₃ _ by_decide, f₂.1 _ by_decide, r₁ _ by_decide by_decide by_decide] at hf
      omega
    · have hbo : ztmug := by
        zubqh
      zugdo
      have e : {x | ∃ j, lo ≤ j ∧ j < ztccr + 1 ∧ x ∈ nodePts c₀.nmem V C ztftq} =
          {x | ∃ j, lo ≤ j ∧ j < ztccr ∧ x ∈ nodePts c₀.nmem V C ztftq} ∪
            nodePts c₀.nmem V C ztxok := by
        zumx
        zujny
        constructor
        · grind
        · rintro (⟨j, h1, h2, hx⟩ | hx)
          · grind
          · exact ⟨ztccr, h.lo_le, by_omega, hx⟩
      grind
    · have hk2' : k₂ ≤ NC := by_grind
      rw [v₃, r₃ _ by_decide, f₂.1 _ by_decide, r₁ _ by_decide by_decide by_decide,
        hf1, cntFrom_succ hiμ heq, Nat.mul_add, Nat.mul_one]
      omega
  · have hq12 : ztsga := by
      rw [x118, r₁ _ by_decide by_decide by_decide, h.rl]; omega
    zqbhl
    have f₂ : ztpkc := FrameB.mono (exec_frameB e₂ (B := fun r => decide zthjz)
      by_decide) fun r hr => by
        zqbhj
    have R : ∀ r, r ≠ 120114 → r ≠ 120090 → r ≠ 120116 → r ≠ 120118 → c₂.nreg r = c.nreg r :=
      by simp_all
    refine ⟨c₂, _, .ifLtN_true zthep ztsqc,
      ⟨e₂.wb_right, hq₁.frame f₂ BC_const, ?_, h.fr.trans (fr₁.trans f₂),
        by zunfj; exact h.rl, by_omega,
        by zunfj; exact h.lo_le,
        by grind,
        by zunfj; exact h.blk,
        by simp_all,
        ?_⟩, ?_⟩
    · zucku
      rw [R 120050 by_decide by_decide by_decide by_decide,
        R 120051 by_decide by_decide by_decide by_decide,
        R 120052 by_decide by_decide by_decide by_decide]; exact h.b
    · have hbo : ztmue := by
        zulbi
        simp_all
      rw [hbo, R _ by_decide by_decide by_decide by_decide]; exact h.hit
    grind

/-! ## The scan of a cluster -/

/-- **The scan of the cluster of node `c`** (register `120110`). -/
theorem clusS_exec {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    (hcμ : c.nreg 120110 < V.μ) {NC : ℕ} (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z zthx ztwmd) :
    ∃ c' k, Exec P W clusS c c' k ∧
      k ≤ (clusSize c.nmem V ztocq + 2) * ztdft ∧
      FrameB BC c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ clusPts c.nmem V C ztocq) z zthx
        ztwot := by
  obtain ⟨u₀, hu₀⟩ : ∃ u, c.nreg 120110 = u := by_simp_all
  rw [hu₀] at hcμ ⊢
  obtain ⟨l, hl⟩ : ∃ l, lab c.nmem V u₀ = l := by_simp_all
  zudug
  obtain ⟨hr0μ, hr0u⟩ := hO.rk u₀ hcμ
  obtain ⟨r0, hr0⟩ : ∃ r, rkOf c.nmem V u₀ = r := by_simp_all
  rw [hr0] at hr0μ hr0u
  have hLAB := hO.LAB_le
  have hRK := hO.RK_le
  -- 1. the head
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W clusHead c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 120112 = l ∧ c₁.nreg 120113 = r0 ∧ c₁.nreg 120114 = 1 ∧
        (∀ r, r < 120111 ∨ 120114 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold clusHead
    exec_block
    · zuoms; omega
    · config_simp; zuomt; omega
    · omega
    · refine ⟨rfl, ?_, ?_, by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; zuoms; exact hl
      · config_simp; zuomt; tauto
      · config_simp; upd_solve
  obtain ⟨x112, x113, x114, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have fr₁ : FrameB (fun r => decide (120111 ≤ r ∧ r ≤ 120114)) c c₁ :=
    exec_frameB e₁ by_decide
  have hq₁ := hq.frame fr₁ by_grind
  -- 2. the left walk
  have L₀ : LInv P W V c₁ l r0 c₁ := by
    refine ⟨e₁.wb_right, FrameB.refl _ _, x112, by_omega, by_omega, fun j h1 h2 => ?_,
      by simp_all⟩
    grind
  obtain ⟨c₂, k₂, e₂, L₂, hex₂, hk₂⟩ := Exec.whileLtN_potential (a := 120012) (b := 120114)
    (LInv P W V c₁ l r0) (fun d => 13 * (cntBelow c₁.nmem V l ztvoi + d.nreg 120114))
    ztpf
    (fun d hd ht => leftBody_inv (P := P) hq₁ by_simp_all hr0μ hd ht) L₀
  have hq₂ := hq₁.frame L₂.fr by_grind
  have hf2 : c₂.nreg 120114 = 0 := by rw [hq₂.zero] at hex₂; omega
  obtain ⟨lo, hlo⟩ : ∃ lo, c₂.nreg 120113 = lo := by_simp_all
  have hlo_r0 : lo ≤ r0 := by rw [← hlo]; exact L₂.i_le
  have hloμ : lo < V.μ := by_omega
  have hstop := L₂.stop hf2
  rw [hlo] at hstop
  -- 3. the forward walk
  obtain ⟨c₃, e₃, v₃, r₃⟩ := const_exec (P := P) L₂.wb 120114 1 by_omega
  have fr₃ : FrameB (fun r => decide zthjz) c₂ c₃ := exec_frameB e₃ by_decide
  have mm : ztckd := by rw [fr₃.2.2.1, L₂.fr.2.2.1, m₁]
  have R₃ : ∀ r, (r < 120111 ∨ 120118 < r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [r₃ r by_omega, L₂.fr.1 r by_grind,
      r₁ r by_omega]
  have x3 : c₃.nreg 120113 = lo := by_simp_all
  have F₀ : FInv P W C V z c₃ S l lo c₃ := by
    refine ⟨e₃.wb_right, hq₂.frame fr₃ by_grind,
      ?_, FrameB.refl _ _, ?_, by rw [v₃], by rw [x3], by_omega,
      by simp_all, by_simp_all, ?_⟩
    · zucku
      rw [R₃ 120050 by_omega, R₃ 120051 by_omega, R₃ 120052 by_omega]; exact hb
    · rw [r₃ _ by_decide, L₂.fr.1 _ by_decide, x112]
    · have hbo : ztmuf := by
        zubqh
      rw [hbo, x3]
      have : {x | ∃ j, lo ≤ j ∧ j < lo ∧ x ∈ nodePts c₃.nmem V C zthzc} = ∅ := by
        grind
      simp_all
  obtain ⟨c₄, k₄, e₄, F₄, hex₄, hk₄⟩ := Exec.whileLtN_potential (a := 120012) (b := 120114)
    (FInv P W C V z c₃ S l lo)
    (fun d => zthbo * cntFrom c₃.nmem V l ztvoi + 60 * d.nreg 120114)
    ztpf
    (fun d hd ht => fwdBody_inv (P := P) hG hW hs by_simp_all by_simp_all
      ztcid hd ht) F₀
  have hf4 : c₄.nreg 120114 = 0 := by rw [F₄.q.zero] at hex₄; omega
  obtain ⟨hi, hhi⟩ : ∃ hi, c₄.nreg 120113 = hi := by_simp_all
  have hstop4 := F₄.stop hf4
  rw [hhi] at hstop4
  have hlo4 : lo ≤ hi := by zuosq; exact F₄.lo_le
  have hhiμ : hi ≤ V.μ := by zuosq; exact F₄.i_le
  -- the block is `[lo, hi)`
  have m13 : c₁.nmem = c₃.nmem := by_simp_all
  have hO3 : OrdOK c₃.nmem V W := by_simp_all
  rw [← mm]
  have hblkL : ∀ j, lo ≤ j → j ≤ r0 → lab c₃.nmem V zthzc = l := by
    intro j h1 h2; rw [← m13]; exact L₂.blk j by_omega h2
  have hr0hi : r0 < hi := by
    grind
  have hstop' : lo = 0 ∨ lab c₃.nmem V (ordAt c₃.nmem V ztkah) ≠ l := by
    simp_all
  have hmemb : ∀ j, j < V.μ → (lab c₃.nmem V zthzc = l ↔ lo ≤ j ∧ j < hi) := by
    zun
    constructor
    · intro hjl
      zujx
      · zuca
        exact lab_ne_left hO3 hloμ by_simp_all hstop' hc hjl
      · zuca
        exact lab_ne_right hO3 hr0hi by_simp_all hstop4 hc hj hjl
    · rintro ⟨h1, h2⟩; exact F₄.blk j h1 by_omega
  refine ⟨c₄, _, .seq e₁ ztcb, ?_, ?_, F₄.b, ?_⟩
  · -- the cost
    have hcs := card_positions hO3 l
    have hc1 : cntBelow c₁.nmem V l r0 ≤ clusSize c₃.nmem V l := by
      rw [← hcs, m13]; exact cntBelow_le l r0 hr0μ.le
    have hc2 : cntFrom c₃.nmem V l lo ≤ clusSize c₃.nmem V l := by
      rw [← hcs]; exact cntFrom_le l lo
    rw [x113, x114] at hk₂
    rw [x3, v₃] at hk₄
    have h1 : zthbo * cntFrom c₃.nmem V l lo ≤ zthbo * clusSize c₃.nmem V l :=
      Nat.mul_le_mul_left _ hc2
    grind
  · have f₂' : ztpkc := FrameB.mono L₂.fr fun r hr => by
      zqbhj
    have f₁' : ztukq := FrameB.mono fr₁ fun r hr => by
      zqbhj
    have f₃' : ztukr := FrameB.mono fr₃ fun r hr => by
      zqbhj
    exact f₁'.trans (f₂'.trans (f₃'.trans F₄.fr))
  · have e : clusPts c₃.nmem V C l =
        {x | ∃ j, lo ≤ j ∧ j < c₄.nreg 120113 ∧ x ∈ nodePts c₃.nmem V C zthzc} := by
      rw [hhi]
      zumx
      simp only [clusPts, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, hu, hul, hx⟩
        obtain ⟨hru, hru'⟩ := hO3.rk u hu
        grind
      · rintro ⟨j, h1, h2, hx⟩
        have hjμ : j < V.μ := by_omega
        exact ⟨ordAt c₃.nmem V j, hO3.lt j hjμ, by_grind, hx⟩
    zvmwe; exact F₄.hit
end
end OracleR
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbks" : tactic => `(tactic| (obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁, v₁, s₁⟩ := after_xp (P := P) hW hv c hw hq
                                           have hn : ztbof := by_omega))
local macro "zqbkt" : tactic => `(tactic| (intro hc1
                                           rw [v₁] at hc1
                                           have hpt := s₁ hc1
                                           have hl := xpSym_lt (C := C) (w := c.nreg 120120) hn htv hh))
local macro "zqbku" : tactic => `(tactic| (obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec (P := P) e₂.wb_right 120128 10010
                                           refine ⟨c₃, _, .seq e₂ e₃, by_omega, by_omega, ?_⟩
                                           rw [v₃, g₂]))
local macro "zqbkv" : tactic => `(tactic| (refine ⟨c₂, _, .ifLtN_false (by rw [hk2, hq₁.two]; omega) e₂, by_omega, ?_, ?_⟩))
local macro "zqbkw" : tactic => `(tactic| obtain ⟨d', k, ex, hk, a, b⟩ := vtxcase by_omega c₂ e₂.wb_right v₂ hq₂.tv)
local macro "zqbkx" : tactic => `(tactic| rcases hq₁.org with ⟨hk2, hzo⟩ | ⟨hk2, p, hp, hpin, hzo⟩)
local macro "zqbky" : tactic => `(tactic| obtain ⟨w, hwdef⟩ : ∃ w, c.nreg 120120 = w := by_simp_all)
local macro "zqbkz" : tactic => `(tactic| rw [v₂, v₁])
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), RAM part 8: the abscissa of a chord endpoint

A chord endpoint is stored as a walk position `(w, h + 1)`.  Its abscissa is `-r` on the left
side of the box (`w = 1`, class `0`), `r` on the right side (`w = 3`, class `2`), and otherwise
(class `1`) the abscissa of a symbolic point of `Q`: the point of the chain edge of the tour edge
`w` at the height of `h`, or the top vertex (for the slit edges).

`xpS` computes the class (register `120122`) and the symbolic point (`120123 …`) from `w`
(`120120`) and `h` (`120121`).  Main result: `xpS_exec`.
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def xpClass (w : ℕ) : ℕ := if w = 1 then 0 else if w = 3 then 2 else 1
open Classical in
/-- The symbolic point with the abscissa of the endpoint `(w, h + 1)` (class `1`). -/
noncomputable def xpSym (C : Chain) (V : QV) (n w h : ℕ) : SymPt :=
  if 6 ≤ w ∧ w < 2 * V.m + 6 then .onEdge (eIdx n V.s ztyrz) h else .vtx V.tv

/-- The vertex part. -/
def xpVtx : Stmt := block [.constN 120123 0, .copyN 120124 120022]

/-- The edge part: the chain edge of the tour edge `w - 6`, its edge of `Q`, and the height. -/
def xpEdge : Stmt :=
  .seq ztiqx
    (.seq (modSub 120127 120019)
      (.seq (.ifLtN 120127 120016 ztouy
          ztebz)
        (.seq (.instr (.addN 120126 120126 120015))
          (.seq (modSub 120126 120010)
            zthsf))))

/-- **The class and symbolic point of the endpoint** `(w, h + 1)`. -/
def xpS : Stmt :=
  ifEq 120120 120011 (.instr ztsop)
    (.seq (.instr (.constN 120126 3))
      (ifEq 120120 120126 (.instr ztsoq)
        (.seq (.instr (.constN 120122 1))
          ztjcw)))

/-- The registers written by `xpS`. -/
def BX (r : ℕ) : Bool := decide (120122 ≤ r ∧ r ≤ 120127)
theorem wr_xpS : wr BX xpS = true := by_decide
theorem xpSym_lt {C : Chain} {V : QV} {n w h : ℕ} (hn : 0 < n) (htv : V.tv < n) (hh : h < n) :
    (xpSym C V n w h).Lt n := by
  unfold xpSym
  split_ifs
  · exact ⟨Nat.mod_lt _ hn, hh⟩
  tauto
theorem xpVtx_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W xpVtx c c' k ∧ k = 2 ∧ c'.nreg 120123 = 0 ∧ c'.nreg 120124 = c.nreg 120022 ∧
      (∀ r, r ≠ 120123 → r ≠ 120124 → c'.nreg r = c.nreg r) := by
  unfold xpVtx
  exec_block
  · omega
  simp_all
theorem xpEdge_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c)
    (h6 : 6 ≤ c.nreg 120120) (hE : c.nreg 120120 < 2 * V.m + 6) :
    ∃ c' k, Exec P W xpEdge c c' k ∧ k ≤ 20 ∧ c'.nreg 120123 = 1 ∧
      c'.nreg 120124 = eIdx P.n V.s (tci C (c.nreg 120120 - 6)) ∧
      c'.nreg 120125 = c.nreg 120121 ∧
      (∀ r, r < 120123 ∨ 120127 < r → c'.nreg r = c.nreg r) := by
  have hmn : ztgaj := by
    have := C.m_lt; zvmxw at this; omega
  zubb
  zubqz
  zqbky
  zuiks
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      ztiqx c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120127 = w - 6 + V.sS ∧ (∀ r, r ≠ 120127 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hq.six, hq.sS, hwdef]; rw [hv.m] at hE; omega
    · zuhjd
      · config_simp; rw [hq.six, hq.sS, hwdef]
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120127) (nr := 120019)
    by_decide c₁ e₁.wb_right ztezr
  zubsp
  have htj : c₂.nreg 120127 = tj C ztvu := by
    zubmg
  have R₂ : ∀ r, r ≠ 120127 → c₂.nreg r = c.nreg r := by_simp_all
  zufwp
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120127 120016 ztouy
        ztebz) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 120126 = tci C ztvu ∧ ztiuy := by
    zupn

    · refine ⟨_, _, .ifLtN_true by_omega ztlei,
        by omega, ?_, fun r hr => ?_⟩
      · config_simp; rw [htj]; unfold tci; simp_all
      simp_all
    · zue
      obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
          ztebz c₂ c₃ k₃ ∧ k₃ = 2 ∧
          c₃.nreg 120126 = 2 * C.m - 1 - tj C _ ∧
          ztiuy := by
        exec_block
        zuhjd
        · config_simp
          rw [R₂ _ by_decide, R₂ _ by_decide, hq.twoM, hq.one, htj, hv.m]
        simp_all
      refine ztiof
      zudkr
  have hci := tci_lt C ztvu
  obtain ⟨c₄, e₄, v₄, r₄, -⟩ := add_exec (P := P) e₃.wb_right 120126 120126 120015 (by
    rw [v₃, r₃ _ by_decide, R₂ _ by_decide, hq.s]; have := hv.s_lt; omega)
  rw [v₃, r₃ _ by_decide, R₂ _ by_decide, hq.s] at v₄
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅, -⟩ := modSub_exec (P := P) (r := 120126) (nr := 120010)
    by_decide c₄ e₄.wb_right (by
      rw [v₄, r₄ _ by_decide, r₃ _ by_decide, R₂ _ by_decide, hq.n]
      have := hv.s_lt; omega)
  rw [v₄, r₄ _ by_decide, r₃ _ by_decide, R₂ _ by_decide, hq.n] at v₅
  obtain ⟨c₆, k₆, e₆, hk₆, v₆⟩ : ∃ c₆ k₆, Exec P W
      zthsf c₅ c₆ k₆ ∧ k₆ = 3 ∧
      (c₆.nreg 120123 = 1 ∧ c₆.nreg 120124 = c₅.nreg 120126 ∧ c₆.nreg 120125 = c₅.nreg 120121 ∧
        ∀ r, r ≠ 120123 → r ≠ 120124 → r ≠ 120125 → c₆.nreg r = c₅.nreg r) := by
    zuef
    exec_block
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp,
        by simp_all⟩
  obtain ⟨x123, x124, x125, r₆⟩ := v₆
  have R : ∀ r, (r < 120123 ∨ 120127 < r) → c₆.nreg r = c.nreg r := fun r hr => by
    rw [r₆ r by_omega by_omega by_omega, r₅ r by_omega, r₄ r by_omega, r₃ r by_omega,
      R₂ r by_omega]
  refine ⟨c₆, _, .seq e₁ ztfv, by_omega, x123, ?_, ?_, R⟩
  · rw [x124, v₅]; unfold eIdx; grind
  · rw [x125, r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide, R₂ _ by_decide]
open Classical in
/-- **The class and symbolic point of the endpoint** `(w, h + 1)` (`w` in `120120`, `h` in
`120121`). -/
theorem xpS_exec {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c' k, Exec P W xpS c c' k ∧ k ≤ 40 ∧ FrameB BX c c' ∧
      c'.nreg 120122 = xpClass ztcpo ∧
      (xpClass ztcpo = 1 →
        SymPtIn c' 120123 ztyxh) := by
  suffices H : ∃ c' k, Exec P W xpS c c' k ∧ k ≤ 40 ∧
      c'.nreg 120122 = xpClass _ ∧
      (xpClass _ = 1 →
        SymPtIn c' 120123 _) by
    zudqy
    exact ⟨c', k, ex, hk, exec_frameB ex wr_xpS, h1, h2⟩
  zqbky
  zumoi
  by_cases h1 : w = 1
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 120122 0 by_omega
    refine ⟨c₁, _, ifEq_eq_exec (by rw [hwdef, hq.one, h1]) e₁, by_omega, ?_, ?_⟩
    · rw [v₁]; unfold xpClass; simp_all
    · zuhgm
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120126 3 by_omega
  by_cases h3 : w = 3
  · obtain ⟨c₂, e₂, v₂, -⟩ := const_exec e₁.wb_right 120122 2 by_omega
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (b := 120011)
      ztktw
      (.seq e₁ (ifEq_eq_exec (a := 120120) (b := 120126)
        by_simp_all e₂))
    refine ⟨c₂, k', ex', by_omega, ?_, ?_⟩
    · rw [v₂]; unfold xpClass; simp_all
    · zuhgm
  have hcl : xpClass w = 1 := by unfold xpClass; simp_all
  rw [hcl]
  obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) e₁.wb_right 120122 1 by_omega
  zuesb
  have x120 : c₂.nreg 120120 = w := by_simp_all
  have x121 : c₂.nreg 120121 = c.nreg 120121 := by_simp_all
  -- the class-1 part
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, s₃⟩ : ∃ c₃ k₃, Exec P W
      ztjcw c₂ c₃ k₃ ∧ k₃ ≤ 23 ∧
      c₃.nreg 120122 = 1 ∧ SymPtIn c₃ 120123 ztyxg := by
    have vtxcase : ¬ (6 ≤ w ∧ w < 2 * V.m + 6) → ∀ (d : Config), WordsBounded W d →
        d.nreg 120122 = 1 → d.nreg 120022 = V.tv → ∃ d' k, Exec P W xpVtx d d' k ∧ k = 2 ∧
          d'.nreg 120122 = 1 ∧ SymPtIn d' 120123 ztyxg := by
      intro hn d hd h22 htv
      obtain ⟨d', k, ex, hk, a1, a2, a3⟩ := xpVtx_exec (P := P) d hd by_omega
      refine ⟨d', k, ex, hk, by_simp_all, ?_⟩
      unfold xpSym; rw [ite_eq_right hn]
      exact ⟨a1, by_simp_all⟩
    zufqv
    · zqbkw
      exact ⟨d', _, .ifLtN_true ztfbq ex, by_omega, a, b⟩
    zugjh
    · obtain ⟨d', k, ex, hk, a1, a2, a3, a4⟩ := xpEdge_exec hW hv c₂ e₂.wb_right hq₂
        by_omega by_omega
      refine ⟨d', _, .ifLtN_false ztfbq
        (.ifLtN_true ztkur ex), by_omega,
        by simp_all, ?_⟩
      unfold xpSym; zunab
      rw [x120] at a2
      exact ⟨a1, a2, by_simp_all⟩
    · zqbkw
      exact ⟨d', _, .ifLtN_false ztfbq
        (.ifLtN_false ztkur ex), by_omega, a, b⟩
  obtain ⟨k₄, ex₄, hk₄⟩ := ifEq_ne_exec (a := 120120) (b := 120126)
    (S := .instr ztsoq)
    (show c₁.nreg 120120 ≠ c₁.nreg 120126 by rw [r₁ _ by_decide, hwdef, v₁]; exact h3)
    ztcr
  obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (a := 120120) (b := 120011)
    (S := .instr ztsop) ztktw (.seq e₁ ex₄)
  exact ⟨c₃, k', ex', by_omega, v₃, by_simp_all⟩

/-! ## Comparisons of an endpoint -/

/-- Decide by the class: `v0` for class `0`, `S1` for class `1`, `v2` for class `2` (bit in
`120128`). -/
def clsDec (v0 v2 : ℕ) (S1 : Stmt) : Stmt :=
  .ifLtN 120122 120011 (.instr (.constN 120128 v0))
    (.ifLtN 120122 120048 S1 (.instr (.constN 120128 v2)))

/-- The endpoint is ahead of the origin (rightwards): `z.1 < x`. -/
def gtZ1 : Stmt :=
  .ifLtN 120025 120048
    (.seq (sgnS 0 ztfez ztdyb ztdbs) ztfeu)
    (.instr (.copyN 120128 120024))

/-- The endpoint is ahead of the origin (leftwards): `x < z.1`. -/
def ltZ1 : Stmt :=
  .ifLtN 120025 120048
    (.seq (sgnS 0 ztdyb ztfez ztdbs) ztfeu)
    (.instr (.subN 120128 120011 120024))

/-- The endpoint comes before the hit `120051` (rightwards): `x < x_D`. -/
def ltD1 : Stmt :=
  .seq (sgnS 0 ztdyb ztdru ztdbs) ztfeu

/-- The endpoint comes before the hit `120051` (leftwards): `x_D < x`. -/
def gtD1 : Stmt :=
  .seq (sgnS 0 ztdru ztdyb ztdbs) ztfeu

/-- **`z.1 < x`** for the endpoint `(w, h + 1)`. -/
def gtZS : Stmt := .seq xpS (clsDec 0 1 gtZ1)
/-- **`x < z.1`** for the endpoint `(w, h + 1)`. -/
def ltZS : Stmt := .seq xpS (clsDec 1 0 ltZ1)
/-- **`x < x_D`** for the endpoint `(w, h + 1)`. -/
def ltDS : Stmt := .seq xpS (clsDec 1 0 ltD1)
/-- **`x_D < x`** for the endpoint `(w, h + 1)`. -/
def gtDS : Stmt := .seq xpS (clsDec 0 1 gtD1)

/-- The registers written by the comparisons. -/
def BX2 (r : ℕ) : Bool := Bk r || decide (120122 ≤ r ∧ r ≤ 120128)
theorem wr_gtZS : wr BX2 gtZS = true := by_decide
theorem wr_ltZS : wr BX2 ltZS = true := by_decide
theorem wr_ltDS : wr BX2 ltDS = true := by_decide
theorem wr_gtDS : wr BX2 gtDS = true := by_decide
section Sem
variable (P : Polygon) (C : Chain) (V : QV)

/-- The abscissa of the class-`1` endpoint `(w, h + 1)`. -/
noncomputable def xpX (w h : ℕ) : ℝ := ((xpSym C V P.n w h).eval zta).1

/-- **`z.1 < x`** in the sense of the program (the box sides are `∓∞`; a box origin is on the
side the ray comes from). -/
def EndGtZ (w h : ℕ) : Prop :=
  xpClass w = 2 ∨ (xpClass w = 1 ∧
    match V.zo with
    | none => V.σb = 1
    | some z => z.1 < xpX P C V w h)

/-- **`x < z.1`** in the sense of the program. -/
def EndLtZ (w h : ℕ) : Prop :=
  xpClass w = 0 ∨ (xpClass w = 1 ∧
    match V.zo with
    | none => V.σb ≠ 1
    | some z => xpX P C V w h < z.1)

/-- **`x < x_D`** in the sense of the program (`x_D` the point of edge `eD`). -/
def EndLtD (eD w h : ℕ) : Prop :=
  xpClass w = 0 ∨ (xpClass w = 1 ∧ xpX P C V w h < xe zta eD V.hz)

/-- **`x_D < x`** in the sense of the program. -/
def EndGtD (eD w h : ℕ) : Prop :=
  xpClass w = 2 ∨ (xpClass w = 1 ∧ xe zta eD V.hz < xpX P C V w h)
end Sem

/-! ### Execution of the comparisons -/
theorem xpClass_le (w : ℕ) : xpClass w ≤ 2 := by unfold xpClass; grind

/-- **Deciding by the class.** -/
theorem clsDec_exec {P : Polygon} {W : ℕ} (hW : 3 ≤ W) {v0 v2 : ℕ} (hv0 : v0 ≤ 1) (hv2 : v2 ≤ 1)
    {S1 : Stmt} {K1 : ℕ} {R1 : Prop} (c : Config) (hw : WordsBounded W c) (hone : c.nreg 120011 = 1)
    (htwo : c.nreg 120048 = 2) (hcl : c.nreg 120122 ≤ 2)
    (hS1 : c.nreg 120122 = 1 → ∃ c' k, Exec P W S1 c c' k ∧ k ≤ K1 ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ R1)) :
    ∃ c' k, Exec P W (clsDec v0 v2 S1) c c' k ∧ k ≤ K1 + 5 ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ (c.nreg 120122 = 0 ∧ v0 = 1) ∨ (c.nreg 120122 = 1 ∧ R1) ∨
        (c.nreg 120122 = 2 ∧ v2 = 1)) := by
  unfold clsDec
  by_cases h0 : c.nreg 120122 < 1
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 120128 v0 by_omega
    refine ⟨c₁, _, .ifLtN_true by_omega e₁, by_omega, by_omega, ?_⟩
    omega
  by_cases h1 : c.nreg 120122 < 2
  · obtain ⟨c₁, k₁, e₁, hk₁, b₁, v₁⟩ := hS1 by_omega
    refine ⟨c₁, _, .ifLtN_false by_omega ztjdl,
      by omega, b₁, ?_⟩
    grind
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 120128 v2 by_omega
    refine ⟨c₁, _, .ifLtN_false by_omega ztnac,
      by omega, by_omega, ?_⟩
    omega

/-- The class-`1` point and the constants after `xpS`. -/
theorem after_xp {P : Polygon} {W : ℕ} (hW : 4 * P.n + 8 ≤ W) {C : Chain} {V : QV}
    (hv : QVOK P C V) (c : Config) (hw : WordsBounded W c) (hq : QConst P V c) :
    ∃ c₁ k₁, Exec P W xpS c c₁ k₁ ∧ k₁ ≤ 40 ∧ FrameB BX c c₁ ∧ QConst P V c₁ ∧
      c₁.nreg 120122 = xpClass ztcpo ∧
      (xpClass ztcpo = 1 →
        SymPtIn c₁ 120123 ztyxh) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁, s₁⟩ := xpS_exec (P := P) hW hv c hw hq
  exact ⟨c₁, k₁, e₁, hk₁, f₁, hq.frame f₁ fun r h1 h2 => by
    zunqb; omega, v₁, s₁⟩

/-- **`z.1 < x`.** -/
theorem gtZS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hh : c.nreg 120121 < P.n) :
    ∃ c' k, Exec P W gtZS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndGtZ P C V ztcpo ztdcp) := by
  zqbks
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 0) (v2 := 1) (S1 := gtZ1)
    (K1 := 250) (R1 := match V.zo with
      | none => V.σb = 1
      | some z => z.1 < xpX P C V ztcpo ztdcp) by_omega by_norm_num
    by_norm_num c₁ e₁.wb_right hq₁.one hq₁.two ztdme (by
      zqbkt
      zqbkx
      · obtain ⟨c₂, e₂, v₂, -⟩ := copy_exec e₁.wb_right 120128 120024
        zqbkv
        · rw [v₂, hq₁.σb]; exact hv.σb_le
        · rw [v₂, hq₁.σb, hzo]
      · obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec hG by_omega 0 by_norm_num
          ztfez ztdyb ztdbs c₁ e₁.wb_right by_decide by_decide
          by_decide hpin hpt rfl hp hl ztntz
        zueap
        refine ⟨c₃, _, .ifLtN_true ztnua ztcr, by_omega,
          by omega, ?_⟩
        zuind
        rfl)
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, exec_frameB ztyv wr_gtZS, b₂, ?_⟩
  zqbkz
  unfold EndGtZ
  grind

/-- **`x < z.1`.** -/
theorem ltZS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hh : c.nreg 120121 < P.n) :
    ∃ c' k, Exec P W ltZS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndLtZ P C V ztcpo ztdcp) := by
  zqbks
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 1) (v2 := 0) (S1 := ltZ1)
    (K1 := 250) (R1 := match V.zo with
      | none => V.σb ≠ 1
      | some z => xpX P C V ztcpo ztdcp < z.1) by_omega by_norm_num
    by_norm_num c₁ e₁.wb_right hq₁.one hq₁.two ztdme (by
      zqbkt
      zqbkx
      · zud
        obtain ⟨c₂, e₂, v₂, -⟩ : ∃ c₂, Exec P W (.instr (.subN 120128 120011 120024)) c₁ c₂ 1 ∧
            c₂.nreg 120128 = c₁.nreg 120011 - c₁.nreg 120024 ∧ True :=
          ⟨_, Exec.subN w₁ _ _ _, by config_simp, trivial⟩
        have hσ := hv.σb_le
        zqbkv
        · rw [v₂, hq₁.one]; omega
        · rw [v₂, hq₁.one, hq₁.σb, hzo]; omega
      · obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec hG by_omega 0 by_norm_num
          ztdyb ztfez ztdbs c₁ e₁.wb_right by_decide by_decide
          by_decide hpt hpin rfl hl hp ztntz
        zueap
        refine ⟨c₃, _, .ifLtN_true ztnua ztcr, by_omega,
          by omega, ?_⟩
        zuind
        rfl)
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, exec_frameB ztyv wr_ltZS, b₂, ?_⟩
  zqbkz
  unfold EndLtZ
  simp

/-- **`x < x_D`.** -/
theorem ltDS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hh : c.nreg 120121 < P.n) (heD : c.nreg 120051 < P.n) :
    ∃ c' k, Exec P W ltDS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndLtD P C V ztfgp ztcpo ztdcp) := by
  zqbks
  have x51 : ztsfy := f₁.1 _ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 1) (v2 := 0) (S1 := ltD1)
    (K1 := 250) (R1 := xpX P C V ztcpo ztdcp <
      xe zta ztfgp V.hz) by_omega by_norm_num
    by_norm_num c₁ e₁.wb_right hq₁.one hq₁.two ztdme (by
      zqbkt
      obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG by_omega 0 by_norm_num
        ztdyb ztdru ztdbs c₁ e₁.wb_right by_decide by_decide
        by_decide hpt rfl rfl hl (show (SymPt.onEdge _ _).Lt P.n from
          ⟨by_omega, by zupaf; exact hv.hz_lt⟩) (by zupag; tauto)
      zqbku
      zunia)
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, exec_frameB ztyv wr_ltDS, b₂, ?_⟩
  zqbkz
  unfold EndLtD
  simp

/-- **`x_D < x`.** -/
theorem gtDS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hh : c.nreg 120121 < P.n) (heD : c.nreg 120051 < P.n) :
    ∃ c' k, Exec P W gtDS c c' k ∧ k ≤ 300 ∧ FrameB BX2 c c' ∧ c'.nreg 120128 ≤ 1 ∧
      (c'.nreg 120128 = 1 ↔ EndGtD P C V ztfgp ztcpo ztdcp) := by
  zqbks
  have x51 : ztsfy := f₁.1 _ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, v₂⟩ := clsDec_exec (P := P) (v0 := 0) (v2 := 1) (S1 := gtD1)
    (K1 := 250) (R1 := xe zta ztfgp V.hz <
      xpX P C V ztcpo ztdcp) by_omega by_norm_num
    by_norm_num c₁ e₁.wb_right hq₁.one hq₁.two ztdme (by
      zqbkt
      obtain ⟨c₂, k₂, e₂, hk₂, -, b₂, g₂⟩ := sgnS_exec (P := P) hG by_omega 0 by_norm_num
        ztdru ztdyb ztdbs c₁ e₁.wb_right by_decide by_decide
        by_decide rfl hpt rfl (show (SymPt.onEdge _ _).Lt P.n from
          ⟨by_omega, by zupaf; exact hv.hz_lt⟩) hl (by zupag; tauto)
      zqbku
      zunia)
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, exec_frameB ztyv wr_gtDS, b₂, ?_⟩
  zqbkz
  unfold EndGtD
  grind
end
end OracleR
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbin" : tactic => `(tactic| (obtain ⟨-, -, hEb, -⟩ := (hwf.2 h0').2 H₀ C₀ hC₀
                                           have hH : HostAt m' _ H₀ := Gran.hostAt_agree' hC₀.1 hEb he
                                           have e1 : ztyls := he _ by_omega))
local macro "zqbio" : tactic => `(tactic| (intro h0 H C hC
                                           have hD := hwf.1
                                           zujyb
                                           rcases hMD with ⟨-, H₀, C₀, hC₀, -⟩ | ⟨h1, -, -⟩))
set_option hygiene true

/-!
# WP-E, part 8: the restoration driver — the region loop

`regS sF` visits the regions `r = 0 … R - 1` of the current normal form; for every region with
more than `D` exit chords (the length of its chord list, `Gran.deg_region`) it calls the splitting
step `sF` (`FindOK`) and appends the returned chord triple to the list at `LB`.  By completeness
of `sF` (the full augmented maps have degree `≤ D`) every such region receives a chord.

`reg_exec`: after the loop the list at `LB` is `oldL N ++ newL.map Prod.snd`, where `newL` pairs
the high regions (in increasing order) with their chords, each sound (`FoundOK`).
-/
namespace Chazelle.Core
namespace Restore
open Machine Machine.Stmt Programs
open Chazelle.Chain (regionsIn)
@[expose] public section
def oldL (N : NF) : List zte := N.chords.map fun x => ztqyz

/-- The degree of region `r` as stored. -/
def degOf (N : NF) (r : ℕ) : ℕ := (N.region r).chords.length

/-- The regions below `r` with more than `D` exit chords. -/
def highList (N : NF) (D r : ℕ) : List ℕ := (List.range r).filter fun r' => D < degOf N r'
variable (N : NF) (D r : ℕ)
theorem highList_succ :
    highList N D ztgu = highList N D r ++ (if D < degOf N r then [r] else []) := by
  unfold highList
  zubic
theorem highList_length_le : (highList N D r).length ≤ r := by
  unfold highList
  grind

/-- A chord triple found for region `r`: attached, at a vertex height, admissible, splitting the
region well. -/
def FoundOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) (r : ℕ)
    (t : ℕ × ℕ × ℕ) : Prop :=
  (recOf t).Attached M Q ∧ t.1 < Q.n ∧ (recOf t).toSet M Q ∈ M.Adm ∧
    SplitsWell M ztdu ztcz ((recOf t).toSet M Q)

/-- The memory context has a local capacity. -/
abbrev CapLocal (X : MemCtx) : Prop := X.CapLocal

/-- The cost of one call of the splitting step. -/
def costF (κf F G Hc : ℕ → ℕ) (dcap γ : ℕ) : ℕ :=
  κf dcap * F γ * G γ * (Hc γ + Nat.clog 2 γ + 1)

/-- The fixed data of the region loop. -/
structure RegEnv where
  P : Polygon
  W : ℕ
  M : Model
  N : NF
  reg : ℕ → Set Point
  A₀ : ℕ
  m₀ : ℕ → ℕ
  LB : ℕ
  H : ℕ
  MD : ℕ
  D : ℕ
  γ : ℕ
  ctx : ℕ
  dcap : ℕ
  sF : Stmt
  κf : ℕ → ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  Ok : Polygon → Model → Prop
namespace RegEnv
variable (E : RegEnv)

/-- The number of chords. -/
def K : ℕ := E.N.nChords

/-- The number of regions. -/
def R : ℕ := E.N.nRegions

/-- The chord family. -/
def S : Set ztf := E.N.F E.M zti

/-- The body bound of the region loop. -/
def Bf : ℕ := costF E.κf E.F E.G E.Hc E.dcap E.γ + 20
end RegEnv
variable {P : Polygon} {m m' : ℕ → ℕ} {W : ℕ} (c : Config)
/-- **Host regularity of a descriptor** survives a change of the memory at or above the bound of
a well-formed descriptor (G10/G11). -/
theorem hregKeep {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D zta M)
    (h : m D = 0 → ∀ H C, ChainDescAt m ztef zta H C → HostRegular (Qof P).n H)
    (he : ∀ a, a < E → m' a = m a) :
    m' D = 0 → ∀ H C, ChainDescAt m' ztef zta H C → HostRegular (Qof P).n H := by
  zqbio
  · zqbin
    have  := NFLoc.hostAt_unique ztfpy hH
    grind
  omega

/-- A chain descriptor's polygon stays simple when the memory changes above its bound. -/
theorem simpKeep {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D zta M)
    (h : m D = 0 → ∀ H C, ChainDescAt m ztef zta H C → C.P.Simple)
    (he : ∀ a, a < E → m' a = m a) :
    m' D = 0 → ∀ H C, ChainDescAt m' ztef zta H C → C.P.Simple := by
  zqbio
  · zqbin
    have hHH := NFLoc.hostAt_unique ztfpy hH
    have hPP : C.P = C₀.P := by rw [hC.2.1, hC₀.2.1, hHH]
    grind
  omega

/-- The facts about the region-loop data and the configuration `c₀` at the start of the loop. -/
structure RegGood (E : RegEnv) (c₀ : Config) : Prop where
  hF : FindOK E.sF E.κf E.F E.G E.Hc E.X E.Ok oracleBands
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, ztcqf → E.γ ≤ E.X.cap E.P m E.ctx
  hA₀ : E.A₀ ≤ E.LB
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD zti E.M
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C → C.P.Simple
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hfull : E.M.FullDegLe zti E.D
  hNW : NFWithin c₀.nmem E.H E.LB E.N
  hNF : IsNF E.M zti E.N
  hregs : NFRegs E.M zti E.N E.reg
  hdeg : E.M.DegLe E.S E.dcap
  hsg : E.M.Semigranular E.S E.γ
  hlow : ∀ a, a < E.A₀ → c₀.nmem a = E.m₀ a
  wb : WordsBounded E.W c₀
  r00 : c₀.nreg 80000 = E.MD
  r03 : c₀.nreg 80003 = E.D
  r04 : c₀.nreg 80004 = E.γ
  r06 : c₀.nreg 80006 = E.ctx
  r12 : c₀.nreg 80012 = E.H
  r14 : c₀.nreg 80014 = E.R
  r19 : c₀.nreg 80019 = E.dcap
  r20 : c₀.nreg 80020 = 1
  r23 : c₀.nreg 80023 = 5
  r24 : c₀.nreg 80024 = 0
  r40 : c₀.nreg 80040 = 0
  r41 : c₀.nreg 80041 = c₀.nmem ztbaq + 2
  r18 : c₀.nreg 80018 = E.K
  r43 : c₀.nreg 80043 = E.LB + 3 * E.K
  alloc : E.LB + 3 * (E.K + E.R) ≤ c₀.nreg ALLOC
  list : ChordListAt c₀.nmem E.LB (oldL E.N)
  room : c₀.nreg ALLOC + ztnd * E.R + 2 ≤ E.W

/-- The region-loop invariant. -/
structure RegI (E : RegEnv) (c₀ : Config) (newL : List ztwjg) (c : Config) :
    Prop where
  wb : WordsBounded E.W c
  r_le : c.nreg 80040 ≤ E.R
  ptr : c.nreg 80041 = c₀.nmem ztbaq + 2 + 5 * c.nreg 80040
  hfst : newL.map Prod.fst = highList E.N E.D ztmgg
  hgood : ∀ p ∈ newL, FoundOK E.M zti E.N E.reg p.1 p.2
  cnt : c.nreg 80018 = E.K + newL.length
  dst : c.nreg 80043 = E.LB + 3 * ztjie
  list : ChordListAt c.nmem E.LB (oldL E.N ++ newL.map Prod.snd)
  low : ∀ a, a < E.LB → c.nmem a = c₀.nmem a
  regs : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
    q ≠ 80043 → c.nreg q = c₀.nreg q
  alloc : c₀.nreg ALLOC ≤ c.nreg ALLOC
  room : c.nreg ALLOC + ztnd * (E.R - c.nreg 80040) ≤ c₀.nreg ALLOC + ztnd * E.R

/-! ## Straight-line pieces -/
theorem load42_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W ztozd c c' k ∧ k = 1 ∧
      c'.nreg 80042 = c.nmem ztvis ∧ (∀ r, r ≠ 80042 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  simp_all
theorem argS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      c'.nreg 81000 = c.nreg 80000 ∧ c'.nreg 81001 = c.nreg 80012 ∧
      c'.nreg 81002 = c.nreg 80040 ∧ c'.nreg 81003 = c.nreg 80004 ∧
      c'.nreg 81004 = c.nreg 80006 ∧ c'.nreg 81005 = c.nreg 80019 ∧
      c'.nreg 81006 = c.nreg 80003 ∧
      (∀ r, (r < 81000 ∨ 81007 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold argS
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    zusb
theorem appS_exec (hw : WordsBounded W c) {d : ℕ}
    (h43 : c.nreg 80043 = d) (h20 : c.nreg 80020 = 1) (hd : d + 3 ≤ W)
    (hn : c.nreg 80018 + 1 ≤ W) :
    ∃ c' k, Exec P W appS c c' k ∧ k = 7 ∧ c'.nreg 80043 = d + 3 ∧
      c'.nreg 80018 = c.nreg 80018 + 1 ∧
      c'.nmem = upd ztyfv ztvq
        ztqid ∧
      (∀ r, r ≠ 80043 → r ≠ 80018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold appS
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h43, h20]; omega)
  simp_all
theorem tail_exec (hw : WordsBounded W c)
    (h1 : c.nreg 80041 + c.nreg 80023 ≤ W) (h2 : c.nreg 80040 + c.nreg 80020 ≤ W) :
    ∃ c' k, Exec P W ztiqs c c' k ∧
      k = 2 ∧ c'.nreg 80041 = c.nreg 80041 + c.nreg 80023 ∧
      c'.nreg 80040 = c.nreg 80040 + c.nreg 80020 ∧
      (∀ r, r ≠ 80041 → r ≠ 80040 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · zubvv
  · simp_all
  simp_all

/-! ## The call of the splitting step -/

/-- The memory of the loop agrees with the initial memory below `A₀`. -/
theorem RegI.agree {E : RegEnv} {c₀ c : Config} {newL : List ztwjg}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a :=
  fun a ha => (hI.low a (lt_of_lt_of_le ha hE.hA₀)).trans ztoad
theorem RegI.nfWithin {E : RegEnv} {c₀ c : Config} {newL : List ztwjg}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) {A : ℕ} (hA : E.LB ≤ A) :
    NFWithin c.nmem E.H A E.N :=
  (hE.hNW.transport hI.low).mono hA
theorem RegGood.lb_le {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀) :
    E.LB ≤ c₀.nreg ALLOC := by have := hE.alloc; omega

/-- The degree word of region `r`. -/
theorem RegI.deg_word {E : RegEnv} {c₀ c : Config} {newL : List ztwjg}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) (hr : c.nreg 80040 < E.R) :
    c.nmem ztvis = degOf E.N ztmgg := by
  zujzt
  have hareas := Gran.nf_areas hNWc
  have h5 : ztzpg := hI.low _ by_omega
  have hreg := (hNWc.nfAt.2.2.2.2.2.2.2.1 _ hr).2.1
  rw [hI.ptr, ← h5]
  unfold degOf
  grind
set_option maxHeartbeats 4000000 in
/-- **One call of the splitting step** on a region with more than `D` exit chords: a sound chord
is appended to the list. -/
theorem call_step {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀)
    {newL : List ztwjg} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 80040 < E.R) (hhigh : E.D < degOf E.N ztmgg) :
    ∃ c' k t, Exec E.P E.W ztjss c c' k ∧ k ≤ costF E.κf E.F E.G E.Hc E.dcap E.γ + 16 ∧
      RF dBands E.A₀ c c' k ∧ WordsBounded E.W c' ∧
      FoundOK E.M zti E.N E.reg ztmgg t ∧
      c'.nreg 80018 = c.nreg 80018 + 1 ∧ c'.nreg 80043 = c.nreg 80043 + 3 ∧
      ChordListAt c'.nmem E.LB (oldL E.N ++ newL.map Prod.snd ++ [t]) ∧
      (∀ a, a < E.LB → c'.nmem a = c.nmem a) ∧
      (∀ q, 80000 ≤ q → q < 81000 → q ≠ 80018 → q ≠ 80043 → c'.nreg q = c.nreg q) := by
  obtain ⟨hF, hG, hWh, hX, hcap, hA₀, hwf, hMD, hreg, hsimp, hGM, hOk, hfull, hNW, hNF, hregs, hdeg, hsg,
    hlow, wb₀, r00, r03, r04, r06, r12, r14, r19, r20, r23, r24, r40, r41, r18, r43, halloc,
    hlist₀, hroom₀⟩ := hE
  have hE' : RegGood E c₀ := ⟨hF, hG, hWh, hX, hcap, hA₀, hwf, hMD, hreg, hsimp, hGM, hOk, hfull, hNW, hNF,
    hregs, hdeg, hsg, hlow, wb₀, r00, r03, r04, r06, r12, r14, r19, r20, r23, r24, r40, r41, r18,
    r43, halloc, hlist₀, hroom₀⟩
  set r := c.nreg 80040 with hrdef
  zumfr
  have c00 : c.nreg 80000 = E.MD := by
    grind
  have c03 : ztuof := by
    grind
  have c04 : c.nreg 80004 = E.γ := by
    grind
  have c06 : c.nreg 80006 = E.ctx := by
    grind
  have c12 : c.nreg 80012 = E.H := by
    grind
  have c19 : c.nreg 80019 = E.dcap := by
    grind
  have c20 : ztpma := by
    grind
  have c24 : c.nreg 80024 = 0 := by
    grind
  have hagree := hI.agree hE'
  have hA0c : E.A₀ ≤ c.nreg ALLOC := by have := hI.alloc; omega
  have hLBc : E.LB ≤ c.nreg ALLOC := by have := hI.alloc; omega
  -- arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    argS_exec (P := E.P) c hI.wb
  zud
  have A₁ : ztdc := R₁ _ by_decide
  have hag₁ : ztkoc := fun a ha => by_grind
  obtain ⟨hMD₁, hwf₁⟩ := Gran.desc_agree' hwf hMD hag₁
  have hNW₁ : ztylg := by
    zuoiz; exact hI.nfWithin hE' hLBc
  have hR : E.R = E.N.nRegions := rfl
  -- the precondition of the splitting step
  have pre : GoodEnv E.P ∧ hostWords E.P.n ≤ E.W ∧
      E.X.holds E.P c₁.nmem ztvms ztbmq ∧
      c₁.nreg 81003 ≤ E.X.cap E.P c₁.nmem ztvms ∧
      ModelDescWF E.P ztbmq c₁.nmem ztjtc ∧
      (c₁.nmem ztjtc = 0 → ∀ H C, ChainDescAt c₁.nmem ztrob zti H C →
        HostRegular (Qof E.P).n H) ∧
      (c₁.nmem ztjtc = 0 → ∀ H C, ChainDescAt c₁.nmem ztrob zti H C →
        C.P.Simple) ∧
      ∃ M N, ModelDescAt c₁.nmem ztjtc zti M ∧ GoodModel M ∧ E.Ok E.P M ∧
        NFWithin c₁.nmem ztvmr ztbmq N ∧ IsNF M zti N ∧
        M.DegLe ztxvn ztqkg ∧
        M.Semigranular ztxvn zterk ∧ c₁.nreg 81002 < N.nRegions := by
    rw [a0, a1, a2, a3, a4, a5, c00, c12, c04, c06, c19]
    refine ⟨hG, hWh, ?_, by_grind, hwf₁.mono by_omega,
      hregKeep hwf hMD hreg hag₁, simpKeep hwf hMD hsimp hag₁, E.M, E.N, hMD₁, hGM,
      hOk, hNW₁, hNF, hdeg, hsg, by_omega⟩
    exact E.X.mono _ _ _ _ _ by_omega
      (E.X.local_ _ _ _ _ _ by_grind hX)
  have hcostle : ztlao := rfl
  have hroomF : c₁.nreg ALLOC + E.κf ztqkg * E.F zterk *
      E.G zterk * ztyhk ≤ E.W := by
    rw [a5, a3, c19, c04, A₁]
    zumba
    have h2 : ztnd * 1 ≤ ztnd * ztnkt := Nat.mul_le_mul_left _ by_omega
    unfold costF at hcostle
    grind
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨P₂8, P₂fl, P₂⟩, F₂⟩ := hF E.P E.W c₁ w₁ pre hroomF
  zuira
  rw [a5, a3, c19, c04] at hk₂
  zue
  -- the flag is `1` and the chord is sound
  have hNAt₁ : NFAt c₁.nmem ztvmr E.N := by rw [a1, c12]; exact hNW₁.nfAt
  have hMD₁' : ModelDescAt c₁.nmem ztjtc zti E.M := by rw [a0, c00]; omega
  obtain ⟨hsnd, hcpl⟩ := P₂ E.M E.N E.reg hMD₁' hNAt₁ hNF hregs
  zufji
  have hdegr : E.M.deg _ _ = degOf E.N r :=
    Gran.deg_region hNF hRC hRO by_omega
  have hflag := hcpl (by rw [a6, c03]; omega)
    (by rw [a6, c03, a2, hdegr]; omega)
  zucya

  set t : ℕ × ℕ × ℕ := ztmic with htdef
  have hgood : FoundOK E.M _ E.N E.reg r t := ztopn
  -- append
  have d43 : c₂.nreg 80043 = E.LB + 3 * ztjie := by
    rw [P₂8 _ zthdw by_omega, R₁ _ by_omega, hI.dst]
  have d20 : zturg := by
    rw [P₂8 _ zthdw by_omega, R₁ _ by_omega, c20]
  have d18 : c₂.nreg 80018 = E.K + newL.length := by
    rw [P₂8 _ zthdw by_omega, R₁ _ by_omega, hI.cnt]
  have hlen : newL.length ≤ r := by
    have := congrArg List.length hI.hfst
    zubus
    zugxg
  zugll
  have hdA : E.LB + 3 * ztjie + 3 ≤ c₁.nreg ALLOC := by
    rw [A₁]; have := hI.alloc; omega
  have hWW : ztpnj := w₂.1 _
  obtain ⟨c₃, k₃, e₃, hk₃, t43, t18, m₃, R₃, rr₃, rm₃, o₃⟩ := appS_exec (P := E.P) c₂ w₂ d43 d20
    by_omega by_omega
  have f24 : c₂.nreg 80024 = 0 := by
    rw [P₂8 _ zthdw by_omega, R₁ _ by_omega, c24]
  have e₂₃ : Exec E.P E.W ztprt c₂ c₃ _ :=
    .ifLtN_true by_omega e₃
  -- memory facts
  have hm₂low := F₂.2.2.1
  have hmem : ∀ a, a < E.LB + 3 * ztjie → c₃.nmem a = c.nmem a := by
    zuge
    rw [m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, hm₂low a by_omega, m₁]
  refine ⟨c₃, k₁ + ztdhs, t, .seq e₁ (.seq e₂ e₂₃), ?_, ?_, e₃.wb_right, hgood,
    ?_, ?_, ?_, fun a ha => hmem a by_omega, fun q q1 q2 q3 q4 => ?_⟩
  · unfold costF; omega
  · -- the frame
    have RF₁ : ztlag := rf_of_regs (fun q hq => R₁ q (by
      omega)) rr₁ m₁ rm₁ o₁
    have RF₂ : RF dBands E.A₀ c₁ c₂ k₂ := RF.of_frame F₂ by_omega
    have RF₃ : RF dBands E.A₀ c₂ c₃ (k₃ + 1) := by
      have hA₃ : ztbox := R₃ _ by_decide by_decide
      have b43 : bandOf 80043 ∈ dBands := by_decide
      have b18 : bandOf 80018 ∈ dBands := by_decide
      refine ⟨fun q hq _ => R₃ q (fun h => hq (h ▸ b43)) (fun h => hq (h ▸ b18)),
        fun q _ => by zuoek, fun a ha => ?_, fun a _ => by rw [rm₃], o₃, by_omega, by_omega⟩
      · zulgl
        rw [m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
          Machine.upd_other _ _ _ by_omega]
    exact (RF₁.trans zthrz)
  · rw [t18, d18, hI.cnt]
  · rw [t43, hI.dst]
  · -- the list
    have hl := hI.list
    have hlen' : (oldL E.N ++ newL.map Prod.snd).length = E.K + newL.length := by
      simp [oldL, RegEnv.K, NF.nChords]
    refine Gran.ChordListAt.snoc hl ztpbd ?_ ?_ ?_
    · rw [hlen'] at a2; exact hmem a a2
    · rw [hlen', m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_same]
    · rw [hlen', m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_same]
    · rw [hlen', m₃, Machine.upd_same]
  · rw [R₃ q q4 q3, P₂8 q (band8 q1 by_omega) q2, R₁ q by_omega]

/-! ## One region, and the loop -/
set_option maxHeartbeats 8000000 in
/-- **One step of the region loop.** -/
theorem regBody_step {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀)
    {newL : List ztwjg} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 80040 < E.R) :
    ∃ c' k newL', Exec E.P E.W ztwcm c c' k ∧ RegI E c₀ newL' c' ∧
      RF dBands E.A₀ c c' k ∧ k ≤ E.Bf ∧ c'.nreg 80040 = c.nreg 80040 + 1 := by
  zumfr
  have c03 : ztuof := by
    rw [reg8 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      hE.r03]
  have c20 : ztpma := by
    rw [reg8 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      hE.r20]
  have c23 : c.nreg 80023 = 5 := by
    rw [reg8 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      hE.r23]
  zukbu
  obtain ⟨r, hrdef⟩ : ∃ r, c.nreg 80040 = r := by_simp_all
  rw [hrdef] at hr hdw
  obtain ⟨c₁, k₁, e₁, hk₁, l42, R₁, rr₁, m₁, rm₁, o₁⟩ := load42_exec (P := E.P) c hI.wb
  rw [hdw] at l42
  zud
  have hroom₁ : c₁.nreg ALLOC + ztnd * (E.R - c₁.nreg 80040) ≤
      c₀.nreg ALLOC + ztnd * E.R := by
    zunti; exact hI.room
  have hI₁ : ztscj := ⟨w₁, by_grind,
    by zunti; exact hI.ptr,
    by zungs; exact hI.hfst, hI.hgood, by zungs; exact hI.cnt,
    by zungs; exact hI.dst, by zvmxn; exact hI.list,
    fun a ha => by zvmxn; exact hI.low a ha,
    by grind,
    by zungs; exact hI.alloc, hroom₁⟩
  have RF₁ : ztlag := rf_of_regs by_grind rr₁ m₁ rm₁ o₁
  have r1 : c₁.nreg 80040 = r := by_grind
  -- the conditional call
  obtain ⟨c₂, k₂, newL', e₂, hk₂, RF₂, w₂, hfst₂, hgood₂, cnt₂, dst₂, list₂, low₂, reg₂⟩ :
      ∃ (c₂ : Config) (k₂ : ℕ) (newL' : List ztwjg),
      Exec E.P E.W (.ifLtN 80003 80042 ztjss .skip) c₁ c₂ k₂ ∧
      k₂ ≤ costF E.κf E.F E.G E.Hc E.dcap E.γ + 17 ∧ RF dBands E.A₀ c₁ c₂ k₂ ∧
      WordsBounded E.W c₂ ∧ newL'.map Prod.fst = highList E.N E.D ztgu ∧
      (∀ p ∈ newL', FoundOK E.M zti E.N E.reg p.1 p.2) ∧
      c₂.nreg 80018 = E.K + newL'.length ∧ c₂.nreg 80043 = E.LB + 3 * (E.K + newL'.length) ∧
      ChordListAt c₂.nmem E.LB (oldL E.N ++ newL'.map Prod.snd) ∧
      (∀ a, a < E.LB → c₂.nmem a = c₁.nmem a) ∧
      (∀ q, 80000 ≤ q → q < 81000 → q ≠ 80018 → q ≠ 80043 → c₂.nreg q = c₁.nreg q) := by
    by_cases hhigh : E.D < degOf E.N r
    · obtain ⟨c₂, k₂, t, e₂, hk₂, RF₂, w₂, hgood, t18, t43, tlist, tlow, treg⟩ :=
        call_step hE hI₁ by_omega by_grind
      zvnal at hgood
      refine ⟨c₂, k₂ + 1, newL ++ [zteve],
        .ifLtN_true by_grind e₂, by_omega,
        RF₂.mono subset_rfl by_omega, w₂, ?_, ?_, ?_, ?_, ?_, tlow, treg⟩
      · rw [List.map_append, hI.hfst, hrdef, highList_succ, ite_eq_left hhigh]; rfl
      · zuda
        zutk
        · zulyn
        grind
      · rw [t18, hI₁.cnt, List.length_append, List.length_singleton]; ring
      · rw [t43, hI₁.dst, List.length_append, List.length_singleton]; ring
      grind
    · refine ⟨c₁, 2, newL, .ifLtN_false by_grind
        ztwd, by_omega, RF.refl _ _, w₁, ?_, hI.hgood, hI₁.cnt, hI₁.dst, hI₁.list,
        by omega, by_omega⟩
      rw [hI.hfst, hrdef, highList_succ, ite_eq_right hhigh, List.append_nil]
  -- the tail
  have k40 : c₂.nreg 80040 = r := by_grind
  have k41 : c₂.nreg 80041 = c₀.nmem ztbaq + 2 + 5 * r := by
    rw [reg₂ _ by_omega by_omega by_omega by_omega, hI₁.ptr, r1]
  have k20 : zturg := by
    grind
  have k23 : c₂.nreg 80023 = 5 := by
    grind
  -- the pointer stays below the allocator
  zujzt
  have hareas := (Gran.nf_areas hNWc).2.2.1 r hr
  have h5 : ztzpg := hI.low _ (by
    have := (Gran.nf_areas hNWc).1; omega)
  rw [h5] at hareas
  have hLBW := le_trans (hE.lb_le) (hE.wb.1 ALLOC)
  have hRW : ztsbg := by
    have := hE.room
    grind
  have hLB3 : E.LB + 3 ≤ E.W := by
    have := hE.alloc; have := hE.wb.1 ALLOC; omega
  obtain ⟨c₃, k₃, e₃, hk₃, t41, t40, R₃, rr₃, m₃, rm₃, o₃⟩ := tail_exec (P := E.P) c₂ w₂
    by_omega by_omega
  rw [k41, k23] at t41
  rw [k40, k20] at t40
  have RF₃ : ztrft := rf_of_regs by_grind
    rr₃ m₃ rm₃ o₃
  have RFall : RF dBands E.A₀ c c₃ _ := RF₁.trans zthrz
  have hBf : ztlao := rfl
  refine ⟨c₃, k₁ + zttl, newL', .seq e₁ ztcr, ⟨e₃.wb_right, by_omega,
    by omega, by_grind, hgood₂,
    by grind,
    by grind, by_grind,
    fun a ha => by rw [m₃, low₂ a ha, m₁]; exact hI.low a ha,
    fun q q1 q2 q3 q4 q5 q6 q7 => ?_, ?_, ?_⟩, RFall, by_omega, by_omega⟩
  · grind
  · exact le_trans hI.alloc RFall.2.2.2.2.2.1
  · zudxy

    rw [t40]
    rw [hrdef] at h1
    have h3 : ztxto := by
      zudkm
    omega

/-- **The region loop.** -/
theorem reg_exec {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀) :
    ∃ c' k newL, Exec E.P E.W ztqvo c₀ c' k ∧ RegI E c₀ newL c' ∧
      c'.nreg 80040 = E.R ∧ RF dBands E.A₀ c₀ c' k ∧ k ≤ ztnd * E.R + 2 := by
  have I0 : RegI E c₀ [] c₀ := ⟨hE.wb, by rw [hE.r40]; omega, by rw [hE.r40, hE.r41],
    by rw [hE.r40]; rfl, by_simp_all, by rw [hE.r18]; simp,
    by rw [hE.r43]; simp, by simpa using hE.list, by_omega,
    by omega, le_rfl, by_simp⟩
  obtain ⟨c', k, e, ⟨newL, I'⟩, hx, RFl, hk⟩ := whileLtN_frame (P := E.P) (W := E.W)
    (a := 80040) (b := 80014) (body := regBody E.sF) (B := dBands) (A₀ := E.A₀)
    ztjvo (fun c => E.R - c.nreg 80040) E.Bf
    ztdnu
    (fun c ⟨newL, I⟩ ht => by
      have t : c.nreg 80040 < E.R := by
        rw [I.regs 80014 by_omega by_omega by_omega by_omega by_omega by_omega
          by_omega, hE.r14] at ht
        exact ht
      obtain ⟨c', k, newL', e, I', RF', hk, h40⟩ := regBody_step hE I t
      grind) ⟨[], I0⟩
  have hR' : c'.nreg 80040 = E.R := by
    rw [I'.regs 80014 by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, hE.r14] at hx
    have := I'.r_le; omega
  refine zthmp
  rw [hE.r40] at hk
  omega
