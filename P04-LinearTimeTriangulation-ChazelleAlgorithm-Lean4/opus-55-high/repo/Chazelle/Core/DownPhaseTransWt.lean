module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.GranInitL5
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.NFDecompRamRound
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.FuseMathCut

namespace Chazelle.Core
namespace Trans
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft IsHChordIn)
open Chazelle.Geometry (lerp)
open Chazelle.Visibility (hseg)
open ArcT (wrapK NonVtx)
variable {Q : Polygon} {C : Chain}

/-- **The inner-side shift.** -/
structure Shift (Q : Polygon) (C : Chain) (c₀ : ℕ) : Prop where
  six : 6 ≤ c₀
  le : c₀ + C.m ≤ 2 * C.m + 6
  vtx : ∀ j, j ≤ C.m → (C.sideWalk C.sideBeta).vtx zthie = (interiorWalk Q).vtx j
variable {c₀ : ℕ}
theorem chain_n : (chainModel C).W.n = 2 * C.m + 7 := Chain.sideWalk_n _ _
theorem Shift.next_chain (_H : Shift Q C c₀) {j : ℕ} (hj : j < C.m) (h6 : c₀ + C.m ≤ 2 * C.m + 6) :
    ztqsa % (C.sideWalk C.sideBeta).n = ztl + c₀ := by
  rw [Chain.sideWalk_n, Nat.mod_eq_of_lt by_omega]; ring
theorem Shift.prev_chain (_H : Shift Q C c₀) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ C.m) :
    (j + c₀ + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = zthv + c₀ := by
  have := _H.le
  rw [Chain.sideWalk_n, show j + c₀ + ztz - 1 = (j - 1 + c₀) + ztz by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
theorem next_W (T : Top Q C) {j : ℕ} (hj : j < C.m) :
    ztl % (interiorWalk Q).n = j + 1 := by
  rw [iw_n, Nat.mod_eq_of_lt (by have := T.hm; omega)]
theorem prev_W (T : Top Q C) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ C.m) :
    (j + (interiorWalk Q).n - 1) % (interiorWalk Q).n = j - 1 := by
  have := T.hm
  rw [iw_n, show j + Q.n - 1 = zthv + Q.n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt by_omega]

/-- **The points agree.** -/
theorem Shift.pt_eq (H : Shift Q C c₀) (T : Top Q C) {j : ℕ} (hj : j < C.m) (s : ℝ) :
    sidePt ztcs zthie s = sidePt ztkb j s := by
  zucky
  rw [H.next_chain hj H.le, next_W T hj, H.vtx j hj.le, H.vtx _ hj]

/-- **The left sectors agree.** -/
theorem Shift.sec_eq (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) {j : ℕ} (hj : j < C.m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hsj : s = 0 → 1 ≤ j) (y : Point) :
    sideLeft ztcs zthie s y ↔ sideLeft ztkb j s y := by
  zubdo
  have hjn : j < (interiorWalk Q).n := by rw [iw_n]; have := T.hm; omega
  zukme
  · have hne2 : (interiorWalk Q).vtx j ≠ (interiorWalk Q).vtx ztytb :=
      hM.nd j hjn
    have hne1 : (C.sideWalk C.sideBeta).vtx zthie ≠
        (C.sideWalk C.sideBeta).vtx (ztqsa % (C.sideWalk C.sideBeta).n) := by
      rw [H.next_chain hj H.le, H.vtx j hj.le, H.vtx ztl hj, ← next_W T hj]; omega
    rw [Chazelle.Chain.sideLeft_edge hne1 by_simp_all, Chazelle.Chain.sideLeft_edge hne2 by_simp_all,
      H.next_chain hj H.le, H.vtx j hj.le, H.vtx _ hj, next_W T hj]
  · subst hs
    have hj1 := hsj rfl
    rw [Chazelle.Chain.sideLeft_zero, Chazelle.Chain.sideLeft_zero, H.prev_chain hj1 hj.le,
      H.next_chain hj H.le, prev_W T hj1 hj.le, next_W T hj, H.vtx j hj.le, H.vtx _ hj,
      H.vtx _ by_omega]

/-- **The piece of an attached chord is attached.** -/
theorem piece_of_attach (hQ : Q.Simple) (T : Top Q C) {F₀ : Set ztf}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {c : Set Point} (hc : c ∈ F₀) {j : ℕ} {s : ℝ}
    (hA : SideAttach ztkb c j s)
    (hP : sidePt ztkb j s ∉ C.dom) :
    ∃ d ∈ pieces Q F₀, SideAttach ztkb d j s := by
  zudg
  obtain ⟨hp, hs0, hs1, hmem, r, hr, hnear⟩ := hA
  obtain ⟨r', hr', hclean⟩ := FactsInterior.clean hWs hWo hp hs0 hs1
  set P := sidePt ztkb j s with hPdef
  zudji
  zuheu
  -- points of the chord near `P` are interior
  have hin : ∀ x ∈ hseg y a b, x ≠ P → dist x P < min r r' → x ∈ Q.filled \ Q.boundary := by
    intro x hx hne hd
    zujuk
    have hl := hnear x hx hne by_simp_all
    simp_all
  have hrr : 0 < min r r' := by_grind
  obtain ⟨hPy, hPa, hPb⟩ := hmem
  have hPab : P.1 = a ∨ P.1 = b := by
    zufm
    exact hP (by
      have e : P = (P.1, y) := by_grind
      zvmwe; exact hch.open_mem _ by_grind by_grind)
  zumcw
  have hdist : ∀ t : ℝ, dist (ztevw : Point) P = |t - P.1| := by
    zujbn
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hPy, sub_self, abs_zero]
    simp
  set δ := min zteuc zthu / 2 with hδ
  zukhp
  have hδ1 : δ < min r r' := by_grind
  have hδ2 : δ < b - a := by_grind
  have hPne : ∀ t : ℝ, t ≠ P.1 → (ztevw : Point) ≠ P := by_grind
  rcases hPab with hPa' | hPb'
  · -- `P` is the left end
    have hz := hin (a + δ, y) ztbci by_grind
      (by rw [hdist, hPa', show a + δ - a = δ by ring, abs_of_pos hδ0]; omega)
    obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord by_grind
      ztgjd ztgje hz hQ
    have ha'a : a' = a := by
      zuct
      have hlt : a < a' := by_grind
      exact hch'.left_not (hin ztfoz ⟨rfl, ha', by_linarith⟩ by_grind
        (by rw [hdist, hPa', abs_of_pos by_linarith]; linarith))
    subst ha'a
    refine ⟨hseg y a' b', ⟨ztcpc, hseg y a' b, hc, fun q hq =>
      ⟨hq.1, hq.2.1, by linarith [hq.2.2]⟩⟩,
      hp, hs0, hs1, ztrcu, r, hr, fun x hx hne hd =>
      hnear x ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩ hne hd⟩
  · -- `P` is the right end
    have hz := hin (b - δ, y) ztbci by_grind
      (by rw [hdist, hPb', show b - δ - b = -δ by ring, abs_neg, abs_of_pos hδ0]; omega)
    obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord by_grind
      ztgjd ztgje hz hQ
    have hb'b : b' = b := by
      zuct
      have hlt : b' < b := by_grind
      exact hch'.right_not (hin ztfpb ⟨rfl, by_linarith, hb'⟩ by_grind
        (by rw [hdist, hPb', abs_of_neg by_linarith]; linarith))
    subst hb'b
    refine ⟨hseg y a' b', ⟨ztcpc, hseg y a b', hc, fun q hq =>
      ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩⟩,
      hp, hs0, hs1, ztrcu, r, hr, fun x hx hne hd =>
      hnear x ⟨hx.1, by zunsm, hx.2.2⟩ hne hd⟩
theorem wrapK_self {n x : ℝ} (hx : x < n) : wrapK n x = x := by unfold wrapK; simp_all

/-- **The key correspondence of the transition.** -/
theorem transCorr (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set ztf} (hF₀ : F₀ ⊆ (chainModel C).Adm) {U V : Set Point} (hVU : V ⊆ U) :
    ArcT.ArcCorr ztc ztd F₀ ztcfd U V 0 C.m
      (fun x => x + c₀) := by
  have hM₁ : ztezg := walkAx_chainModel hP
  zucwk
  zufug
  have hle := H.le
  have hsix := H.six
  -- the position of a key of `(0, m)`
  have hpos : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) C.m → ⌊x⌋₊ < C.m ∧ 0 ≤ x - ⌊x⌋₊ ∧ x - ⌊x⌋₊ < 1 ∧
      ⌊x + c₀⌋₊ = ⌊x⌋₊ + c₀ ∧ x + c₀ - ⌊x + c₀⌋₊ = x - ⌊x⌋₊ := by
    zuh
    have hfl : ⌊x + c₀⌋₊ = ⌊x⌋₊ + c₀ := by
      rw [show x + c₀ = x + ((c₀ : ℕ) : ℝ) from rfl, Nat.floor_add_natCast hx.1.le]
    refine ⟨?_, sub_nonneg.2 ztvaf, by linarith [Nat.lt_floor_add_one x], hfl, ?_⟩
    · have  := lt_of_le_of_lt ztvaf hx.2
      simp_all
    simp_all
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · zvnux; exact_mod_cast T.n_pos
  · rw [hWn, zero_add]; exact_mod_cast by_grind
  · intro x _ y _ hxy; simp_all
  · zuh
    zuevy
    zuoxr
    have : (x : ℝ) + c₀ ≤ C.m + c₀ := by_simp_all
    have h2 : ((C.m + c₀ : ℕ) : ℝ) < ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast by_omega
    grind
  · zujbw
    refine ⟨y - c₀, by_simp_all, by_ring⟩
  · zukjy
    have hkc : c₀ ≤ k := by
      have : (c₀ : ℝ) < k := by_grind
      exact_mod_cast this.le
    exact hv (k - c₀) (by push_cast [hkc]; linarith)
  · zudqi

    obtain ⟨k, hk⟩ := hnv
    exact hnv' (k + c₀) by_simp_all
  · -- cuts
    zudta
    zudrk
    set j := ⌊x⌋₊ with hj
    set s := x - j with hs
    have hkey : ((p₁ : ℕ) : ℝ) + t₁ = ((j + c₀ : ℕ) : ℝ) + s := by
      grind
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA₁.2.1 hA₁.2.2.1 ht0 ht1 hkey
    have hsj : ztppu := by
      zubww
      by_contra hj0; push Not at hj0
      zudgu
      have hx0 : ztsmx := by rw [hs, this] at h0; grind
      simp_all
    have hA₂ : SideAttach _ c j s :=
      ExtG.attach_of_sector (H.pt_eq T hjm s).symm
        (fun y hy => (H.sec_eq T hQ hjm ht0 ht1 hsj y).1 hy)
        zthex ht0 ht1 hA₁
    have hPd : sidePt ztkb j s ∉ C.dom := by
      rw [← H.pt_eq T hjm s]
      exact hM₁.trace _ (by zuoxr; omega) s ht0 ht1.le
    obtain ⟨d, hd, hAd⟩ := piece_of_attach hQ T hF₀ hc hA₂ hPd
    have hxn : ztlbj := by
      zufnj

    refine ⟨d, hd, j, s, hAd, ?_⟩
    rw [wrapK_self hxn, hs]; ring
  · -- faces
    intro x hx _ hfa
    zudrk
    have hxn : ztlbj := by
      zufnj

    rw [wrapK_self hxn] at hfa
    zukuf
    refine ExtG.faces_of_offset one_pos (fun δ => ?_) hVU hfa
    zuoev
    show Chazelle.Jordan.offset ((C.sideWalk C.sideBeta).vtx _)
      ((C.sideWalk C.sideBeta).vtx ((⌊x⌋₊ + c₀ + 1) % (C.sideWalk C.sideBeta).n)) _ δ =
      Chazelle.Jordan.offset ((interiorWalk Q).vtx ⌊x⌋₊)
        ((interiorWalk Q).vtx (ztpew % (interiorWalk Q).n)) _ δ
    rw [H.next_chain hjm H.le, next_W T hjm, H.vtx _ hjm.le, H.vtx _ hjm]
  · -- counted
    zumhq
    obtain ⟨hjm, -, -, hfl, -⟩ := hpos x hx
    zumng
    show 6 ≤ ⌊x⌋₊ + c₀ ∧ ⌊x⌋₊ + c₀ < 2 * C.m + 6
    omega

/-- **A straight piece of an arc** inside `[0, m]` weighs at most the weight of `U`. -/
theorem piece_wt (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set ztf} (hF₀ : F₀ ⊆ (chainModel C).Adm) (hfin : F₀.Finite)
    {U V : Set Point} (hU : U ∈ (chainModel C).regions F₀) (hVU : V ⊆ U) {a b a' b' : ℝ}
    (harc : (interiorModel Q).IsArc ztcfd V a b) (h0 : 0 ≤ a') (hab' : a' < b')
    (hm : b' ≤ C.m) (hsub : ∀ x, a' < x → x < b' → sideInArc a b x) :
    (interiorModel Q).arcWt a' b' ≤ (chainModel C).weight F₀ U := by
  zufug
  have hmn : (C.m : ℝ) < Q.n := by exact_mod_cast (show C.m < Q.n by have := T.hm; omega)
  have hplain : ∀ x, sideInArc a' b' x ↔ a' < x ∧ x < b' := fun x => by
    zuxb
  refine ArcT.arcWt_le ztwhs hF₀ hfin hU (transCorr H T hQ hP hF₀ hVU) h0 hab' hm ?_ ?_ ?_ ?_
  · intro x _ hxn hx
    exact ⟨x, by_simp_all, wrapK_self hxn⟩
  · intro xx hxx
    rw [wrapK_self by_grind]
    simp_all
  · zuh
    exact harc.2.2.2.2.2.1 x by_simp_all
  · intro p t hp ht0 ht1 hx
    exact harc.2.2.2.2.2.2 p t hp ht0 ht1 by_simp_all

/-- The keys after `m` meet only the last walk edge. -/
theorem arcWt_last (T : Top Q C) : (interiorModel Q).arcWt C.m 0 ≤ 1 := by
  zufug
  rw [BoxT.arcWt_eq']
  calc (BoxT.edgesIn _ C.m 0).ncard ≤ ({C.m} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton _)
        zuecg
        zukti
        have hm0 : ¬ ((C.m : ℝ) < 0) := by_simp
        zuhba
        rw [ite_eq_right hm0] at hx
        have h1 : ztehg := by
          grind
        have h2 : ztiye := by exact_mod_cast h1
        have := T.hm
        grind
    _ = 1 := Set.ncard_singleton _

/-- **(T3) The weight of an arc after the transition** is at most `2 · weight U + 1`. -/
theorem arcWt_le_trans (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set ztf} (hF₀ : F₀ ⊆ (chainModel C).Adm) (hfin : F₀.Finite)
    {U V : Set Point} (hU : U ∈ (chainModel C).regions F₀) (hVU : V ⊆ U) {a b : ℝ}
    (harc : (interiorModel Q).IsArc ztcfd V a b) :
    (interiorModel Q).arcWt a b ≤ 2 * (chainModel C).weight F₀ U + 1 := by
  set w := (chainModel C).weight F₀ U
  have ha0 := harc.1
  zumdb
  have hm0 : (0 : ℝ) ≤ C.m := Nat.cast_nonneg _
  have hlast := arcWt_last T
  have pw := fun {a' b' : ℝ} (h0 : 0 ≤ a') (hab' : a' < b') (hm : b' ≤ C.m)
      (hsub : ∀ x, a' < x → x < b' → sideInArc a b x) =>
    piece_wt H T hQ hP hF₀ hfin hU hVU harc h0 hab' hm hsub
  -- membership in the last edge interval
  have hlastI : ∀ x : ℝ, (C.m : ℝ) < x → sideInArc (C.m : ℝ) 0 x := fun x hx => by
    zuxb
  zuul
  · have hin : ztiek := fun x => by
      zuxb
    zujsz
    · -- the piece `(a, min b m)` and the last edge
      have hbm : a < min b C.m := by_grind
      have h1 := pw ha0 hbm by_grind by_grind
      have hadd := BoxT.arcWt_le_add (M := interiorModel Q) (a₁ := a)
        (b₁ := min b C.m) (a₂ := C.m) (b₂ := 0) (fun p _ t _ _ hx => by
          zubik
          by_cases hxm : (p : ℝ) + t < C.m
          · left
            have : sideInArc a (min b C.m) ztk ↔ a < p + t ∧ p + t < min b C.m := by
              zujv
            grind
          · right
            push Not at hxm
            rcases hxm.lt_or_eq with h | h
            · grind
            · exfalso
              -- a vertex key is not of the form `p + t` with `0 < t < 1`
              zulh

              omega)
      omega
    · -- the arc lies on the last edge
      zumii
      have := BoxT.arcWt_le_of_sub (M := interiorModel Q) (a := a) (b := b) (a' := C.m) (b' := 0)
        by_grind
      omega
  · -- the arc wraps around: keys above `a` or below `b`
    have hin : ztiel := fun x => by
      zuxb
    set b' := min b (C.m : ℝ) with hb'
    have hb'0 : 0 ≤ b' := by_grind
    have hb'm : b' ≤ C.m := by_grind
    have hK : ∀ x, sideInArc (C.m : ℝ) b' x ↔ (C.m : ℝ) < x ∨ x < b' := fun x => by
      zujv
    -- the wrap-around interval `(m, b')` weighs at most `w + 1`
    have hKw : (interiorModel Q).arcWt (C.m : ℝ) b' ≤ w + 1 := by
      rcases hb'0.lt_or_eq with hpos | hzero
      · have h2 := pw le_rfl hpos hb'm by_grind
        have hadd := BoxT.arcWt_le_add (M := interiorModel Q)
          (a₁ := C.m) (b₁ := 0) (a₂ := 0) (b₂ := b') (fun p _ t ht0 _ hx => by
            rw [hK] at hx
            zuky
            · grind
            · right
              have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
              unfold sideInArc; grind)
        omega
      grind
    zujsz
    · have h1 := pw ha0 ham le_rfl by_grind
      have hadd := BoxT.arcWt_le_add (M := interiorModel Q) (a₁ := a)
        (b₁ := C.m) (a₂ := C.m) (b₂ := b') (fun p _ t ht0 ht1 hx => by
          zubik
          have hne : ztmrm := fun h => by
            zulh

            omega
          zuevn
          · zuky
            · left
              zujv
            grind
          grind)
      omega
    · zumii
      have := BoxT.arcWt_le_of_sub (M := interiorModel Q) (a' := C.m) (b' := b')
        (fun p _ t ht0 ht1 hx => by
          zubik
          zuky
          · grind
          · have hne : ztmrm := fun h => by
              zulh

              omega
            grind)
      omega
theorem semigranular_pieces (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q)
    {F₀ : Set ztf} (hF₀ : (chainModel C).ChordFamily C.P F₀) {γ : ℕ}
    (hγ : (chainModel C).Semigranular F₀ γ) :
    (interiorModel Q).Semigranular ztcfd ztpty := by
  zubwg
  obtain ⟨c₀, h6, hle, hvtx⟩ := exists_shift hQ T hD
  have H : Shift Q C c₀ := ⟨h6, hle, hvtx⟩
  zudic

  zudwr

  have := arcWt_le_trans H T hQ hP hF₀.2.1 hF₀.1 hU hVU hab
  have hw := hγ U hU
  grind

/-- **The transition** (T1–T4). -/
theorem transition (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q)
    {F₀ : Set ztf} (hF₀ : (chainModel C).ChordFamily C.P F₀) {γ d : ℕ}
    (hγ : (chainModel C).Semigranular F₀ γ) (hd : (chainModel C).DegLe F₀ d) :
    (interiorModel Q).ChordFamily Q ztcfd ∧
      (interiorModel Q).DegLe ztcfd d ∧
      (interiorModel Q).Semigranular ztcfd ztpty ∧
      (pieces Q F₀).ncard ≤ F₀.ncard := by
  zucwk
  zubb
  have hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 by_omega by_omega by_omega
  obtain ⟨hfam, hcard⟩ := chordFamily_pieces T hF₀ hQ hh
  exact ⟨hfam, degLe_pieces hQ T hh hF₀ hd, semigranular_pieces hQ T hD hF₀ hγ, hcard⟩
end
end Trans
namespace DrvT
@[expose] public section
open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE sideCcw sideCross sideDot)
open TourA (sA tourA)
variable {Q : Polygon} {C : Chain}

/-- The input index of interior walk vertex `j` (`n` vertices). -/
def idxI (li : Bool) (n j : ℕ) : ℕ := if li then j else n - 1 - j

/-- **The tour index** of interior walk vertex `0`: the side-`A` tour index of chain edge `0`
(if `LeftInside`) or of chain edge `m`. -/
noncomputable def i0 (C : Chain) (li : Bool) : ℕ := tourA C C.sideBeta (if li then 0 else C.m)

/-- **The inner-side shift** of the top chain. -/
noncomputable def c0 (C : Chain) (li : Bool) : ℕ := i0 C li + 6
theorem iw_vtx_idx {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {j : ℕ} (hj : j < Q.n) :
    (interiorWalk Q).vtx j = Q.vtx (idxI li Q.n j) := by
  zulbu
  zubah
  · zvnbq; exact Trans.iw_vtx_left ztvvn j
  · zvnoi; exact Trans.iw_vtx_right ztdzx hj
theorem idxI_lt {li : Bool} {n j : ℕ} (hj : j < n) : idxI li n j < n := by
  zumsw

/-- The tour start residue at `i0`. -/
theorem mod_i0 (li : Bool) :
    ztigy % ztbb = if li then 0 else C.m := by
  zubt
  unfold i0
  zus
  · exact TourA.mod_tourA by_omega
  · exact TourA.mod_tourA by_omega

/-- `sA` is the reduced tour start. -/
theorem sA_eq : sA C C.sideBeta = C.sideS C.sideBeta % ztbb := rfl

/-- The value of `i0` in terms of `sA`. -/
theorem i0_eq (li : Bool) :
    i0 C li = if li then (2 * C.m - sA C C.sideBeta) % ztbb
      else (3 * C.m - sA C C.sideBeta) % ztbb := by
  unfold i0 tourA
  grind

/-- **`sA` and the top index.** -/
theorem sA_top : (sA C C.sideBeta = C.topIdx ∧ C.topIdx < 2 * C.m) ∨
    (sA C C.sideBeta = 2 * C.m - C.topIdx ∧ 0 < C.topIdx) := by
  zuwi
  zubt
  rcases C.sideS_mod C.sideBeta with ⟨h, -⟩ | ⟨h, h0, -⟩
  · left; exact ⟨h, by_omega⟩
  tauto
theorem sA_lt' : sA C C.sideBeta < 2 * C.m := TourA.sA_lt

/-- `sA = 0` exactly when the top is the first vertex. -/
theorem sA_zero_iff : sA C C.sideBeta = 0 ↔ C.topIdx = 0 := by
  zuwi
  zubt
  zucoy

/-- `sA = m` exactly when the top is the last vertex. -/
theorem sA_m_iff : sA C C.sideBeta = C.m ↔ C.topIdx = C.m := by
  zuwi
  zubt
  zucoy
variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

/-- `i0 ≤ m`. -/
theorem i0_le : i0 C li ≤ C.m := by
  zubt
  zuhfp
  obtain ⟨hL1, hL2⟩ := Trans.sA_inner hQ T hD
  zumol
  zubah
  · zueyn
    rcases hL1 ztvvn with h0 | h0
    · simp_all
    · zupd
  · zubme
    have h1 := hL2 ztdzx
    rw [show 3 * C.m - sA C C.sideBeta = ztjhh + 2 * C.m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    omega

/-- **Chain walk vertex `j + c₀` is interior walk vertex `j`.** -/
theorem vtx_c0 {j : ℕ} (hj : j ≤ C.m) :
    (C.sideWalk C.sideBeta).vtx ztqrz = (interiorWalk Q).vtx j := by
  zubt
  zucwk
  zuhze
  have hr := mod_i0 (C := C) li
  unfold c0
  rw [show j + (i0 C li + 6) = ztqsc + 6 by ring,
    C.sideWalk_vtx_tour _ by_omega, iw_vtx_idx hli by_omega]
  zueev
  rw [Chain.sideIdx_eq, show C.sideS C.sideBeta + ztqsc =
      ztigy + j by ring, Nat.add_mod, hr]
  have hv : ztcee := fun k hk => T.vertex_eq by_omega
  zulbu
  zubah
  · zughp
    zuey
    zuhay
  · zuhpq
    rw [Nat.mod_eq_of_lt (show j < 2 * C.m by omega)]
    rcases hj.lt_or_eq with hj' | rfl
    · zuey
      zudma

    · rw [show C.m + C.m = 2 * C.m by ring,
        Nat.mod_self, Chazelle.Chain.sideE_zero, hv 0 by_omega]
      simp_all

/-- **The explicit shift.** -/
theorem shift_c0 : Trans.Shift Q C ztpe := by
  zuhze
  exact ⟨by unfold c0; omega, by unfold c0; omega, fun j hj => vtx_c0 hQ T hD hli hj⟩

/-- **The turn at interior walk vertex `0`**: unless it is the top vertex, the chain walk comes
back from interior walk vertex `1` and goes on to it. -/
theorem uturn_zero (hne : (interiorWalk Q).vtx 0 ≠ C.top) :
    1 ≤ i0 C li ∧ (C.sideWalk C.sideBeta).vtx ztqjh = (interiorWalk Q).vtx 1 := by
  zubt
  zuix

  have h1 : 1 ≤ i0 C li := by
    zuccr
    zugre
    have hi0 : i0 C li = 0 := by_omega
    zudcp

    zubah
    · zuikx
      have : sA C C.sideBeta = 0 := by
        by_contra hne0
        zuhkg
      rw [sA_zero_iff.1 this]
    · zueyr

      rw [show 3 * C.m - sA C C.sideBeta = ztjhh + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega] at hi0
      rw [sA_m_iff.1 by_omega]
      grind
  zujfv
  unfold c0
  rw [show i0 C li + 6 - 1 = ztqre + 6 by omega, C.sideWalk_vtx_tour _ by_omega,
    iw_vtx_idx hli by_omega]
  zueev
  zuewl
  -- the residue before `i0`
  set q := (C.sideS C.sideBeta + ztqre) % ztbb with hq
  have hqlt : q < 2 * C.m := Nat.mod_lt _ by_omega
  have hsucc : ztfo % ztbb = if li then 0 else C.m := by
    grind
  zulbu
  zubah
  · zvnbq at hsucc ⊢
    have hq' : q = 2 * C.m - 1 := by
      zuknf
      · zuhki
      · omega
    rw [hq', hv _ ztqgq]
    zubvs
  · zvnoi at hsucc ⊢
    have hq' : q = C.m - 1 := by
      zuknf
      · zuhki
      · rw [h2, Nat.mod_self] at hsucc; omega
    rw [hq', hv _ ztqgr]
    zubvs

/-- **The turn at interior walk vertex `m`**: unless it is the top vertex, the chain walk goes
back to interior walk vertex `m - 1`. -/
theorem uturn_last (hne : (interiorWalk Q).vtx C.m ≠ C.top) :
    i0 C li < C.m ∧
      (C.sideWalk C.sideBeta).vtx (c0 C li + C.m + 1) = (interiorWalk Q).vtx ztdfi := by
  zubt
  zuix

  have h1 : i0 C li < C.m := by
    zuccr
    zugre
    have hi0 : i0 C li = C.m := by_omega
    zudcp

    zubah
    · zuikx
      have : sA C C.sideBeta = C.m := by
        by_cases h00 : sA C C.sideBeta = 0
        · simp_all
        · zuhkg
      rw [sA_m_iff.1 this]
    · zueyr

      rw [show 3 * C.m - sA C C.sideBeta = ztjhh + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega] at hi0
      rw [sA_zero_iff.1 by_omega]
      simp_all
  zujfv
  unfold c0
  rw [show i0 C li + 6 + C.m + 1 = ztobl + 6 by ring,
    C.sideWalk_vtx_tour _ by_omega, iw_vtx_idx hli by_omega]
  zueev
  rw [Chain.sideIdx_eq, show C.sideS C.sideBeta + ztobl =
      ztigy + ztbpj by ring, Nat.add_mod, hr]
  zulbu
  zubah
  · zughp
    zuknd
    · rw [Nat.mod_eq_of_lt h2, hv _ ztqgq]
      zubvs
    · rw [h2, Nat.mod_self, Chazelle.Chain.sideE_zero, hv 0 by_omega]
      grind
  · zuhpq
    zuknd
    · rw [Nat.mod_eq_of_lt h2, show C.m + ztbpj = 1 + 2 * C.m by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega, hv _ (by unfold sideE; simp_all)]
      zubvs
    · rw [h2, Nat.mod_self, add_zero, Nat.mod_eq_of_lt by_omega,
        hv _ ztqgr]
      zubvs
omit hQ T hD hli in
/-- **At a turn every horizontal direction is in the left sector.** -/
theorem sideLeft_uturn {W : Polygon} {p : ℕ} {a : Point}
    (hprev : W.vtx ztbvk = a) (hnext : W.vtx ztwjb = a)
    (ha : a.2 ≠ (W.vtx p).2) {x : Point} (hx : x.2 = (W.vtx p).2) (hxv : x ≠ W.vtx p) :
    sideLeft W p 0 x := by
  rw [Chazelle.Chain.sideLeft_zero, hprev, hnext]
  zueez
  zubef
  have hB : a - W.vtx p ≠ 0 := by
    grind
  refine ⟨Chazelle.Chain.sideCross_self _, Chazelle.Chain.sideDot_self_pos hB, Or.inl ?_⟩
  have hx1 : x.1 ≠ (W.vtx p).1 := fun h => hxv (Prod.ext h hx)
  zuhax
end
@[expose] public section
open Set Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)

/-- **Points of a horizontal segment near any of its points.** -/
theorem hseg_near {y a b : ℝ} (hab : a < b) {e : Point} (he : e ∈ hseg y a b) {r : ℝ}
    (hr : 0 < r) : ∃ x ∈ hseg y a b, x ≠ e ∧ dist x e < r := by
  obtain ⟨hy, hae, heb⟩ := he
  have hdist : ∀ δ : ℝ, dist (ztjul : Point) e = |δ| := by
    intro δ
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy, sub_self, abs_zero,
      show e.1 + δ - e.1 = δ by ring]
    simp
  have hne : ∀ δ : ℝ, δ ≠ 0 → (ztjul : Point) ≠ e := by
    grind
  rcases heb.lt_or_eq with h | h
  · set δ := min ztzr (zttfk / 2) with hδ
    zufhl

    have hδ2 : δ ≤ zttfk / 2 := by_simp_all
    refine ⟨ztjul, ztgpk, by_grind,
      ?_⟩
    grind
  · set δ := min ztzr (zttjl / 2) with hδ
    have hea : a < e.1 := by_linarith
    zufhl

    have hδ2 : δ ≤ zttjl / 2 := by_simp_all
    refine ⟨(e.1 + -δ, y), ztgpk,
      by grind, ?_⟩
    grind

/-- **Uniqueness of attachment positions** in a model with the walk axioms: a position with the
same point whose left sector contains the points of the chord near it is the attachment
position. -/
theorem pos_eq_of_sector {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach M.W c p t) (hp' : p' < M.W.n) (ht' : 0 ≤ t')
    (ht1' : t' < 1) (hpt : sidePt M.W p' t' = sidePt M.W p t)
    (hsec : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt M.W p t → dist x ztbp < r →
      sideLeft M.W p' t' x)
    (hnear : ∀ r > 0, ∃ x ∈ c, x ≠ sidePt M.W p t ∧ dist x ztbp < r) :
    p' = p ∧ t' = t := by
  obtain ⟨hp, ht0, ht1, hmem, rA, hrA, hsA⟩ := hA
  obtain ⟨rS, hrS, hS⟩ := hsec
  zuchm
  set e := sidePt M.W p t with he
  have heD := hM.trace p hp t ht0 ht1.le
  have hend : WalkEnd M.W c e := by
    zvmyh at hmem
    obtain ⟨s, hs0, hs1, hs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hmem
    zunl
    · zuqy
      · grind
      · rw [h1, Chazelle.Geometry.lerp_one] at hs; grind
    · rw [← h0, Chazelle.Geometry.lerp_zero] at hs; grind
  zuct
  have hne' : ztppi := by_grind
  obtain ⟨r, hr, hdis⟩ := hend.2 p p' t t' hp ht0 ht1 hp' ht' ht1' hne' rfl hpt
  obtain ⟨x, hx, hxe, hxd⟩ := hnear (min r (min rA rS)) (lt_min hr (lt_min hrA hrS))
  have h1 : dist x e < r := by_grind
  have h2 : dist x e < rA := by_grind
  have h3 : dist x e < rS := by_grind
  exact hdis x (mem_ball.2 h1) by_grind by_grind
variable {Q : Polygon} {C : Chain}

/-- **Interior points lie strictly below the top vertex.** -/
theorem int_lt_top (hQ : Q.Simple) (T : Trans.Top Q C) {x : Point}
    (hx : x ∈ Q.filled \ Q.boundary) : x.2 < C.top.2 := by
  have hO := Chazelle.Jordan.isOpen_filled_sdiff_boundary hQ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x hx
  have hmem : ((x.1, x.2 + ε / 2) : Point) ∈ Q.filled \ Q.boundary := hball (by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show x.2 + ε / 2 - x.2 = ε / 2 by ring, abs_of_pos by_linarith]
    simp_all)
  have := T.filled_below_top hQ hmem.1
  grind

/-- A point strictly inside a segment with ends at distinct heights has neither end's
height. -/
theorem lerp_snd_ne {A B : Point} (h : A.2 ≠ B.2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (lerp A B s).2 ≠ A.2 ∧ (lerp A B s).2 ≠ B.2 ∧
      (lerp A B s).2 < max A.2 B.2 := by
  rw [Chazelle.Geometry.lerp_snd]
  zuici
  have hd : B.2 - A.2 ≠ 0 := by_grind
  refine ⟨fun e => hd ?_, fun e => hd ?_, ?_⟩
  · simp_all
  · grind
  · rcases lt_or_gt_of_ne h with h' | h'
    · rw [max_eq_right h'.le]; nlinarith
    · rw [max_eq_left h'.le]; nlinarith
variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli
omit hQ T hD hli in
/-- Distinct interior walk vertices have distinct heights. -/
theorem iw_snd_ne (_hQ : Q.Simple) (_T : Trans.Top Q C) (hD : Trans.DistinctH Q)
    (hli : li = true ↔ Mountain.LeftInside Q) {j k : ℕ} (hj : j < Q.n) (hk : k < Q.n)
    (hjk : j ≠ k) :
    ((interiorWalk Q).vtx j).2 ≠ ((interiorWalk Q).vtx k).2 := by
  rw [iw_vtx_idx hli hj, iw_vtx_idx hli hk]
  refine hD _ _ (idxI_lt hj) (idxI_lt hk) ?_
  zumsw
omit hli in
/-- **The open last edge lies in the domain of the top chain.** -/
theorem openLast_mem_dom {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lerp ztcpk ztccl s ∈ C.dom := by
  zucwk
  zubb
  have hh := hD C.m 0 by_omega by_omega by_omega
  obtain ⟨hne1, hne2, hlt⟩ := lerp_snd_ne hh hs
  set e := lerp ztcpk ztccl s with he
  have heE : e ∈ Q.edge C.m := by
    rw [T.last_edge]; exact Chazelle.Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
  have hefill : e ∈ Q.filled := Or.inl ⟨C.m, by_omega, heE⟩
  refine C.mem_dom_iff.2 ztcg
  · have hsq := Chazelle.Jordan.filled_subset_square Q hefill
    have := C.coordBound_lt_radius
    zukpz
    zulfx
  · rintro ⟨k, hk, hek⟩
    rw [T.chainEdge_eq' hk] at hek
    have hint := hQ.2.2 k C.m by_omega by_omega by_omega
    have hc : e ∈ Q.commonEndpoints k C.m := by_grind
    rcases hc.2 with h | h
    · grind
    · rw [show ztbpj % Q.n = 0 by rw [hmn, Nat.mod_self]] at h
      grind
  · intro hsl
    have h2 := (C.mem_slit_iff.1 hsl).2.1
    have hv1 := T.vtx_le_top (show C.m < Q.n by omega)
    have hv2 := T.vtx_le_top ztimc
    grind

/-- **A chord of the chain model whose points near its end are interior is attached on the
inner run.** -/
theorem inner_of_interior {c : Set Point} (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach ztcs c p t)
    (hnear : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt ztcs p t →
      dist x ztyfq < r → x ∈ Q.filled \ Q.boundary) :
    c0 C li ≤ p ∧ p ≤ c0 C li + C.m ∧ (p = c0 C li + C.m → t = 0) := by
  zubwg
  zulir
  zucwk
  zubb
  zudg
  zubfr

  zuhxv
  have hIn : ztcfx := Trans.iw_n
  zujmu
  set e := sidePt W p t with he
  have hc' := hc
  obtain ⟨y, a, b, hch, -, rfl⟩ := hc'
  zucgh
  obtain ⟨hp, ht0, ht1, hemem, -⟩ := hA'
  obtain ⟨rN, hrN, hN⟩ := hnear
  have hnearc : ∀ r > 0, ∃ x ∈ hseg y a b, x ≠ e ∧ dist x e < r :=
    fun r hr => hseg_near hch.lt hemem hr
  -- the end is a boundary point of `Q`
  have heD : e ∉ C.dom := hMC.trace p hp t ht0 ht1.le
  have hefill : e ∈ Q.filled := by
    have : e ∈ closure ztrx := by
      zujha
      zudik
      obtain ⟨x, hx, hxe, hxd⟩ := hnearc _ (lt_min hε hrN)
      exact ⟨x, by_simp_all, by
        rw [dist_comm]; simp_all⟩
    exact closure_minimal by_simp_all ztuxn this
  have hebd : e ∈ Q.boundary := by
    zumv
    exact heD (T.interior_sub_dom hQ by_simp_all)
  -- its interior walk position
  obtain ⟨j, hj, s, hs0, hs1, hjs⟩ :=
    FactsInterior.exists_pos_of_mem_boundary (W := interiorWalk Q) (by rw [hWb]; omega)
  rw [hIn] at hj
  obtain ⟨rI, hrI, hI⟩ := FactsInterior.interior_left hWs hWo by_linarith hs0 hs1
  -- the points of the chord near the end are in the interior walk's sector
  have hsecI : ∃ r > 0, ∀ x ∈ hseg y a b, x ≠ e → dist x e < r →
      sideLeft ztkb j s x := by
    refine ⟨min rN rI, by_grind, fun x hx hxe hxd => ?_⟩
    refine hI x ?_ ?_
    · rw [mem_ball, hjs]; grind
    grind
  obtain ⟨rS, hrS, hS⟩ := hsecI
  -- points of the chord have the height of the end
  have hey := hemem.1
  have hxy : ∀ x ∈ hseg y a b, x.2 = e.2 := fun x hx => by rw [hey]; exact hx.1
  -- an interior point near the end, for the top cases
  have htopc : e ≠ C.top := by
    intro het
    obtain ⟨x, hx, hxe, hxd⟩ := hnearc rN hrN
    have h1 := int_lt_top hQ T (hN x hx hxe hxd)
    grind
  rcases (show j < C.m ∨ j = C.m by omega) with hjm | rfl
  · by_cases hj0 : j = 0 ∧ s = 0
    · -- the first vertex of the run
      obtain ⟨rfl, rfl⟩ := hj0
      have hev : e = (interiorWalk Q).vtx 0 := by zuoec
      obtain ⟨hi1, hprev⟩ := uturn_zero hQ T hD hli by_grind
      have hv0 : W.vtx ztpe = (interiorWalk Q).vtx 0 := by
        have := vtx_c0 hQ T hD hli (j := 0) by_omega; grind
      have hv1 : W.vtx (c0 C li + 1) = (interiorWalk Q).vtx 1 := by
        have := vtx_c0 hQ T hD hli hm1; grind
      have hc0 : 7 ≤ c0 C li := by unfold c0; omega
      have hpt : sidePt W ztpe 0 = e := by rw [Chazelle.Chain.sidePt_zero, hv0, hev]
      have hpos := pos_eq_of_sector hMC hc hA (by
          show c0 C li < W.n; zvnux; unfold c0; omega) le_rfl one_pos hpt
        ⟨1, one_pos, fun x hx hxe _ => sideLeft_uturn (W := W) (a := (interiorWalk Q).vtx 1)
          (by rw [hWn, show c0 C li + ztz - 1 = ztqjh + ztz by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt ztggt]; omega)
          ztyas
          (by rw [hv0]; exact iw_snd_ne hQ T hD hli by_omega by_omega by_omega)
          by_grind (by rw [hv0, ← hev]; tauto)⟩ hnearc
      omega
    · -- inside the run
      have hsj : ztppu := fun h0 => by
        grind
      have hpt : sidePt W ztqrz s = e := by rw [H.pt_eq T hjm s, hjs]
      have hpos := pos_eq_of_sector hMC hc hA (by
          show j + c0 C li < W.n; zvnux; unfold c0; omega) hs0 hs1 hpt
        ⟨rS, hrS, fun x hx hxe hxd =>
          (H.sec_eq T hQ hjm hs0 hs1 hsj x).2 (hS x hx hxe hxd)⟩ hnearc
      omega
  · zukme
    · -- the open last edge: impossible
      zulgd

      have hlast : sidePt ztkb C.m s = lerp ztcpk ztccl s ∨
          sidePt ztkb C.m s = lerp ztccl ztcpk s := by
        zucky
        rw [hIn, show ztbpj % Q.n = 0 by rw [hmn, Nat.mod_self],
          iw_vtx_idx hli by_omega, iw_vtx_idx hli by_omega]
        zulbu
        zubah
        · grind
        · right; rw [ite_eq_right h, ite_eq_right h, show Q.n - 1 - C.m = 0 by omega,
            show Q.n - 1 - 0 = C.m by omega]
      rw [← hjs]
      rcases hlast with h | h
      · zvmwc; exact openLast_mem_dom hQ T hD by_grind
      · rw [h, show lerp _ _ s = lerp ztcpk _ zteb by
          apply Prod.ext <;> zuowg <;> ring]
        exact openLast_mem_dom hQ T hD by_grind
    · -- the last vertex of the run
      subst hs
      have hev : e = (interiorWalk Q).vtx C.m := by zuoec
      obtain ⟨hi1, hnext⟩ := uturn_last hQ T hD hli by_grind
      have hvm : W.vtx ztqjg = (interiorWalk Q).vtx C.m := by
        have := vtx_c0 hQ T hD hli le_rfl; grind
      have hvm1 : W.vtx ztnws = (interiorWalk Q).vtx ztdfi := by
        have := vtx_c0 hQ T hD hli (j := C.m - 1) by_omega
        rwa [show C.m - 1 + c0 C li = c0 C li + C.m - 1 by omega] at this
      have hpt : sidePt W ztqjg 0 = e := by rw [Chazelle.Chain.sidePt_zero, hvm, hev]
      have hpos := pos_eq_of_sector hMC hc hA (by
          show c0 C li + C.m < W.n; zvnux; unfold c0; omega) le_rfl one_pos hpt
        ⟨1, one_pos, fun x hx hxe _ => sideLeft_uturn (W := W) (a := (interiorWalk Q).vtx _)
          (by rw [hWn, show c0 C li + C.m + ztz - 1 =
              ztnws + ztz by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt ztggt]; omega)
          ztyas
          (by rw [hvm]; exact iw_snd_ne hQ T hD hli by_omega by_omega by_omega)
          by_grind (by rw [hvm, ← hev]; tauto)⟩ hnearc
      grind
end
end DrvT
namespace Gran
open NFLoc
@[expose] public section
theorem robust_addr3 {E : ℕ} {m : ℕ → ℕ} {b₁ p₂ t v : ℕ} (hp₂ : p₂ < E)
    (h : Robust E m fun m' => m' ztodd = v) : m b₁ + m p₂ + t < E := by
  have hb₁ : b₁ < E := by
    zucux
    zueeg
    have := h ztzkb
      ztxl
    grind
  zucux
  have := h ztzjy (fun a ha => by
    grind)
  grind

/-- **The areas of a normal form readable below `E`.** -/
theorem nf_areas {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) :
    B + 7 < E ∧
    ztxhp ∧
    ztxht ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      m ztlw + m ztwnp + t < E) ∧
    ztxhs ∧
    (∀ j, j < N.seq.length → m ztcsw + j < E) := by
  have hB : B + 11 < E := robust_addr (v := N.dec.length) fun m' hm' => (h m' hm').2.2.2.2.1
  refine ⟨by_omega, fun i hi => ?_, fun r hr => ?_, fun r hr t ht => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := robust_addr2 (b := B + 3) (o := 5 * i + 4) (v := (N.chord i).dn)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        omega)
    omega
  · have := robust_addr2 (b := B + 5) (o := 5 * r + 4) (v := (N.region r).wt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        omega)
    omega
  · have hp : m zter + 5 * r + 3 < E := by
      have := robust_addr2 (b := B + 5) (o := 5 * r + 4) (v := (N.region r).wt)
        (fun m' hm' => by
          have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
          omega)
      omega
    have := robust_addr3 (b₁ := B + 7) (p₂ := m zter + 5 * r + 3) (t := t)
      (v := (N.region r).chords.getD t 0) hp (fun m' hm' => by
        zuhvt
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
        simp_all)
    omega
  · have := robust_addr2 (b := B + 4) (o := 5 * j + 4) (v := (N.arc j).e.hgt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.1 j hj).2.2.2.2
        omega)
    omega
  · have := robust_addr2 (b := B + 6) (o := j) (v := N.seq.getD j 0)
      (fun m' hm' => (h m' hm').2.2.2.2.2.2.2.2.1 j hj)
    omega
noncomputable def envOf (M : Model) (P : Polygon) (N : NF) (reg : ℕ → Set Point) (γ D kind m : ℕ) :
    Env := ⟨M, Qof P, N, reg, γ, D, decide (kind = 0), m⟩
variable {P : Polygon} {mem : ℕ → ℕ} {MD : ℕ} {M : Model} {N : NF} {reg : ℕ → Set Point} {γ D : ℕ}
/-- The model kind and chain length read from a descriptor describe the counted edges. -/
theorem desc_count
    (h : ModelDescAt mem MD zta M) :
    CountDesc M ztbahk ztxhe ∧
      (decide ztlrh = true → M.W.n = 2 * mem ztua + 7) ∧
      szOf P ztkat ztxhe = cntIn ztbahk ztxhe 0 M.W.n := by
  rcases h with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩
  · zukdj
    zuiyn
    rw [hm, h0]
    simp only [decide_true]
    refine ⟨⟨fun _ => by_omega, fun p hp => ?_⟩, fun _ => hn, ?_⟩
    · simp [chainModel]
    · unfold szOf cntIn; simp_all
  · zuwv
    simp only [show (1 : ℕ) ≠ 0 by decide, decide_false]
    refine ⟨⟨fun h => absurd h by_decide, fun p hp => ?_⟩, fun h => absurd h by_decide, ?_⟩
    · tauto
    · unfold szOf cntIn
      simp only [Bool.false_eq_true, ite_false, ite_eq_right (show (1 : ℕ) ≠ 0 by decide),
        Nat.sub_zero]
      show P.n = (interiorWalk zta).n
      rw [NFLoc.interiorWalk_n]
      exact (shear_n _ _).symm

/-- **The environment satisfies its hypotheses.** -/
theorem envOf_good
 (hMD : ModelDescAt mem MD zta M) (hGM : GoodModel M)
    (hNF : IsNF M zta N) (hRC : RegionCorr M zta N reg)
    (hCS : ChordSidesOK M zta N reg) (hRO : RegionsOK M zta N reg)
    (hne : (N.F M zta).Nonempty) :
    (envOf M P N reg γ D ztkat ztxhe).Good := by
  obtain ⟨hcd, hn, -⟩ := desc_count hMD
  exact ⟨walkAx_of_goodModel hGM, hGM, hNF, hRC, hCS, hRO, hne, hcd, hn⟩
theorem envOf_sz
 (hMD : ModelDescAt mem MD zta M) :
    (envOf M P N reg γ D ztkat ztxhe).sz = szOf P ztkat ztxhe :=
  (desc_count hMD).2.2.symm

/-- The chain length of a well-formed chain descriptor is below `64 n`. -/
theorem chain_m_le {E : ℕ} {mem : ℕ → ℕ} {MD : ℕ} {M : Model}
    (hwf : ModelDescWF P E mem MD) (h : ModelDescAt mem MD zta M) (h0 : mem MD = 0) :
    mem ztua ≤ 64 * P.n := by
  rcases h with ⟨-, H, C, hC, rfl⟩ | ⟨h1, -, -⟩
  · obtain ⟨hl, hwfH, -, -⟩ := (hwf.2 h0).2 H C hC
    have := NFLoc.chain_n_le hC hl hwfH
    zukdj
    have := C.m_lt
    omega
  · omega

/-- The number of counted edges is below the word bound. -/
theorem szOf_le {E W : ℕ} {mem : ℕ → ℕ} {MD : ℕ} {M : Model}
    (hwf : ModelDescWF P E mem MD) (h : ModelDescAt mem MD zta M)
    (hW : hostWords P.n ≤ W) : szOf P ztkat ztxhe ≤ W := by
  unfold szOf hostWords at *
  zujpn
  · have := chain_m_le hwf h h0; omega
  · omega
open Machine Machine.Stmt Programs SignK
def GF (b : ℕ) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ granBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    ztimx ∧
    (∀ a, a < b → c'.nmem a = c.nmem a) ∧ (∀ a, a < b → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k
variable {b : ℕ} {P : Polygon} {r : ℕ}
theorem GF.trans {c₁ c₂ c₃ : Config} {k₁ k₂ : ℕ} (h₁ : GF b c₁ c₂ k₁)
    (h₂ : GF b c₂ c₃ k₂) : GF b c₁ c₃ ztbct := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h₂
  exact ⟨by_simp_all, by_simp_all,
    by simp_all, by_simp_all, b5.trans a5,
    a6.trans b6, by_omega⟩
theorem GF.mono {c c' : Config} {k k' : ℕ} (h : GF b c c' k) (hk : k ≤ k') :
    GF b c c' k' := by
  zuddy
  exact ⟨a1, a2, a3, a4, a5, a6, by_omega⟩

/-- A natural-only statement writing registers of band `9` or `5` (`Bw`) and storing only at or
above `b` gives `GF b`. -/
theorem GF.of_nat {W b : ℕ} {s : Stmt} {c c' : Config} {k : ℕ} {Bw : ℕ → Bool}
    (e : Exec P W s c c' k) (hs : natOnly s = true) (hB : wrS Bw s = true)
    (hBw : ∀ r, Bw r = true → bandOf r ∈ granBands ∧ r ≠ ALLOC)
    (hm : ∀ a, a < b → c'.nmem a = c.nmem a) : GF b c c' k := by
  have F := exec_frameS e hB
  have N := exec_natOnly e hs
  have hA : Bw ALLOC = false := by
    grind
  refine ⟨fun r hr _ => F.1 r ?_, fun r _ => by rw [N.1], hm, fun a _ => by_simp_all, N.2.2,
    by zuokz, by zuokz; omega⟩
  grind
theorem band9_gran (h1 : 90000 ≤ r) (h2 : r < 100000) : bandOf r ∈ granBands ∧ r ≠ ALLOC := by
  unfold bandOf granBands kernelBands bGran ALLOC
  grind
theorem band5_gran (h1 : 50000 ≤ r) (h2 : r < 60000) : bandOf r ∈ granBands ∧ r ≠ ALLOC := by
  unfold bandOf granBands kernelBands bLocate ALLOC
  grind

/-! ## The first half -/

/-- Header, layout and allocation, chords, worklist, classes. -/
def initA : Stmt := .seq hdrStmt (.seq baseStmt (.seq chLoop (.seq stkLoop regLoop)))

/-- The state after the first half of the initialisation (layout `dmOf K A R D b0`). -/
structure InitMid (P : Polygon) (W MD NFH D γ : ℕ) (N : NF) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  r00 : c.nreg 90000 = MD
  r01 : c.nreg 90001 = NFH
  r02 : c.nreg 90002 = D
  r03 : c.nreg 90003 = γ
  r10 : c.nreg 90010 = N.nChords
  r11 : c.nreg 90011 = N.arcs.length
  r12 : c.nreg 90012 = N.nRegions
  r13 : c.nreg 90013 = c₀.nmem ztdfu
  r15 : c.nreg 90015 = c₀.nmem (NFH + 4)
  r17 : c.nreg 90017 = c₀.nmem zttam
  r23 : c.nreg 90023 = c₀.nmem MD
  r18 : c.nreg 90018 = szOf P zthvy ztbagy
  r14 : c.nreg 90014 = γ
  r19 : c.nreg 90019 = 1
  r20 : c.nreg 90020 = 3
  r21 : c.nreg 90021 = 2
  l00 : c.nreg 50000 = MD
  r26 : c.nreg 90026 = D * N.nChords
  r28 : c.nreg 90028 =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oList
  bases : Bases c ztyvw
  alloc : c.nreg ALLOC =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEnd
  live : ∀ u, u < N.nChords → c.nmem ztrnz = 1 ∧
    c.nmem ztpak = (N.chord u).up ∧
    c.nmem ztmhv = (N.chord u).dn
  stk : ∀ u, u < (dmOf N.nChords N.arcs.length N.nRegions D ztdq).cap →
    c.nmem ztxnv =
      u
  cls : ∀ x, x < N.nRegions →
    c.nmem ztxns =
      (N.region x).chords.length ∧
    c.nmem ztxnw =
      (N.region x).wt ∧
    c.nmem ztxnt =
      c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEx + D * x ∧
    ∀ t, t < D → c.nmem (c₀.nreg ALLOC +
      (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEx + D * x + t) =
      (N.region x).chords.getD t 0
  mem : ∀ a, (a < c₀.nreg ALLOC ∨
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEnd ≤ a) →
    c.nmem a = c₀.nmem a

/-- The cost of the first half. -/
def costA (K A R D : ℕ) : ℕ :=
  30 + (4 * R + 4 * D + 32 + 3 * (dmOf K A R D 0).oEnd) + (15 * K + 5) +
    (5 * (dmOf K A R D 0).cap + 4) + (ztjgg * R + 6)
set_option maxHeartbeats 4000000 in
theorem initA_exec {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF} {reg : ℕ → Set Point}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P ztm c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hNW : NFWithin c.nmem NFH ztm N) (hNF : IsNF M zta N)
    (hRC : RegionCorr M zta N reg) (hRO : RegionsOK M zta N reg)
    (hdeg : M.DegLe ztwiv D)
    (hroom : c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd ≤ W)
    (hK1 : 1 ≤ N.nChords) (hR1 : 1 ≤ N.nRegions) :
    ∃ c' k, Exec P W initA c c' k ∧ k ≤ costA N.nChords N.arcs.length N.nRegions D ∧
      InitMid P W MD NFH D γ N c c' ∧ GF ztm c c' k := by
  zusn

  zubjd

  have hEnd : d.oEnd = (dmOf K A R D 0).oEnd := rfl
  zuclw

  zudof
  have hWn : ztfku := by unfold hostWords at hWh; omega
  zuf
  have hdE := dmOf_oEnd K A R D b0
  -- 1. the header
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, q18, q14, q19, q20,
    q21, q50, q51, F₁⟩ := hdr_exec (P := P) c hw h0 h1 by_omega (by have := hwf.1; omega) hWn
    (fun h0' => by have := chain_m_le hwf hMD h0'; unfold hostWords at hWh; omega)
  zud
  rw [hN.1] at q10; rw [hN.2.1] at q11; rw [hN.2.2.1] at q12
  have g₁ := F₁.1
  have hA₁ : c₁.nreg ALLOC = b0 := g₁ _ by_decide
  -- 2. the layout
  obtain ⟨c₂, k₂, e₂, hk₂, B₂, a₂, x27, x28, x26, ab₂, r₂, m₂, F₂⟩ := base_exec (P := P) c₁ w₁
    (K := K) (A := A) (R := R) (by zunsp; rfl) (by rw [q11]) (by rw [q12]; rfl)
    (by rw [g₁ _ by_decide, h2]) q19 (by rw [hA₁]; exact hroom)
  rw [hA₁] at hk₂ B₂ a₂ x27 x28
  zue
  zumau
  have mem₂ : ztckc := by rw [m₂, F₁.2.2.1]
  -- the entry records
  have hrec : ∀ i, i < K → c₂.nmem (c.nmem ztdfu + 5 * i + 3) = (N.chord i).up ∧
      c₂.nmem (c.nmem ztdfu + 5 * i + 4) = (N.chord i).dn := fun i hi => by
    rw [mem₂]
    obtain ⟨-, -, -, h3', h4'⟩ := hN.2.2.2.2.2.1 i hi
    omega
  have hCB : ztyuc := by have := aCh ztfnu by_omega; omega
  have hRB : c.nmem ztnnh + 5 * R ≤ b0 := by have := aRg (R - 1) by_omega; omega
  zukbf
  -- 3. the chords
  have c2 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false → c₂.nreg r = c.nreg r :=
    fun r a1 a2 a3 a4 => by rw [g₂ r by_omega by_omega ztu, g₁ r a4]
  have t10 : zturm := by
    rw [g₂ _ by_omega by_omega by_decide, q10]; rfl
  have t13 : c₂.nreg 90013 = c.nmem ztdfu := by
    grind
  have t19 : ztizn := by_grind
  have t20 : c₂.nreg 90020 = 3 := by rw [g₂ _ by_omega by_omega ztu, q20]
  obtain ⟨c₃, k₃, e₃, hk₃, L₃, M₃, F₃⟩ := chLoop_exec (P := P) (d := d) (chords := N.chord) w₂ B₂
    rfl t10 t13 t19 t20 hrec hCB hbW hW5
  zubj
  have g₃ := F₃.1
  have B₃ := B₂.frame fun r a1 a2 => g₃ r ztbjn
  -- 4. the worklist
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, M₄, F₄⟩ := stkLoop_exec (P := P) (d := d) w₃ B₃
    (by rw [g₃ _ by_decide, t10, hdK])
    (by rw [g₃ _ by_decide, x26, hdD, hdK])
    (by rw [g₃ _ by_decide, t19]) hbW
  zucc
  have g₄ := F₄.1
  have B₄ := B₃.frame fun r a1 a2 => g₄ r ztbjn
  have t4 : ∀ r, Binit r = false → c₄.nreg r = c₂.nreg r := fun r h => by rw [g₄ r h, g₃ r h]
  -- 5. the classes
  have m4 : ∀ a, a < b0 → c₄.nmem a = c.nmem a := fun a ha => by
    rw [M₄ a by_omega, M₃ a by_omega, mem₂]
  have u2 : ∀ r, Binit r = false → 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false →
      c₄.nreg r = c.nreg r := fun r a0 a1 a2 a3 a4 => by rw [t4 r a0, c2 r a1 a2 a3 a4]
  have hrecR : ∀ r, r < R → RegRec c₄.nmem (c.nmem ztnnh) (c.nmem zttan) r
      (N.region r).chords.length (N.region r).wt (N.region r).chords := by
    zuz
    obtain ⟨-, a2, a4, -, a5⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have hr4 := aRg r hr
    refine ⟨by zunpa; exact a2, by zunpa; exact a4, fun t ht => ?_,
      rfl⟩
    have := aLst r hr t ht
    rw [m4 (c.nmem _ + 5 * r + 3) by_omega, m4 _ by_omega]
    exact a5 t ht
  obtain ⟨c₅, k₅, e₅, hk₅, C₅, M₅, F₅⟩ := regLoop_exec (P := P) (W := W) (R := R) (D := D)
    (RB := c.nmem ztnnh) (LB := c.nmem zttan) (d := d) (rg := N.region) w₄ B₄ rfl rfl
    (by rw [t4 _ by_decide, g₂ _ by_omega by_omega by_decide,
      g₁ _ by_decide, h2])
    (by rw [t4 _ by_decide, g₂ _ by_omega by_omega by_decide, q12]; rfl)
    (by rw [t4 _ by_decide, g₂ _ by_omega by_omega by_decide, q16])
    (by rw [t4 _ by_decide, g₂ _ by_omega by_omega by_decide, q22])
    (by rw [t4 _ by_decide, x27]; rfl)
    (by rw [t4 _ by_decide, t19]) (by rw [t4 _ by_decide, t20])
    (by rw [t4 _ by_decide, g₂ _ by_omega by_omega by_decide, q21])
    hrecR (fun r hr => chords_le hNF hRC hRO hdeg hr) hRB
    (fun r hr h1r => by
      have := aLst r hr ((N.region r).chords.length - 1) by_omega
      zunpa; omega) hbW hW5
  have u5 : ∀ r, Binit r = false → c₅.nreg r = c₂.nreg r := fun r h => by
    rw [F₅.1 r h, t4 r h]
  have v2 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → c₅.nreg r = c₁.nreg r := fun r a1 a2 a3 => by
    rw [u5 r ztbjn, g₂ r by_omega by_omega ztu]
  have v1 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false → c₅.nreg r = c.nreg r :=
    fun r a1 a2 a3 a4 => by rw [v2 r a1 a2 a3, g₁ r a4]
  have hGF1 : GF b0 c c₁ k₁ := GF.of_nat e₁ (Bw := Bhdr) by_decide by_decide
    (fun r hr => by
      simp only [Bhdr, Bool.or_eq_true, decide_eq_true_eq] at hr
      zuws
      · zulxy
      · zulxy
      · exact band5_gran by_omega by_omega
      · exact band5_gran by_omega by_omega)
    ztdnp
  have hGF2 : GF b0 c₁ c₂ k₂ := by
    have N2 := exec_natOnly e₂ by_decide
    refine ⟨fun r hr ha => F₂.1 r ?_, fun r _ => by rw [N2.1], fun a _ => by zunbg,
      fun a _ => by rw [N2.2.1], N2.2.2, by_omega, ab₂⟩
    simp only [Bbase, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨fun h => hr (band9_gran by_omega by_omega).1, ha⟩
  have hGF3 : GF b0 c₂ c₃ k₃ := GF.of_nat e₃ by_decide wrS_chLoop
    (fun r hr => by
      zuclp
      exact band9_gran by_omega by_omega)
    (fun a ha => M₃ a by_omega)
  have hGF4 : GF b0 c₃ c₄ k₄ := GF.of_nat e₄ by_decide wrS_stkLoop
    (fun r hr => by
      zuclp
      exact band9_gran by_omega by_omega)
    (fun a ha => M₄ a by_omega)
  have hGF5 : GF b0 c₄ c₅ k₅ := GF.of_nat e₅ by_decide wrS_regLoop
    (fun r hr => by
      zuclp
      exact band9_gran by_omega by_omega)
    (fun a ha => M₅ a zteem)
  refine ⟨c₅, _, .seq e₁ ztbq, ?_, ⟨e₅.wb_right, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    (hGF1.trans (hGF2.trans (hGF3.trans (hGF4.trans hGF5)))).mono le_rfl⟩
  · have c0 : (dmOf K A R D 0).cap = K + D * K := rfl
    have c1 : d.cap = K + D * K := rfl
    rw [hdE] at hk₂
    rw [c1] at hk₄
    unfold costA; rw [dmOf_oEnd, c0]; omega
  · rw [v1 _ by_norm_num by_norm_num by_norm_num by_decide, h0]
  · rw [v1 _ by_norm_num by_norm_num by_norm_num by_decide, h1]
  · rw [v1 _ by_norm_num by_norm_num by_norm_num by_decide, h2]
  · rw [v1 _ by_norm_num by_norm_num by_norm_num by_decide, h3]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q10]; rfl
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q11]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q12]; rfl
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q13]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q15]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q17]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q23]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q18]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q14, h3]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q19]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q20]
  · rw [v2 _ by_norm_num by_norm_num by_norm_num, q21]
  · rw [u5 _ by_decide, g₂ _ by_omega by_omega ztu, q50]
  · rw [u5 _ by_decide, x26]
  · rw [u5 _ by_decide, x28]
  · exact B₄.frame fun r a1 a2 => F₅.1 r ztbjn
  · rw [u5 _ by_decide, a₂]
  · zubgt
    obtain ⟨l1, l2, l3⟩ := L₃ u hu
    zusk
    · zunds; exact l1
    · zunds; exact l2
    · zunds; exact l3
  · zubgt
    zujum
    change c₅.nmem ztqdu = u
    rw [M₅ _ by_omega]; exact S₄ u hu
  · exact C₅
  · zuge
    change a < b0 ∨ b0 + d.oEnd ≤ a at ha
    zufxf
    rw [M₅ a (by rcases ha with h | h <;> [left; right] <;> omega),
      M₄ a (by rcases ha with h | h <;> [left; right] <;> omega),
      M₃ a (by rcases ha with h | h <;> [left; right] <;> omega), mem₂]
def finStmt : Stmt := block [.copyN 90050 90010, .copyN 90051 90010, .constN 90052 0]

/-- The second half. -/
def initB : Stmt := .seq posLoop (.seq ndLoop finStmt)

/-- The start edge of position `u`. -/
def edgeOf (N : NF) (u : ℕ) : ℕ := (N.arc zttak).s.edge

/-- The start height code of position `u`. -/
def hgtOf (N : NF) (u : ℕ) : ℕ := (N.arc zttak).s.hgt

/-- Reading an array. -/
def rdArr (m : ℕ → ℕ) (base : ℕ) : ℕ → ℕ := fun i => m zttgo

/-- The state after the initialisation (layout `dmOf K A R D b0`, `b0` the entry allocator). -/
structure InitEnd (P : Polygon) (W MD NFH D γ : ℕ) (M : Model) (N : NF) (c₀ c : Config) :
    Prop where
  wb : WordsBounded W c
  r00 : c.nreg 90000 = MD
  r01 : c.nreg 90001 = NFH
  r02 : c.nreg 90002 = D
  r03 : c.nreg 90003 = γ
  r10 : c.nreg 90010 = N.nChords
  r13 : c.nreg 90013 = c₀.nmem ztdfu
  r18 : c.nreg 90018 = szOf P zthvy ztbagy
  r14 : c.nreg 90014 = γ
  r19 : c.nreg 90019 = 1
  r20 : c.nreg 90020 = 3
  r21 : c.nreg 90021 = 2
  r28 : c.nreg 90028 =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oList
  r50 : c.nreg 90050 = N.nChords
  r51 : c.nreg 90051 = N.nChords
  r52 : c.nreg 90052 = 0
  bases : Bases c ztyvw
  alloc : c₀.nreg ALLOC +
    (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEnd ≤ c.nreg ALLOC
  live : ∀ u, u < N.nChords → c.nmem ztrnz = 1 ∧
    c.nmem ztpak = (N.chord u).up ∧
    c.nmem ztmhv = (N.chord u).dn
  stk : ∀ u, u < (dmOf N.nChords N.arcs.length N.nRegions D ztdq).cap →
    c.nmem ztxnv =
      u
  cls : ∀ x, x < N.nRegions →
    c.nmem ztxns =
      (N.region x).chords.length ∧
    c.nmem ztxnw =
      (N.region x).wt ∧
    c.nmem ztxnt =
      c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEx + D * x ∧
    ∀ t, t < D → c.nmem (c₀.nreg ALLOC +
      (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEx + D * x + t) =
      (N.region x).chords.getD t 0
  ring : ∀ j, j < N.arcs.length →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oNxt + j) =
      (if j + 1 < N.arcs.length then j + 1 else 0) ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oPrv + j) =
      (if 0 < j then j - 1 else N.arcs.length - 1) ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oEg + j) =
      bB zthgm zttjq ∧
    c.nmem ztxnu ≤ 1 ∧
    (c.nmem ztxnu = 1 ↔
      M.counted zttjq ∧ M.param zta ⟨edgeOf N j, hgtOf N j⟩ ≠ 0)
  cnt : ∀ j, j < N.arcs.length →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztdq).oCnt + j) =
      cntInit N.nChords
        (rdArr c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D
          ztdq).oNd0))
        (rdArr c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D
          ztdq).oNd1)) j
  nd0 : ∀ u, u < N.nChords →
    c.nmem ztmhw < N.arcs.length ∧
    pk M zta N (c.nmem ztmhw) = M.key zta (N.chord u).lpos
  nd1 : ∀ u, u < N.nChords →
    c.nmem ztmhx < N.arcs.length ∧
    pk M zta N (c.nmem ztmhx) = M.key zta (N.chord u).rpos
  mem : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a
set_option maxHeartbeats 4000000 in
theorem initB_exec {P : Polygon} {W : ℕ} {c c₅ : Config} {MD NFH D γ : ℕ} {M : Model} {N : NF}
    (hI : InitMid P W MD NFH D γ N c c₅) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P ztm c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH ztm N) (hNF : IsNF M zta N)
    (hne : (N.F M zta).Nonempty)
    (hroom : c₅.nreg ALLOC + N.nChords * zteky ≤ W) :
    ∃ c' k, Exec P W initB c₅ c' k ∧
      k ≤ 6052 * N.arcs.length + N.nChords * ztgyi + 12 ∧
      InitEnd P W MD NFH D γ M N c c' ∧ GF ztm c₅ c' k := by
  zusn

  zuf
  zufhv

  zubjd

  zuclw

  zullh
  have hmem5 : ∀ a, a < b0 → c₅.nmem a = c.nmem a := fun a ha => hI.mem a ztbbu
  have al5 : c₅.nreg ALLOC = b0 + d.oEnd := hI.alloc
  zukbf
  zuhxu
  zuc
  obtain ⟨hdesc₅, hwf₅⟩ := desc_agree' hwf hMD hmem5
  -- 1. the positions
  have hPE : PosEnv P W A MD _ _ d M (edgeOf N) (hgtOf N) c₅ :=
    { hG := hG, hW := hWh, hA := rfl, bW := hbW, bases := hI.bases, h11 := hI.r11,
      h15 := hI.r15, h17 := hI.r17, h19 := hI.r19,
      h23 := by rw [hI.r23, hmem5 _ (by have := hwf.1; omega)],
      h50 := hI.l00, wf := hwf₅, desc := hdesc₅,
      arcs := fun u hu => by
        have hs := aSeq u by_omega
        have ha := NFLoc.seq_lt hNF hu
        have hA4 := aArc _ ha
        have e1 : c₅.nmem (c.nmem zttam + u) = N.seq.getD u 0 := by
          rw [hmem5 _ by_omega]; exact hN.2.2.2.2.2.2.2.2.1 u by_omega
        obtain ⟨-, s1, s2, -⟩ := hN.2.2.2.2.2.2.1 _ ha
        refine ⟨by_omega, by_omega, ?_, ?_⟩
        · zunyy; exact s1
        · zunyy; exact s2
      edge_lt := fun u hu => edge_lt' hNF hne hu
      hgt_le := fun u hu => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := id hNF
        have := (hpp _ (NFLoc.seq_lt hNF hu)).1.2.2
        zvmxg at this; tauto }
  obtain ⟨c₆, k₆, e₆, hk₆, R₆, M₆, F₆⟩ := posLoop_exec (P := P) hI.wb hPE hW6
  zujb
  zumav
  have hmem6 : ∀ a, a < b0 → c₆.nmem a = c.nmem a := fun a ha => by
    rw [M₆ a by_omega, hmem5 a ha]
  obtain ⟨hdesc₆, hwf₆⟩ := desc_agree' hwf hMD hmem6
  have hK1 : 1 ≤ K := by
    zuxq

  have hcb : ztyuc := by have := aCh ztfnu by_omega; omega
  have al6 : c₆.nreg ALLOC = b0 + d.oEnd := by rw [g₆ _ by_decide, al5]
  -- 2. the chord ends
  have hNE : NdEnv P W MD NFH _ d M N c₆ :=
    { hG := hG, hWh := hWh, hGM := hGM, hNF := hNF, hne := hne, hK := rfl, hA := rfl,
      bases := hI.bases.frame fun r a1 a2 => g₆ r (by
        zubml
        omega),
      r00 := by rw [g₆ _ by_decide, hI.r00], r01 := by rw [g₆ _ by_decide, hI.r01],
      r10 := by rw [g₆ _ by_decide, hI.r10], r13 := by rw [g₆ _ by_decide, hI.r13],
      r19 := by rw [g₆ _ by_decide, hI.r19], r21 := by rw [g₆ _ by_decide, hI.r21],
      alloc := al6, wf := hwf₆, desc := hdesc₆,
      nfw := hNW.transport hmem6,
      chords := fun i hi => by
        obtain ⟨a0, a1, a2, -, -⟩ := hN.2.2.2.2.2.1 i hi
        have := aCh i hi
        exact ⟨by zunpb; exact a0, by zunpb; exact a1,
          by zunpb; exact a2⟩,
      cbB := hcb,
      room := by rw [al6, ← al5]; omega,
      cnt0 := fun j hj => (R₆ j hj).1 }
  zudof
  obtain ⟨c₇, k₇, e₇, hk₇, I₇, i₇, a₇⟩ := ndLoop_exec (P := P) w₆ hNE hW5
  have w₇ := I₇.wb
  have g₇ := I₇.r9
  have t7 : ∀ r, 90000 ≤ r → r < 90070 → Bpos r = false → c₇.nreg r = c₅.nreg r :=
    fun r a1 a2 a3 => by rw [g₇ r a1 by_omega ztbjn, g₆ r a3]
  -- 3. the end
  obtain ⟨c₈, k₈, e₈, hk₈, f50, f51, f52, fr, fm⟩ : ∃ c₈ k₈, Exec P W finStmt c₇ c₈ k₈ ∧ k₈ = 3 ∧
      c₈.nreg 90050 = K ∧ c₈.nreg 90051 = K ∧ c₈.nreg 90052 = 0 ∧
      (∀ r, r ≠ 90050 → r ≠ 90051 → r ≠ 90052 → c₈.nreg r = c₇.nreg r) ∧ c₈.nmem = c₇.nmem := by
    have t10 : c₇.nreg 90010 = K := by rw [t7 _ by_norm_num by_norm_num by_decide, hI.r10]
    unfold finStmt
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => by zunsq, rfl⟩ <;> config_simp
      · omega
      omega
  have u8 : ∀ r, 90000 ≤ r → r < 90050 → Bpos r = false → c₈.nreg r = c₅.nreg r :=
    fun r a1 a2 a3 => by rw [fr r by_omega by_omega by_omega, t7 r a1 by_omega a3]
  have m8 : ∀ a, a < c₆.nreg ALLOC → ztjnx →
      zteor → c₈.nmem a = c₆.nmem a := fun a h1 h2 h3 => by
    rw [fm, I₇.mem a h1 h2 h3]
  have hA6 := al6
  have hBp : ∀ r, bandOf r ∉ granBands → Bpos r = false := by
    zuz
    zubml
    have h1 : ¬ ztdew := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bSign, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    have h5 : ¬ ztdfc := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bLocate, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    have h9 : ztlyz := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bGran, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    omega
  have hGF6 : GF b0 c₅ c₆ k₆ := ⟨fun r hr _ => g₆ r zttlz, fun r hr => F₆.2.1 r zttlz,
    fun a ha => M₆ a by_omega, fun a _ => by rw [F₆.2.2.1], F₆.2.2.2,
    by omega, by_omega⟩
  have hGF7 : GF b0 c₆ c₇ k₇ := ⟨fun r hr ha => I₇.fr r (fun h => hr (by
      simp only [granBands, kernelBands, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h ⊢; tauto)) ha,
    fun r hr => I₇.frr r (fun h => hr (by
      simp only [granBands, kernelBands, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h ⊢; tauto)),
    fun a ha => I₇.mem a by_omega by_omega by_omega,
    fun a ha => I₇.frm a by_omega, I₇.fro, I₇.al1, a₇⟩
  have hGF8 : GF b0 c₇ c₈ k₈ := GF.of_nat e₈ (Bw := fun r => decide (90050 ≤ r ∧ r < 90053))
    by_decide by_decide
    (fun r hr => by
      have : 90050 ≤ r ∧ r < 90053 := by simpa using hr
      exact band9_gran by_omega by_omega)
    (fun a _ => by zuoyi)
  refine ⟨c₈, _, .seq e₆ ztjdu, ?_, ⟨by exact e₈.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, f50, f51, f52, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    (hGF6.trans (hGF7.trans hGF8)).mono le_rfl⟩
  · simp only [hKd, hAd] at hk₆ hk₇ ⊢; omega
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r00]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r01]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r02]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r03]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r10]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r13]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r18]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r14]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r19]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r20]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r21]
  · rw [u8 _ by_norm_num by_norm_num by_decide, hI.r28]
  · exact hI.bases.frame fun r a1 a2 => u8 r by_omega by_omega (by
      zubml
      omega)
  · change b0 + d.oEnd ≤ _
    rw [fr _ by_decide by_decide by_decide]
    have := I₇.al1; omega
  · zubgt
    change u < K at hu
    obtain ⟨l1, l2, l3⟩ := hI.live u hu
    change c₅.nmem _ = 1 at l1
    zuisg
    change c₅.nmem _ = _ at l3
    change c₈.nmem _ = 1 ∧ c₈.nmem _ = _ ∧ c₈.nmem _ = _
    zusk
    · zuedl
    · zuedm
    · zuedn
  · zubgt
    zujum
    change c₈.nmem ztqdu = u
    have := y4
    zufny
    exact hI.stk u hu
  · zuh
    change x < R at hx
    obtain ⟨l1, l2, l3, l4⟩ := hI.cls x hx
    change c₅.nmem _ = _ at l1
    zuisg
    change c₅.nmem _ = b0 + d.oEx + D * x at l3
    change ∀ t, t < D → c₅.nmem _ = _ at l4
    have hs := slot_le (D := D) hx ztbhw
    have hRD : d.R * d.D = R * D := rfl
    change c₈.nmem (b0 + d.oDeg + x) = _ ∧ c₈.nmem (b0 + d.oWt + x) = _ ∧
      c₈.nmem (b0 + d.oExb + x) = b0 + d.oEx + D * x ∧
      ∀ t, t < D → c₈.nmem (b0 + d.oEx + D * x + t) = _
    refine ⟨?_, ?_, ?_, fun t ht => ?_⟩
    · zuedl
    · zuedm
    · zuedn
    · have hs' := by_omega
      zufny
      exact l4 t ht
  · zun
    obtain ⟨-, r1, r2, r3, r4, r5⟩ := R₆ j hj
    change c₈.nmem _ = _ ∧ c₈.nmem _ = _ ∧
      c₈.nmem _ = _ ∧ c₈.nmem _ ≤ 1 ∧
      (c₈.nmem _ = 1 ↔ _)
    rw [m8 (b0 + d.oNxt + j) by_omega by_omega by_omega,
      m8 (b0 + d.oPrv + j) by_omega by_omega by_omega,
      m8 (b0 + d.oEg + j) by_omega by_omega by_omega,
      m8 (b0 + d.oPz + j) by_omega by_omega by_omega]
    rw [hmem5 MD (by have := hwf.1; omega)] at r3
    exact ⟨r1, r2, r3, r4, r5⟩
  · zun
    have := I₇.cnt j hj
    rw [i₇] at this
    change c₈.nmem _ = cntInit K _
      _ j
    zuoyi; exact this
  · zubgt
    have := I₇.nd0 u by_omega
    zuecx

  · zubgt
    have := I₇.nd1 u by_omega
    zuecx

  · zuge
    rw [m8 a by_omega by_omega by_omega, hmem6 a ha]
def initStmt : Stmt := .seq initA initB

/-- The cost of the initialisation. -/
def costInit (K A R D : ℕ) : ℕ :=
  costA K A R D + (6052 * A + K * (2 * NFLoc.locCost 5100 A + 32) + 12)

/-- The initial state read from the memory after the initialisation. -/
noncomputable def st0 (E : Env) (d : Dm) (m : ℕ → ℕ) : St :=
  initSt E (rdArr m (d.b0 + d.oNd0)) (rdArr m (d.b0 + d.oNd1)) (rdArr m (d.b0 + d.oEg))
    (rdArr m (d.b0 + d.oPz))
set_option maxHeartbeats 4000000 in
theorem init_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF} {reg : ℕ → Set Point}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P ztm c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH ztm N) (hNF : IsNF M zta N)
    (hRC : RegionCorr M zta N reg) (hCS : ChordSidesOK M zta N reg)
    (hRO : RegionsOK M zta N reg) (hne : (N.F M zta).Nonempty)
    (hdeg : M.DegLe ztwiv D) (hsemi : M.Semigranular ztwiv γ)
    (hroom : c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd +
      N.nChords * zteky ≤ W) :
    ∃ c' k, Exec P W initStmt c c' k ∧ k ≤ costInit N.nChords N.arcs.length N.nRegions D ∧
      MS W ztwns
        ztxcm ztm c.nmem c'
        (st0 ztwns
          ztxcm c'.nmem) ∧
      Inv ztwns
        (st0 ztwns
          ztxcm c'.nmem) ∧
      (envOf M P N reg γ D zteqv ztyih).Good ∧
      DimOK ztwns
        ztxcm W ∧
      c'.nreg 90052 = 0 ∧ c'.nreg 90000 = MD ∧ c'.nreg 90001 = NFH ∧ c'.nreg 90002 = D ∧
      c'.nreg 90003 = γ ∧ c'.nreg 90010 = N.nChords ∧ c'.nreg 90013 = c.nmem ztdfu ∧
      c'.nreg 90028 =
        c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztm).oList ∧
      c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D ztm).oEnd ≤
        c'.nreg ALLOC ∧
      GF ztm c c' k := by
  have hK1 : 1 ≤ N.nChords := by
    zuxq

  have hM : ztgpz := walkAx_of_goodModel hGM
  have hR1 : 1 ≤ N.nRegions := by rw [nRegions_eq hNF hM]; omega
  obtain ⟨c₅, k₅, e₅, hk₅, I₅, G₅⟩ := initA_exec (P := P) hw h0 h1 h2 h3 hWh hwf hMD hNW hNF hRC
    hRO hdeg by_omega hK1 hR1
  obtain ⟨c₈, k₈, e₈, hk₈, I₈, G₈⟩ := initB_exec (P := P) I₅ hG hWh hwf hMD hGM hNW hNF hne
    (by rw [I₅.alloc]; tauto)
  zubzc

  set st := st0 E d c₈.nmem with hst
  have hE : E.Good := envOf_good hMD hGM hNF hRC hCS hRO hne
  have henc : Enc c₈.nmem d st := by
    refine ⟨fun i hi => (I₈.live i hi).1, fun i hi => (I₈.live i hi).2.1,
      fun i hi => (I₈.live i hi).2.2, fun i _ => rfl, fun i _ => rfl,
      fun x hx => (I₈.cls x hx).1, fun x hx => (I₈.cls x hx).2.1,
      fun x hx => (I₈.cls x hx).2.2.1, fun x t hx ht => (I₈.cls x hx).2.2.2 t ht,
      fun j hj => I₈.cnt j hj, fun j hj => (I₈.ring j hj).1, fun j hj => (I₈.ring j hj).2.1,
      fun j _ => rfl, fun j _ => rfl, fun t ht => I₈.stk t ht⟩
  have hstat : StatOK E st :=
    ⟨fun i hi => I₈.nd0 i hi, fun i hi => I₈.nd1 i hi, fun j hj => (I₈.ring j hj).2.2.1,
      fun j hj => ⟨(I₈.ring j hj).2.2.2.1, (I₈.ring j hj).2.2.2.2⟩⟩
  have hI : Inv E st := Inv.init hE hstat hdeg hsemi
  have hsz : E.sz ≤ W := by rw [envOf_sz hMD]; exact szOf_le hwf hMD hWh
  have hW3 : ztpik := by_grind
  have hEnd : d.oEnd = (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd := rfl
  have hDim : DimOK E d W := ⟨rfl, rfl, rfl, rfl, by show c.nreg ALLOC + d.oEnd ≤ W; omega, hsz,
    hW3⟩
  have hC : Cst c₈ E d := Cst.of_bases I₈.bases I₈.r14 (by rw [I₈.r18, envOf_sz hMD]) I₈.r19
    I₈.r20 I₈.r21
  refine ⟨c₈, _, .seq e₅ e₈, ?_, ⟨I₈.wb, hC, henc, I₈.r50, I₈.r51, I₈.mem⟩, hI, hE, hDim,
    I₈.r52, I₈.r00, I₈.r01, I₈.r02, I₈.r03, I₈.r10, I₈.r13, I₈.r28, I₈.alloc,
    (G₅.trans G₈).mono le_rfl⟩
  unfold costInit
  omega
def trip (N : NF) (u : ℕ) : ℕ × ℕ × ℕ := ((N.chord u).h, (N.chord u).lp, (N.chord u).rp)

/-- The live record indices below `i`. -/
def liveList (live : ℕ → ℕ) (i : ℕ) : List ℕ := (List.range i).filter fun u => live u == 1

/-- The triples of the live records below `i`. -/
def outList (N : NF) (live : ℕ → ℕ) (i : ℕ) : List zte := (liveList live i).map (trip N)
variable (live : ℕ → ℕ) (i : ℕ) {P : Polygon} {W : ℕ} (c : Config) (N : NF) {m m' : ℕ → ℕ} {A : ℕ} {L : List (ℕ × ℕ × ℕ)}
theorem liveList_succ :
    liveList live ztg = liveList live i ++ (if live i = 1 then [i] else []) := by
  unfold liveList
  zubic
theorem mem_liveList {live : ℕ → ℕ} {i u : ℕ} : u ∈ liveList live i ↔ u < i ∧ live u = 1 := by
  unfold liveList; simp
theorem liveList_nodup : (liveList live i).Nodup :=
  (List.nodup_range).filter _

/-- **The list describes the current submap and is a valid input of the construction.** -/
theorem outList_ok {E : Env} {st : St} (hE : E.Good) :
    {c | ∃ x ∈ outList E.N st.live E.K, c = (recOf x).toSet E.M E.Q} = st.F E ∧
      ChordTriplesOK E.M E.Q (outList E.N st.live E.K) := by
  have hF : {c | ∃ x ∈ outList E.N st.live E.K, c = (recOf x).toSet E.M E.Q} = st.F E := by
    zubcj
    simp only [outList, List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨h1, h2⟩ := mem_liveList.1 hu
      exact ⟨u, ztwo, h1, rfl⟩
    · rintro ⟨u, ⟨h1, h2⟩, -, rfl⟩
      exact ⟨trip E.N u, ⟨u, mem_liveList.2 by_omega, rfl⟩, rfl⟩
  refine ⟨hF, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · zvoij; exact fam_chordFamily hE.hNF _
  · rw [outList, List.map_map]
    refine (liveList_nodup st.live E.K).map_on fun u hu v hv h => ?_
    exact cs_inj hE.hNF (mem_liveList.1 hu).1 (mem_liveList.1 hv).1 h
  · zudcg

    exact hE.hNF.2.2.1 u (mem_liveList.1 hu).1
  · zudcg

    zubts
    exact hh u (mem_liveList.1 hu).1

/-! ## The program -/

/-- Write the triple of record `r71` at `r96` (advanced by three) and count it in `r95`. -/
def writeT : Stmt := block [.loadN 90074 90071, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90075 90071 90019, .loadN 90074 90075, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90075 90071 90021, .loadN 90074 90075, .storeN 90096 90074, .addN 90096 90096 90019,
  .addN 90095 90095 90019]

/-- One record. -/
def outBody : Stmt :=
  .seq ztjoy
    (.seq ztjde ztiqt)

/-- **The output of the chord list** at `r28`, its length in `r95`. -/
def outStmt : Stmt := .seq (block [.constN 90070 0, .copyN 90071 90013, .constN 90095 0,
  .copyN 90096 90028, .constN 90076 5]) (.whileLtN 90070 90010 outBody)
theorem wrS_outStmt : wrS Binit outStmt = true := by_decide
set_option maxHeartbeats 2000000 in
theorem writeT_exec (hw : WordsBounded W c) {p q L : ℕ}
    (h71 : c.nreg 90071 = p) (h96 : c.nreg 90096 = q) (h95 : c.nreg 90095 = L)
    (h19 : c.nreg 90019 = 1) (h21 : c.nreg 90021 = 2) (hpq : p + 2 < q) (hq : q + 3 ≤ W)
    (hL : L + 1 ≤ W) :
    ∃ c' k, Exec P W writeT c c' k ∧ k = 12 ∧ c'.nreg 90096 = q + 3 ∧ c'.nreg 90095 = L + 1 ∧
      c'.nmem = upd (upd (upd c.nmem q (c.nmem p)) ztfo (c.nmem ztr)) (q + 2)
        (c.nmem ztcao) ∧
      (∀ r, r ≠ 90074 → r ≠ 90075 → r ≠ 90095 → r ≠ 90096 → c'.nreg r = c.nreg r) := by
  unfold writeT
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
    h71, h96, h95, h19, h21]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h71, h96, h95, h19, h21]

/-! ## Lists -/
theorem liveList_length_le : (liveList live i).length ≤ i := by
  unfold liveList
  grind
theorem outList_length_le (live : ℕ → ℕ) (i : ℕ) : (outList N live i).length ≤ i := by
  unfold outList; rw [List.length_map]; exact liveList_length_le live i
theorem outList_succ (live : ℕ → ℕ) (i : ℕ) :
    outList N live ztg = outList N live i ++ (if live i = 1 then [trip N i] else []) := by
  unfold outList; rw [liveList_succ, List.map_append]; grind
theorem ChordListAt.congr (h : ChordListAt m A L)
    (hm : ∀ a, A ≤ a → a < A + 3 * L.length → m' a = m a) : ChordListAt m' A L := by
  zug
  zuety
theorem ChordListAt.snoc {x : ℕ × ℕ × ℕ}
    (h : ChordListAt m A L) (hm : ∀ a, A ≤ a → a < A + 3 * L.length → m' a = m a)
    (h0 : m' ztgcw = x.1) (h1 : m' ztnid = x.2.1)
    (h2 : m' ztnie = x.2.2) : ChordListAt m' A ztffm := by
  zug
  zucjh
  rcases Nat.lt_or_ge i L.length with hl | hl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
    exact (ChordListAt.congr h hm) i hl
  grind

/-! ## The loop -/

/-- The output-loop invariant. -/
structure OutI (W K CB LB0 : ℕ) (N : NF) (live : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 90070 ≤ K
  ptr : c.nreg 90071 = CB + 5 * c.nreg 90070
  c76 : c.nreg 90076 = 5
  cnt : c.nreg 90095 = (outList N live zterb).length
  dst : c.nreg 90096 = LB0 + 3 * (outList N live zterb).length
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  list : ChordListAt c.nmem LB0 (outList N live zterb)
  mem : ∀ a, ztctr → c.nmem a = c₀.nmem a
theorem outHead_exec (hw : WordsBounded W c)
    (ha : c.nreg 90030 + c.nreg 90070 ≤ W) :
    ∃ c' k, Exec P W ztjoy c c' k ∧ k = 2 ∧
      c'.nreg 90073 = c.nmem (c.nreg 90030 + c.nreg 90070) ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 90072 → r ≠ 90073 → c'.nreg r = c.nreg r) := by
  exec_block
  · exact ha
  simp_all
theorem outTail_exec (hw : WordsBounded W c)
    (ha : c.nreg 90071 + c.nreg 90076 ≤ W) (hb : c.nreg 90070 + c.nreg 90019 ≤ W) :
    ∃ c' k, Exec P W ztiqt c c' k ∧
      k = 2 ∧ c'.nreg 90071 = c.nreg 90071 + c.nreg 90076 ∧
      c'.nreg 90070 = c.nreg 90070 + c.nreg 90019 ∧ c'.nmem = c.nmem ∧
      ztgsn := by
  exec_block
  · exact ha
  · simp_all
  simp_all

/-- The fixed data of the output loop. -/
structure OutEnv (W K CB LB0 b0 : ℕ) (N : NF) (live : ℕ → ℕ) (c₀ : Config) : Prop where
  r30 : c₀.nreg 90030 = b0
  r19 : c₀.nreg 90019 = 1
  r21 : c₀.nreg 90021 = 2
  r10 : c₀.nreg 90010 = K
  hlive : ∀ u, u < K → c₀.nmem (b0 + u) = live u
  hl01 : ∀ u, u < K → live u ≤ 1
  hrec : ∀ u, u < K → c₀.nmem (CB + 5 * u) = (N.chord u).h ∧
    c₀.nmem (CB + 5 * u + 1) = (N.chord u).lp ∧ c₀.nmem (CB + 5 * u + 2) = (N.chord u).rp
  hCB : CB + 5 * K ≤ LB0
  hb0 : b0 + K ≤ LB0
  hW : LB0 + 3 * K ≤ W
set_option maxHeartbeats 1000000 in
theorem outBody_exec {W K CB LB0 b0 : ℕ} {N : NF} {live : ℕ → ℕ} {c₀ c : Config}
    (hE : OutEnv W K CB LB0 b0 N live c₀) (hI : OutI W K CB LB0 N live c₀ c)
    (ht : c.nreg 90070 < K) :
    ∃ c' k, Exec P W outBody c c' k ∧ OutI W K CB LB0 N live c₀ c' ∧ k ≤ 19 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hi, hp, h76, hcnt, hdst, hr, hlist, hm⟩ := hI
  have c30 : c.nreg 90030 = b0 := by rw [hr _ by_decide, hE.r30]
  have c19 : zthoj := by rw [hr _ by_decide, hE.r19]
  have c21 : ztuok := by rw [hr _ by_decide, hE.r21]
  zuol
  have hCB := hE.hCB
  have hb0 := hE.hb0
  set i := c.nreg 90070 with hi_def
  set L := outList N live i with hL_def
  have hLi : L.length ≤ i := outList_length_le N live i
  have mlive : c.nmem (b0 + i) = live i := by rw [hm _ by_omega, hE.hlive i ht]
  obtain ⟨c₁, k₁, e₁, hk₁, r73, m₁, R₁⟩ := outHead_exec (P := P) c hw by_omega
  rw [c30, mlive] at r73
  zud
  -- the conditional write
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, r95, r96, lst, mm, R₂⟩ : ∃ c₂ k₂, Exec P W
      ztjde c₁ c₂ k₂ ∧ k₂ ≤ 14 ∧ WordsBounded W c₂ ∧
      c₂.nreg 90095 = (outList N live ztg).length ∧
      c₂.nreg 90096 = LB0 + 3 * (outList N live ztg).length ∧
      ChordListAt c₂.nmem LB0 (outList N live ztg) ∧
      (∀ a, ztctr → c₂.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 90072 → r ≠ 90073 → r ≠ 90074 → r ≠ 90075 → r ≠ 90095 → r ≠ 90096 →
        c₂.nreg r = c.nreg r) := by
    rw [outList_succ, ← hL_def]
    have h1 : ztgas := by_simp_all
    by_cases hl : live i = 1
    · simp only [hl, ite_true]
      have hrec := hE.hrec i ht
      obtain ⟨c₂, k₂, e₂, hk₂, r96', r95', m₂, R₂'⟩ := writeT_exec c₁ w₁ (p := CB + 5 * i)
        (q := LB0 + 3 * L.length) (L := L.length)
        by_simp_all by_simp_all
        by_simp_all h1
        by_simp_all by_omega by_omega by_omega
      have e₂' : Exec P W ztjde c₁ c₂ _ :=
        .ifLtN_false by_omega e₂
      have v0 : c₁.nmem ztblv = (N.chord i).h := by_grind
      have v1 : c₁.nmem ztbye = (N.chord i).lp := by
        grind
      have v2 : c₁.nmem ztbyf = (N.chord i).rp := by
        grind
      refine ⟨c₂, _, e₂', by_omega, e₂.wb_right, by_grind, by_grind,
        ?_, fun a ha => ?_, fun r a1 a2 a3 a4 a5 a6 => ?_⟩
      · refine ChordListAt.snoc hlist ztpbd ?_ ?_ ?_
        · rw [m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
            Machine.upd_other _ _ _ by_omega, m₁]
        · rw [m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
            Machine.upd_same, v0]; rfl
        · rw [m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_same, v1]; rfl
        · rw [m₂, Machine.upd_same, v2]; rfl
      · have hL : L.length < K := by_omega
        rw [m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
          Machine.upd_other _ _ _ by_omega, m₁, hm a ha]
      grind
    · have h0 : live i = 0 := by have := hE.hl01 i ht; omega
      simp only [hl, ite_false, List.append_nil]
      refine ⟨c₁, _, .ifLtN_true by_omega ztwd, by_omega, w₁,
        by simp_all, by_simp_all,
        by simp_all, by_simp_all,
        by simp_all⟩
  have c71 : ztoqw := by_grind
  have c76 : c₂.nreg 90076 = 5 := by_grind
  have c70 : zturn := by_grind
  have d19 : ztizn := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, r71, r70, m₃, R₃⟩ := outTail_exec (P := P) c₂ w₂
    by_omega by_omega
  rw [c71, c76] at r71
  rw [c70, d19] at r70
  refine ⟨c₃, _, .seq e₁ ztcr, ⟨e₃.wb_right, by_omega, by_omega, by
    grind, by_grind,
    by grind, fun r hr' => ?_, by_grind,
    fun a ha => by_grind⟩, by_omega, r70⟩
  have hb : ¬ ztnib := by simpa [Binit] using hr'
  grind

/-- **The output loop** writes the triples of the live records to the list area. -/
theorem out_exec {W K CB LB0 b0 : ℕ} {N : NF} {live : ℕ → ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : OutEnv W K CB LB0 b0 N live c₀) (h13 : c₀.nreg 90013 = CB)
    (h28 : c₀.nreg 90028 = LB0) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W outStmt c₀ c' k ∧ k ≤ 21 * K + 7 ∧
      c'.nreg 90095 = (outList N live K).length ∧ ChordListAt c'.nmem LB0 (outList N live K) ∧
      ztybi ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W outStmt c₀ c' k ∧ k ≤ 21 * K + 7 ∧
      c'.nreg 90095 = (outList N live K).length ∧ ChordListAt c'.nmem LB0 _ ∧
      ztybi by
    zudec
    exact ⟨c', k, e, h1, h2, h3, h4, exec_frameS e wrS_outStmt⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90095 0, .copyN 90096 90028, .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 5 ∧
      OutI W K CB LB0 N live c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, by_simp_all⟩, ?_⟩
      · simp
      · simp_all
      · config_simp
      · rfl
      · tauto
      · zubzi
        config_simp; simp only [upd]; grind
      · tauto
      simp
  zuidc
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90010)
    (body := outBody) (OutI W K CB LB0 N live c₀) ztnyn 19
    ztpf
    (fun c I ht => by
      have t : ztuol := by rw [I.regs 90010 by_decide, hE.r10] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := outBody_exec (P := P) hE I t
      grind) q
  have hK' : ztung := by
    rw [I'.regs 90010 by_decide, hE.r10] at hx; have := I'.i_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, by rw [I'.cnt, hK'], by rw [← hK']; exact I'.list, I'.mem⟩
  omega
def BuildOK (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem ztdph ztdo N ∧
          IsNF M zta N ∧ N.chords.map ztwma = L ∧ N.dec = [])
    ztzj

/-- The contract of a decomposition (the body of `DecompSpec`). -/
def DecompOK (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDecomp}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztefq ∧
      ∃ M N, ModelDescAt c.nmem ztefq zta M ∧
      GoodModel M ∧ NFWithin c.nmem ztczz ztm N ∧ IsNF M zta N ∧
      M.DegLe ztwiv zthzw)
    (fun P c c' => ∀ M N, ModelDescAt c.nmem ztefq zta M →
      NFAt c.nmem ztczz N → IsNF M zta N →
        ∃ N', c.nreg ALLOC ≤ rd c' bDecomp 3 ∧
          NFWithin c'.nmem ztrvn ztdo N' ∧
          N'.chords = N.chords ∧ N'.arcs = N.arcs ∧ N'.regions = N.regions ∧ N'.seq = N.seq ∧
          IsDecomp N' ztzvn)
    (fun _ c => κ * ztpdd *
      ztxkr)
theorem buildOK_of (h : BuildNFSpec) : ∃ s κ, BuildOK s κ := h
theorem decompOK_of (h : DecompSpec) : ∃ s κ, DecompOK s κ := h

/-- The chords of a list of triples. -/
def lset (M : Model) (Q : Polygon) (L : List zte) : Set ztf :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}
variable {M : Model} {Q : Polygon} {P : Polygon} {W : ℕ} (c : Config)
/-- Validity does not depend on the decomposition. -/
theorem isNF_congr {N N' : NF} (h : IsNF M Q N)
    (h1 : N'.chords = N.chords) (h2 : N'.arcs = N.arcs) (h3 : N'.regions = N.regions)
    (h4 : N'.seq = N.seq) : IsNF M Q N' := by
  obtain ⟨c, a, r, s, d, ro, l⟩ := N
  zudeb
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  zubh
theorem F_congr {N N' : NF} (h : N'.chords = N.chords) :
    N'.F M Q = N.F M Q := by
  zujqb
theorem F_of_map {N : NF} {L : List zte}
    (h : N.chords.map ztwma = L) : N.F M Q = lset M Q L := by
  zubst
  zubcj
  simp only [NF.F, lset, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · tauto
  · zudtc

/-- A frame from a register-only change. -/
theorem frame_of {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hr : ∀ r, bandOf r ∉ B → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output)
    (hA : bandOf ALLOC ∉ B) : Frame B c c' k := by
  have := hr ALLOC hA
  exact ⟨fun r h _ => hr r h, fun r _ => by zvnhk, fun a _ => by zvmwi,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩

/-- Build then decompose. -/
def bdStmt (sB sD : Stmt) : Stmt :=
  .seq (block [.copyN 40000 90000, .copyN 40001 90028, .copyN 40002 90095])
    (.seq sB (.seq (block [.copyN 60000 90000, .copyN 60001 40003, .copyN 60002 90002])
      (.seq sD (block [.copyN 90004 60003]))))

/-- The cost of `bdStmt` for `x` chords. -/
def costBD (κB κD D x : ℕ) : ℕ :=
  7 + κB * ztxyj + κD * ztef * ztxyj
theorem copy3_exec (hw : WordsBounded W c)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (hb₂ : b₂ ≠ a₁) (hb₃ : b₃ ≠ a₁) (hb₃' : b₃ ≠ a₂) :
    ∃ c' k, Exec P W (block [.copyN a₁ b₁, .copyN a₂ b₂, .copyN a₃ b₃]) c c' k ∧ k = 3 ∧
      c'.nreg a₁ = c.nreg b₁ ∧ c'.nreg a₂ = c.nreg b₂ ∧ c'.nreg a₃ = c.nreg b₃ ∧
      (∀ r, r ≠ a₁ → r ≠ a₂ → r ≠ a₃ → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  simp_all
theorem copy1_exec (hw : WordsBounded W c) (a b : ℕ) :
    ∃ c' k, Exec P W ztozb c c' k ∧ k = 1 ∧ c'.nreg a = c.nreg b ∧
      ztivh ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  simp_all
theorem band_not {r b : ℕ} {B : Finset ℕ} (hr : bandOf r = b) (hb : b ∈ B) :
    ¬ bandOf r ∉ B := fun h => h (hr ▸ hb)
set_option maxHeartbeats 1000000 in
/-- **Normal form and decomposition of the result.** -/
theorem bd_exec {sB sD : Stmt} {κB κD : ℕ} (hsB : BuildOK sB κB) (hsD : DecompOK sD κD)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {MD D LB : ℕ} {M : Model} {L : List zte}
    (h0 : c.nreg 90000 = MD) (h2 : c.nreg 90002 = D) (h28 : c.nreg 90028 = LB)
    (h95 : c.nreg 90095 = L.length)
    (hwf : ModelDescWF P ztm c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hGM : GoodModel M) (hL : ChordListAt c.nmem LB L) (hLB : LB + 3 * L.length ≤ c.nreg ALLOC)
    (hok : ChordTriplesOK M zta L) (hdeg : M.DegLe ztxef D)
    (hroom : c.nreg ALLOC + costBD κB κD D L.length ≤ W) :
    ∃ c' k, Exec P W zttgs c c' k ∧ k ≤ costBD κB κD D L.length ∧
      (∃ N', c.nreg ALLOC ≤ c'.nreg 90004 ∧
        NFWithin c'.nmem ztvgq ztdo N' ∧
        IsNF M zta N' ∧ N'.F M zta = lset M zta L ∧
        IsDecomp N' zttiy) ∧
      Frame granBands c c' k := by
  -- the arguments of the construction
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, R₁, rr₁, m₁, rm₁, o₁⟩ := copy3_exec (P := P) c hw
    40000 90000 40001 90028 40002 90095 by_decide by_decide by_decide by_decide
    by_decide by_decide
  zud
  have A₁ : ztdc :=
    R₁ _ by_decide by_decide by_decide
  have F₁ : Frame {bBuild} c c₁ k₁ := frame_of (fun r hr => R₁ r
    (band_not (r := 40000) rfl by_decide ∘ fun h => h ▸ hr)
    (band_not (r := 40001) rfl by_decide ∘ fun h => h ▸ hr)
    (band_not (r := 40002) rfl by_decide ∘ fun h => h ▸ hr)) rr₁ m₁ rm₁ o₁ by_decide
  have hX : L.length * ztjki + 1 ≤ L.length * ztjki + 1 :=
    le_rfl
  have r0 : rd c₁ bBuild 0 = MD := a0.trans h0
  have r1 : rd c₁ bBuild 1 = LB := a1.trans h28
  have r2 : rd c₁ bBuild 2 = L.length := a2.trans h95
  have hMD₁ : ModelDescAt c₁.nmem MD zta M := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, F₂⟩ := hsB P W c₁ w₁
    ⟨hG, hWh, by_simp_all, M, L, by_simp_all, hGM, r2,
      by omega, by_simp_all, hok⟩
    (by beta_reduce; rw [A₁, r2]; unfold costBD at hroom; omega)
  zuira
  rw [r2] at hk₂
  obtain ⟨N₁, g₁, hNW₁, hNF₁, hmap₁, -⟩ := post₂ M L by_grind r2
    by_grind
  zue
  have hF₁ : N₁.F M zta = lset M zta L := F_of_map hmap₁
  have hlen₁ : N₁.chords.length = L.length := by_grind
  -- the arguments of the decomposition
  obtain ⟨c₃, k₃, e₃, hk₃, b0, b1, b2, R₃, rr₃, m₃, rm₃, o₃⟩ := copy3_exec (P := P) c₂ w₂
    60000 90000 60001 40003 60002 90002 by_decide by_decide by_decide by_decide
    by_decide by_decide
  zubj
  have A₃ : ztbox := R₃ _ by_decide by_decide by_decide
  have F₃ : Frame {bDecomp} c₂ c₃ k₃ := frame_of (fun r hr => R₃ r
    (band_not (r := 60000) rfl by_decide ∘ fun h => h ▸ hr)
    (band_not (r := 60001) rfl by_decide ∘ fun h => h ▸ hr)
    (band_not (r := 60002) rfl by_decide ∘ fun h => h ▸ hr)) rr₃ m₃ rm₃ o₃ by_decide
  have k90000 : c₂.nreg 90000 = MD := by
    rw [F₂.1 _ by_decide by_decide, R₁ _ by_decide by_decide by_decide, h0]
  have k90002 : zturl := by
    rw [F₂.1 _ by_decide by_decide, R₁ _ by_decide by_decide by_decide, h2]
  have s0 : rd c₃ bDecomp 0 = MD := b0.trans k90000
  have s1 : rd c₃ bDecomp 1 = rd c₂ bBuild 3 := b1
  have s2 : rd c₃ bDecomp 2 = D := b2.trans k90002
  have hA12 : zteia := A₁ ▸ F₂.2.2.2.2.2.1
  have hlow : ztblg := fun a ha => by
    rw [m₃, F₂.2.2.1 a by_omega, m₁]
  obtain ⟨hMD₃, hwf₃⟩ := desc_agree' hwf hMD hlow
  have hNW₃ : NFWithin c₃.nmem ztrwk zterl N₁ := by
    grind
  have hcnt : c₃.nmem ztrwk = L.length := by
    rw [← hlen₁]; exact hNW₃.nfAt.1
  obtain ⟨c₄, k₄, e₄, hk₄, post₄, F₄⟩ := hsD P W c₃ w₃
    ⟨hG, hWh, by zuoyh; exact hwf₃.mono by_omega, M, N₁, by_grind, hGM, hNW₃,
      hNF₁, by_grind⟩
    (by
      beta_reduce
      rw [s2, hcnt, A₃]
      have := F₂.2.2.2.2.2.2
      unfold costBD at hroom
      omega)
  beta_reduce at hk₄
  rw [s2, hcnt] at hk₄
  obtain ⟨N₂, g₂, hNW₂, hc₂, ha₂, hr₂, hs₂, hdec₂⟩ := post₄ M N₁ by_grind
    hNW₃.nfAt hNF₁
  zucc
  -- the handle
  obtain ⟨c₅, k₅, e₅, hk₅, d0, R₅, rr₅, m₅, rm₅, o₅⟩ := copy1_exec (P := P) c₄ w₄ 90004 60003
  have A₅ : ztcrj := R₅ _ by_decide
  have F₅ : ztpka := frame_of (fun r hr => R₅ r
    (band_not (r := 90004) rfl by_decide ∘ fun h => h ▸ hr)) rr₅ m₅ rm₅ o₅ by_decide
  have FF := (((F₁.trans F₂).trans F₃).trans F₄).trans F₅
  refine ⟨c₅, _, .seq e₁ ztbq, ?_, ⟨N₂, ?_, ?_, ?_, ?_, ?_⟩,
    FF.mono by_decide by_omega⟩
  · unfold costBD; nlinarith
  · have := F₄.2.2.2.2.2.1
    rw [d0]
    show c.nreg ALLOC ≤ rd c₄ bDecomp 3
    omega
  · rw [d0, m₅, A₅]; exact hNW₂
  · exact isNF_congr hNF₁ hc₂ ha₂ hr₂ hs₂
  · rw [F_congr hc₂, hF₁]
  · have : N₂.nChords = N₁.nChords := by unfold NF.nChords; zumxp
    grind
def costMain (K A R D : ℕ) : ℕ :=
  costInit K A R D + (ztpuy * ztzbz + 2) + (21 * K + 7)

/-- The constant of the procedure. -/
def κGran (κB κD D : ℕ) : ℕ := 500000 * ztmo ^ 2 + κB + κD * ztef
theorem clog_two_le {K A : ℕ} (hA : A ≤ 2 * K) : Nat.clog 2 A ≤ Nat.clog 2 K + 1 := by
  zudwq
  have := Nat.le_pow_clog (by norm_num : 1 < 2) K
  omega
theorem costInit_le {K A R D : ℕ} (hA : A ≤ 2 * K) (hR : R = K + 1) :
    costInit K A R D ≤ 100000 * (D * K + D + K + 1) + 10880 * (K * ztgef) := by
  unfold costInit costA NFLoc.locCost
  rw [dmOf_oEnd]
  simp only [dmOf, Dm.cap]
  subst hR
  grind
theorem room_le (K A R D : ℕ) :
    (dmOf K A R D 0).oEnd + K * (2 * NFLoc.locCost 5100 A + 30) ≤ costInit K A R D := by
  unfold costInit costA
  grind
theorem costBD_mono {κB κD D x y : ℕ} (h : x ≤ y) : costBD κB κD D x ≤ costBD κB κD D y := by
  unfold costBD
  have := Nat.clog_mono_right 2 h
  gcongr
theorem cost_total {κB κD K A R D ℓ : ℕ} (hA : A ≤ 2 * K) (hR : R = K + 1) (hℓ : ℓ ≤ K) :
    4 + costMain K A R D + costBD κB κD D ℓ ≤
      κGran κB κD D * ztwko := by
  set X := K * ztho + 1 with hX
  have hKX : ztsbw := by_grind
  have hY : K * ztgef ≤ 2 * X := by
    have := clog_two_le hA
    have : K * ztgef ≤ K * ztqan := Nat.mul_le_mul_left _ by_omega
    grind
  have hℓX : ℓ * (Nat.clog 2 ℓ + 1) + 1 ≤ X := by
    have := Nat.mul_le_mul hℓ (Nat.add_le_add_right (Nat.clog_mono_right 2 hℓ) 1)
    omega
  have hI := costInit_le (D := D) hA hR
  set T := ztmo ^ 2 with hT
  have hT4 : 4 ≤ T := by_grind
  have hDK : D * K + D + K + 1 ≤ T * X := by
    grind
  have hL : ztpuy * ztzbz ≤ 402 * (T * X) := by
    grind
  have hX1 : X ≤ T * X := Nat.le_mul_of_pos_left X by_omega
  have hTX : 4 ≤ T * X := by_nlinarith
  have hB : costBD κB κD D ℓ ≤ 7 + (κB + κD * ztef) * X := by
    unfold costBD
    have := Nat.mul_le_mul_left κB hℓX
    have := Nat.mul_le_mul_left (κD * ztef) hℓX
    nlinarith
  unfold costMain κGran
  grind
def mainStmt : Stmt := .seq initStmt (.seq loopStmt outStmt)
theorem wrS_loop : wrS Bbody loopStmt = true := by
  rfl
theorem natOnly_loop : natOnly loopStmt = true := by_decide
theorem natOnly_out : natOnly outStmt = true := by_decide
set_option maxHeartbeats 2000000 in
/-- **The main path.** -/
theorem main_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P ztm c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH ztm N) (hNF : IsNF M zta N)
    (hne : (N.F M zta).Nonempty)
    (hdeg : M.DegLe ztwiv D) (hsemi : M.Semigranular ztwiv γ)
    (hroom : c.nreg ALLOC + costMain N.nChords N.arcs.length N.nRegions D ≤ W) :
    ∃ c' k L, Exec P W mainStmt c c' k ∧ k ≤ costMain N.nChords N.arcs.length N.nRegions D ∧
      c'.nreg 90000 = MD ∧ c'.nreg 90002 = D ∧ c'.nreg 90095 = L.length ∧
      L.length ≤ N.nChords ∧
      ChordListAt c'.nmem (c'.nreg 90028) L ∧ c'.nreg 90028 + 3 * L.length ≤ c'.nreg ALLOC ∧
      ChordTriplesOK M zta L ∧ lset M zta L ⊆ N.F M zta ∧
      M.DegLe ztxef D ∧ M.Granular ztxef γ ∧
      GF ztm c c' k := by
  obtain ⟨reg, hRC, hCS, -, hRO, -⟩ := hNF.2.2.2
  have hK1 : 1 ≤ N.nChords := by
    zuxq

  have hroomI := room_le N.nChords N.arcs.length N.nRegions D
  obtain ⟨c₈, k₈, e₈, hk₈, hMS, hI, hE, hDim, r52, r00, -, r02, -, r10, r13, r28, hal, G₈⟩ :=
    init_exec (P := P) hw h0 h1 h2 h3 hG hWh hwf hMD hGM hNW hNF hRC hCS hRO hne hdeg hsemi
      (by unfold costMain at hroom; omega)
  zubzc

  zukzk
  -- the worklist
  obtain ⟨c₉, k₉, st', e₉, hk₉, hMS', hI', htop, hR₉⟩ := loop_exec (P := P) hE hMS hI hDim
    le_rfl r52
  have FS₉ := exec_frameS e₉ wrS_loop
  have G₉ : GF ztm c₈ c₉ k₉ := GF.of_nat e₉ natOnly_loop wrS_loop
    (fun r hr => by
      simp only [Bbody, Bool.or_eq_true, decide_eq_true_eq] at hr
      exact band9_gran by_omega by_omega)
    (fun a ha => by rw [hMS'.low a ha, hMS.low a ha])
  -- the output
  have hNA := nf_areas hNW
  set CB := c.nmem ztdfu with hCBd
  have hCB : CB + 5 * K ≤ c.nreg ALLOC := by
    have := hNA.2.1 ztfnu by_omega
    omega
  have hd0 : d.b0 = c.nreg ALLOC := rfl
  have hdK : ztshu := rfl
  have hLB : d.oList + 3 * K = d.oEnd := rfl
  have hoL : K ≤ d.oList := by
    simp only [hd, dmOf, Dm.oList, Dm.oTmp, Dm.oStk, Dm.oPz, Dm.oEg, Dm.oPrv, Dm.oNxt, Dm.oCnt,
      Dm.oEx]
    omega
  have hbase := hDim.base
  have hOE : OutEnv W K CB (c.nreg ALLOC + d.oList) ztm N st'.live c₉ :=
    { r30 := hMS'.cst.bLive
      r19 := hMS'.cst.one
      r21 := hMS'.cst.two
      r10 := by rw [hR₉ _ by_decide, r10]
      hlive := fun u hu => hMS'.enc.live u hu
      hl01 := fun u hu => hI'.live01 u hu
      hrec := fun u hu => by
        have hb := hNA.2.1 u hu
        have hr := (hNW.nfAt.2.2.2.2.2.1 u hu)
        zusk
        · zueda
        · zueda
        · zueda
      hCB := by_omega
      hb0 := by_omega
      hW := by_omega }
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, r95, hlist, hmem, FS₁₀⟩ := out_exec (P := P) hMS'.wb hOE
    (by rw [hR₉ _ by_decide, r13]) (by rw [hR₉ _ by_decide, r28])
    by_omega
  have G₁₀ : GF ztm c₉ c₁₀ k₁₀ := GF.of_nat e₁₀ natOnly_out wrS_outStmt
    (fun r hr => by
      simp only [Binit, decide_eq_true_eq] at hr
      exact band9_gran by_omega by_omega)
    (fun a ha => hmem a by_omega)
  have q28 : c₁₀.nreg 90028 = c.nreg ALLOC + d.oList := by
    rw [FS₁₀.1 _ by_decide, hR₉ _ by_decide, r28]
  have qA : ztsgu := by
    rw [FS₁₀.1 _ by_decide, hR₉ _ by_decide]
  obtain ⟨hFeq, hok⟩ := outList_ok (st := st') hE
  obtain ⟨hgran, hdg⟩ := hI'.final hE htop
  have hlset : lset M zta (outList N st'.live K) = st'.F E := hFeq
  have hlen := outList_length_le N st'.live K
  refine ⟨c₁₀, _, outList N st'.live K, .seq e₈ (.seq e₉ e₁₀), ?_, ?_, ?_, r95, hlen,
    by grind, by_omega, hok, ?_, ?_, ?_,
    (G₈.trans (G₉.trans G₁₀)).mono le_rfl⟩
  · have hm : st0 E d c₈.nmem = initSt E _ _ _ _ := rfl
    have hmeas : (st0 E d c₈.nmem).meas E = K + ztef * K := by
      rfl
    have hED : E.D = D := rfl
    rw [hmeas, hED] at hk₉
    unfold costMain
    omega
  · rw [FS₁₀.1 _ by_decide, hR₉ _ by_decide, r00]
  · rw [FS₁₀.1 _ by_decide, hR₉ _ by_decide, r02]
  · zuofd; exact St.F_sub
  · zuofd; exact hdg
  · zuofd; exact hgran
def emptyS : Stmt := block [.constN 90095 0, .constN 90028 0]

/-- **Granularity enforcement.** -/
def granStmt (sB sD : Stmt) : Stmt :=
  .seq ztkri
    (.seq ztjdd zttgs)
theorem GF.frame {c c' : Config} {k : ℕ} (h : GF ztm c c' k) :
    Frame granBands c c' k := h
theorem gran_ne_alloc : bandOf ALLOC ∉ ({bGran} : Finset ℕ) := by_decide
theorem band9_not {r : ℕ} (h1 : 90000 ≤ r) (h2 : r < 100000) : ¬ bandOf r ∉ ({bGran} : Finset ℕ) := by
  unfold bandOf bGran; simp; omega
variable {P : Polygon} {W : ℕ} (c : Config)
theorem pre_exec (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W ztkri c c' k ∧ k = 2 ∧
      c'.nreg 90019 = 1 ∧ c'.nreg 90010 = c.nmem (c.nreg 90001) ∧
      (∀ r, r ≠ 90019 → r ≠ 90010 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · zugkh
  · refine ztfkc <;>
      zusb
theorem empty_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W emptyS c c' k ∧ k = 2 ∧
      c'.nreg 90095 = 0 ∧ c'.nreg 90028 = 0 ∧
      (∀ r, r ≠ 90095 → r ≠ 90028 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold emptyS
  exec_block
  · omega
  · omega
  · refine ztfkc <;>
      zusb
theorem granular_empty {M : Model} {F : Set ztf} {γ : ℕ} (hF : F = ∅)
    (h : M.Semigranular F γ) : M.Granular F γ := by
  zulov
  have : Merge.ContractionCondIn M.D M.weight F γ := by
    zumlt
    zung
    have := hc.1
    zvoij at this
    zufep
  zufep
set_option maxHeartbeats 4000000 in
/-- **WP-F: granularity enforcement**, from the construction of normal forms and the
decomposition. -/
theorem granularize (hB : BuildNFSpec) (hD : DecompSpec) : GranularizeSpec := by
  obtain ⟨sB, κB, hsB⟩ := buildOK_of hB
  obtain ⟨sD, κD, hsD⟩ := decompOK_of hD
  refine ⟨granStmt sB sD, κGran κB κD, ?_⟩
  intro P W c hw ⟨hG, hWh, hD1, hwf, M, N, hMD, hGM, hNW, hNF, hdeg, hsemi⟩ hroom
  zubmr
  have e0 : rd c bGran 0 = c.nreg 90000 := rfl
  have e1 : rd c bGran 1 = c.nreg 90001 := rfl
  have e2 : rd c bGran 2 = c.nreg 90002 := rfl
  have e3 : rd c bGran 3 = c.nreg 90003 := rfl
  zvokq at hwf hMD
  zuelk

  zvnak at hsemi
  zuguf
  set MD := c.nreg 90000 with hMDd
  set NFH := c.nreg 90001 with hNFHd
  set D := c.nreg 90002 with hDd
  set γ := c.nreg 90003 with hγd
  zucvx

  set X := K * ztho + 1 with hXd
  zukav
  have hκ : 12 + κB + κD * ztef ≤ κGran κB κD D := by
    unfold κGran; nlinarith
  have hκX : κGran κB κD D ≤ κGran κB κD D * X := Nat.le_mul_of_pos_right _ hX1
  -- the post-condition, from the result of `bdStmt`
  have post : ∀ (c' : Config) (L : List zte) (N' : NF),
      lset M zta L ⊆ N.F M zta → M.DegLe ztxef D →
      M.Granular ztxef γ → c.nreg ALLOC ≤ c'.nreg 90004 →
      NFWithin c'.nmem ztvgq ztdo N' → IsNF M zta N' →
      N'.F M zta = lset M zta L → IsDecomp N' zttiy →
      ∀ M₀ N₀, ModelDescAt c.nmem MD zta M₀ → NFAt c.nmem NFH N₀ →
        ∃ N'', c.nreg ALLOC ≤ rd c' bGran 4 ∧
          NFWithin c'.nmem ztcoh ztdo N'' ∧
          N''.F M₀ zta ⊆ N₀.F M₀ zta ∧ IsCanonicalNF M₀ zta N'' γ D := by
    intro c' L N' hsub hdg hgr hA hW hN hF hdec M₀ N₀ hM₀ hN₀
    have := NFLoc.modelDesc_unique hMD hM₀
    zumo
    have hch := NFLoc.nfAt_chords_eq hNW.nfAt hN₀
    refine ⟨N', hA, hW, ?_, hN, ?_, ?_, hdec⟩
    · rw [F_congr hch, hF]; exact hsub
    · zvoij; exact hdg
    · zvoij; exact hgr
  obtain ⟨c₁, k₁, e₁, hk₁, p19, p10, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    pre_exec (P := P) c hw (le_trans ztdmm hWh)
  zud
  zuhdp
  have F₁ : Frame {bGran} c c₁ k₁ := frame_of (fun r hr => R₁ r
    ztesm ztesm)
    rr₁ m₁ rm₁ o₁ gran_ne_alloc
  rw [← hNFHd, hK] at p10
  have q0 : c₁.nreg 90000 = MD := R₁ _ by_decide by_decide
  have q1 : c₁.nreg 90001 = NFH := R₁ _ by_decide by_decide
  have q2 : c₁.nreg 90002 = D := R₁ _ by_decide by_decide
  have q3 : c₁.nreg 90003 = γ := R₁ _ by_decide by_decide
  rcases Nat.lt_or_ge K 1 with hK0 | hK1
  · -- no chords
    have hnil : N.chords = [] :=
      List.eq_nil_of_length_eq_zero (by have h' : N.chords.length = K := rfl; omega)
    have hFe : N.F M zta = ∅ := by
      ext x; simp [NF.F, hnil]
    have hl : lset M zta [] = N.F M zta := by
      rw [hFe]; ext x; simp [lset]
    obtain ⟨c₂, k₂, e₂, hk₂, s95, s28, R₂, rr₂, m₂, rm₂, o₂⟩ := empty_exec (P := P) c₁ w₁
    have F₂ : Frame {bGran} c₁ c₂ k₂ := frame_of (fun r hr => R₂ r
      ztesm ztesm)
      rr₂ m₂ rm₂ o₂ gran_ne_alloc
    have A₂ : ztbae := by rw [R₂ _ by_decide by_decide, A₁]
    have hm₂ : ztckc := by rw [m₂, m₁]
    obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hA', hW', hN', hF', hdec'⟩, F₃⟩ := bd_exec (L := []) hsB hsD
      e₂.wb_right hG hWh (by rw [R₂ _ by_decide by_decide, q0])
      (by rw [R₂ _ by_decide by_decide, q2]) s28 s95 (by rw [A₂, hm₂]; exact hwf)
      (by zundq; exact hMD) hGM (fun i hi => by simp at hi) (by rw [A₂]; simp)
      ⟨by rw [show {c | ∃ x ∈ ([] : List zte), c = (recOf x).toSet M zta} =
          N.F M zta from hl]; exact hNF.1, List.nodup_nil, fun x hx => by simp at hx,
        fun x hx => by simp at hx⟩
      ztmdr
      (by rw [A₂]; unfold costBD; simp; omega)
    have e₁₂ : Exec P W ztjdd c₁ c₂ ztcaj :=
      .ifLtN_true ztlih e₂
    refine ztgor
    · unfold costBD at hk₃; simp at hk₃; omega
    · rw [A₂] at hA'
      exact post c₃ [] N' (by zvnen) ztmdr
        (by zvnen; exact granular_empty hFe hsemi) hA' hW' hN' hF' hdec'
    · exact ((F₁.trans (F₂.mono ztbhw (by omega : k₂ ≤ k₂ + 1))).trans F₃).mono
        by_decide by_omega
  · -- the worklist
    have hne : ztxml :=
      ⟨cs M zta N 0, mem_F_iff.2 ⟨0, by_omega, rfl⟩⟩
    have hWA := walkAx_of_goodModel hGM
    have hAr := arcs_le hNF hWA hne
    have hRr := nRegions_eq hNF hWA
    have hct := cost_total (κB := κB) (κD := κD) (D := D) hAr hRr (le_refl K)
    rw [← hXd] at hct
    obtain ⟨c₂, k₂, L, e₂, hk₂, s00, s02, s95, hLK, hlist, hLB, hok, hsub, hdg, hgr, G₂⟩ :=
      main_exec (P := P) w₁ q0 q1 q2 q3 hG hWh (by zuolg; exact hwf)
        (by zvmxn; exact hMD) hGM (by zuolg; exact hNW) hNF hne hdeg hsemi
        (by rw [A₁]; nlinarith)
    have hmono : costBD κB κD D L.length ≤ costBD κB κD D K := costBD_mono hLK
    have A₂ := G₂.2.2.2.2.2.2
    have hlow : ztux := fun a ha => by
      rw [G₂.2.2.1 a by_omega, m₁]
    obtain ⟨hMD₂, hwf₂⟩ := desc_agree' hwf hMD hlow
    obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hA', hW', hN', hF', hdec'⟩, F₃⟩ := bd_exec hsB hsD
      e₂.wb_right hG hWh s00 s02 rfl s95 (hwf₂.mono (by zuosb; exact G₂.2.2.2.2.2.1))
      hMD₂ hGM hlist hLB hok hdg (by rw [A₁] at A₂; nlinarith)
    have e₁₂ : Exec P W ztjdd c₁ c₂ ztoci :=
      .ifLtN_false ztlih e₂
    have hA₂ : zteia := by zuosb; exact G₂.2.2.2.2.2.1
    refine ztgor
    · omega
    · exact post c₃ L N' hsub hdg hgr (le_trans hA₂ hA') hW' hN' hF' hdec'
    · have F₂ : Frame granBands c₁ c₂ k₂ := GF.frame G₂
      exact ((F₁.trans (F₂.mono ztbhw (by omega : k₂ ≤ k₂ + 2))).trans F₃).mono
        by_decide by_omega

/-- **WP-F: granularity enforcement**, from the construction of normal forms alone. -/
theorem granularize' (hB : BuildNFSpec) : GranularizeSpec := granularize hB DecR.decomp
end
end Gran
namespace MergeAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def setF : Stmt := block [.copyN 70000 100000, .copyN 70001 100001, .copyN 70002 100002,
  .copyN 70003 100003, .copyN 70004 100004, .copyN 70005 100005, .copyN 70006 100007,
  .copyN 70008 100009]

/-- A model descriptor of the whole chain at the allocator. -/
def descS : Stmt := block [.constN 100020 1, .constN 100021 5, .copyN 100010 ALLOC,
  .constN 100011 0, .storeN 100010 100011, .copyN 100012 100002, .addN 100013 100010 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014, .addN 100012 100012 100020,
  .addN 100013 100013 100020,
  .loadN 100014 100012, .storeN 100013 100014,
  .constN 100015 6, .addN ALLOC ALLOC 100015]

/-- Initialisation of the maximum-degree loop (normal form at `70007`). -/
def mdInit : Stmt := block [.constN 100035 2, .addN 100036 70007 100035, .loadN 100034 100036,
  .constN 100035 5, .addN 100036 70007 100035, .loadN 100031 100036,
  .constN 100035 2, .addN 100031 100031 100035, .constN 100030 0, .constN 100032 0]

/-- One step of the maximum-degree loop. -/
def mdBody : Stmt :=
  .seq (block [.loadN 100033 100031])
    (.seq (.ifLtN 100032 100033 ztoyk .skip)
      (block [.addN 100031 100031 100021, .addN 100030 100030 100020]))

/-- The maximum-degree loop. -/
def mdLoop : Stmt := .whileLtN 100030 100034 mdBody

/-- `γ_R = min γ₀ (2 m) + 1` in `100045`. -/
def gamS : Stmt :=
  .seq (block [.copyN 100040 100005, .constN 100041 2, .addN 100041 100002 100041,
      .loadN 100042 100041, .addN 100043 100042 100042])
    (.seq (.ifLtN 100040 100043 (block [.copyN 100045 100040]) (block [.copyN 100045 100043]))
      ztnry)

/-- The arguments of restoration. -/
def setR : Stmt := block [.copyN 80000 100010, .copyN 80001 70007, .copyN 80002 100032,
  .copyN 80003 100007, .copyN 80004 100045, .copyN 80006 100009]

/-- The arguments of granularity enforcement. -/
def setG : Stmt := block [.copyN 90000 100010, .copyN 90001 80005, .copyN 90002 100007,
  .copyN 90003 100006]

/-- The output. -/
def outS : Stmt := block [.copyN 100008 90004]

/-- **The merge** (Lemma 3.5): fuse, restore conformality, restore granularity. -/
def mergeMk (fMk : Stmt → Stmt) (rMk : Stmt → Stmt → Stmt) (gS : Stmt) (sh cu : Stmt) : Stmt :=
  .seq setF (.seq (fMk sh) (.seq descS (.seq mdInit (.seq mdLoop (.seq gamS (.seq setR
    (.seq (rMk sh cu) (.seq setG (.seq gS outS)))))))))

/-! ## Register-only blocks -/

/-- A band predicate. -/
def inBand (b : ℕ) (r : ℕ) : Bool := decide (bandOf r = b)
theorem wr_setF : wr ztvwz setF = true := by_decide
theorem wr_setR : wr ztvxb setR = true := by_decide
theorem wr_setG : wr ztvxa setG = true := by_decide
theorem wr_mdInit : wr ztjyv mdInit = true := by_decide
theorem wr_mdLoop : wr ztjyv mdLoop = true := by_decide
theorem wr_gamS : wr ztjyv gamS = true := by_decide
variable {P : Polygon} {W : ℕ} (c : Config)
theorem setF_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setF c c' k ∧ k = 8 ∧
      rd c' bFuse 0 = rd c bMerge 0 ∧ rd c' bFuse 1 = rd c bMerge 1 ∧
      rd c' bFuse 2 = rd c bMerge 2 ∧ rd c' bFuse 3 = rd c bMerge 3 ∧
      rd c' bFuse 4 = rd c bMerge 4 ∧ rd c' bFuse 5 = rd c bMerge 5 ∧
      rd c' bFuse 6 = rd c bMerge 7 ∧ rd c' bFuse 8 = rd c bMerge 9 ∧
      FrameB ztvwz c c' := by
  have ztdqk : ∃ c' k, Exec P W setF c c' k ∧ k = 8 ∧
      (rd c' bFuse 0 = rd c bMerge 0 ∧ rd c' bFuse 1 = rd c bMerge 1 ∧
      rd c' bFuse 2 = rd c bMerge 2 ∧ rd c' bFuse 3 = rd c bMerge 3 ∧
      rd c' bFuse 4 = rd c bMerge 4 ∧ rd c' bFuse 5 = rd c bMerge 5 ∧
      rd c' bFuse 6 = rd c bMerge 7 ∧ rd c' bFuse 8 = rd c bMerge 9) := by
    unfold setF
    exec_block
    tauto
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, exec_frameB e wr_setF⟩
theorem setR_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setR c c' k ∧ k = 6 ∧
      rd c' bRestore 0 = c.nreg 100010 ∧ rd c' bRestore 1 = rd c bFuse 7 ∧
      rd c' bRestore 2 = c.nreg 100032 ∧ rd c' bRestore 3 = rd c bMerge 7 ∧
      rd c' bRestore 4 = c.nreg 100045 ∧ rd c' bRestore 6 = rd c bMerge 9 ∧
      FrameB ztvxb c c' := by
  have ztdqk : ∃ c' k, Exec P W setR c c' k ∧ k = 6 ∧
      (rd c' bRestore 0 = c.nreg 100010 ∧ rd c' bRestore 1 = rd c bFuse 7 ∧
      rd c' bRestore 2 = c.nreg 100032 ∧ rd c' bRestore 3 = rd c bMerge 7 ∧
      rd c' bRestore 4 = c.nreg 100045 ∧ rd c' bRestore 6 = rd c bMerge 9) := by
    unfold setR
    exec_block
    tauto
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    exec_frameB e wr_setR⟩
theorem setG_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setG c c' k ∧ k = 4 ∧
      rd c' bGran 0 = c.nreg 100010 ∧ rd c' bGran 1 = rd c bRestore 5 ∧
      rd c' bGran 2 = rd c bMerge 7 ∧ rd c' bGran 3 = rd c bMerge 6 ∧
      FrameB ztvxa c c' := by
  have ztdqk : ∃ c' k, Exec P W setG c c' k ∧ k = 4 ∧
      (rd c' bGran 0 = c.nreg 100010 ∧ rd c' bGran 1 = rd c bRestore 5 ∧
      rd c' bGran 2 = rd c bMerge 7 ∧ rd c' bGran 3 = rd c bMerge 6) := by
    unfold setG
    exec_block
    tauto
  exact ⟨c', k, e, hk, h.1, h.2.1, h.2.2.1, h.2.2.2, exec_frameB e wr_setG⟩
theorem outS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W outS c c' k ∧ k = 1 ∧ rd c' bMerge 8 = rd c bGran 4 ∧
      FrameB (fun r => r == 100008) c c' := by
  have ztdqk : ∃ c' k, Exec P W outS c c' k ∧ k = 1 ∧
      rd c' bMerge 8 = rd c bGran 4 := by
    zumtv
    exec_block
    tauto
  exact ⟨c', k, e, hk, h, exec_frameB e by_decide⟩

/-! ## `γ_R` -/
theorem gamS_exec (hw : WordsBounded W c)
    (h20 : c.nreg 100020 = 1) {g m : ℕ} (hg : rd c bMerge 5 = g)
    (hm : c.nmem ztilx = m) (hgW : g + 1 ≤ W) (hmW : 2 * m ≤ W)
    (h2W : rd c bMerge 2 + 2 ≤ W) :
    ∃ c' k, Exec P W gamS c c' k ∧ k ≤ 9 ∧ c'.nreg 100045 = min g ztdk + 1 ∧
      FrameB ztjyv c c' ∧ (∀ r, r < 100040 → c'.nreg r = c.nreg r) := by
  have hg' : c.nreg 100005 = g := hg
  have hm' : c.nmem (c.nreg 100002 + 2) = m := hm
  have h2W' : c.nreg 100002 + 2 ≤ W := h2W
  obtain ⟨c₁, k₁, e₁, hk₁, v40, v43, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 100040 100005,
      .constN 100041 2, .addN 100041 100002 100041, .loadN 100042 100041,
      .addN 100043 100042 100042]) c c₁ k₁ ∧
      k₁ = 5 ∧ c₁.nreg 100040 = g ∧ c₁.nreg 100043 = 2 * m ∧
      ∀ r, r < 100040 → c₁.nreg r = c.nreg r := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hg', hm']; omega)
    refine ⟨rfl, ?_, ?_, fun r hr => ?_⟩
    · simp_all
    · simp (disch := omega) only [Machine.upd_same,
        hm']
      ring
    · zup
  zuka
  have tail : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 100045 = min g ztdk →
      c₂.nreg 100020 = 1 → ∃ c₃, Exec P W ztnry c₂ c₃ 1 ∧
        c₃.nreg 100045 = min g ztdk + 1 ∧ ∀ r, r ≠ 100045 → c₃.nreg r = c₂.nreg r :=
    fun c₂ hw₂ h45 h20' => by
      have e := Exec.addN (P := P) hw₂ 100045 100045 100020 (by
        omega)
      exact ⟨_, .seq e ztmac, by_simp_all,
        fun r hr => by_simp_all⟩
  by_cases hlt : c₁.nreg 100040 < c₁.nreg 100043
  · have e₂ := Exec.copyN (P := P) hw₁ 100045 100040
    obtain ⟨c₃, e₃, v₃, r₃⟩ := tail _ e₂.wb_right (by
        zumwv; omega)
      (by zunvu
          grind)
    have ex : Exec P W gamS c c₃ (k₁ + (ztceh + 1 + 1)) :=
      .seq e₁ (.seq (.ifLtN_true hlt ztxug) e₃)
    zucza

  · have e₂ := Exec.copyN (P := P) hw₁ 100045 100043
    obtain ⟨c₃, e₃, v₃, r₃⟩ := tail _ e₂.wb_right (by
        zumwv; omega)
      (by zunvu
          grind)
    have ex : Exec P W gamS c c₃ (k₁ + (ztceh + 2 + 1)) :=
      .seq e₁ (.seq (.ifLtN_false hlt ztxug) e₃)
    zucza
set_option maxHeartbeats 4000000 in
theorem descS_exec (hw : WordsBounded W c) {A bw : ℕ}
    (hA : c.nreg ALLOC = A) (hbw : c.nreg 100002 = bw) (hbA : bw + 5 ≤ A) (hAW : A + 6 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 27 ∧ c'.nreg 100010 = A ∧ c'.nreg ALLOC = A + 6 ∧
      c'.nreg 100020 = 1 ∧ c'.nreg 100021 = 5 ∧
      c'.nmem A = 0 ∧ ztxsm ∧
      ztfjc ∧
      (∀ r, ztofh → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descS
  zufth
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', hbw, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl⟩
  · tauto
  · zudvw
  · rfl
  · rfl
  · simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hA', hbw, ALLOC]
  · interval_cases j <;>
      simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hA', hbw, ALLOC, add_zero]
  · zudvv
  · zujym
    zup

/-! ## The maximum-degree loop -/
theorem mdInit_exec (hw : WordsBounded W c) {H : ℕ}
    (hH : rd c bFuse 7 = H) (hHW : H + 5 ≤ W) (hbW : c.nmem ztwj + 2 ≤ W) :
    ∃ c' k, Exec P W mdInit c c' k ∧ k = 10 ∧ c'.nreg 100034 = c.nmem ztfnq ∧
      c'.nreg 100031 = c.nmem ztwj + 2 ∧ c'.nreg 100030 = 0 ∧ c'.nreg 100032 = 0 ∧
      c'.nmem = c.nmem ∧ ztiuu ∧
      FrameB ztjyv c c' := by
  have hH' : c.nreg 70007 = H := hH
  obtain ⟨c', k, e, hk, q⟩ : ∃ c' k, Exec P W mdInit c c' k ∧ k = 10 ∧
      (c'.nreg 100034 = c.nmem ztfnq ∧ c'.nreg 100031 = c.nmem ztwj + 2 ∧
      c'.nreg 100030 = 0 ∧ c'.nreg 100032 = 0 ∧ c'.nmem = c.nmem ∧
      ztiuu) := by
    unfold mdInit
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hH']; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun r hr => ?_⟩
    · simp_all
    · simp_all
    · simp
    · simp
    · zup
  exact ⟨c', k, e, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2,
    exec_frameB e wr_mdInit⟩

/-- One step of the maximum-degree loop. -/
theorem mdBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h20 : c.nreg 100020 = 1) (h21 : c.nreg 100021 = 5) (hp : c.nreg 100031 + 5 ≤ W)
    (hi : c.nreg 100030 + 1 ≤ W) :
    ∃ c' k, Exec P W mdBody c c' k ∧ k ≤ 5 ∧
      c'.nreg 100032 = max ztvhe ztbage ∧
      c'.nreg 100031 = c.nreg 100031 + 5 ∧ c'.nreg 100030 = c.nreg 100030 + 1 ∧
      c'.nmem = c.nmem ∧
      ztegp := by
  have e₁ := Exec.loadN (P := P) hw 100033 100031
  set c₁ : Config := { c with nreg := upd c.nreg 100033 (c.nmem (c.nreg 100031)) } with hc₁
  have hw₁ : ztidr := e₁.wb_right
  have q₁ : ∀ r, r ≠ 100033 → c₁.nreg r = c.nreg r := fun r hr => by
    simp_all
  have v₁ : c₁.nreg 100033 = c.nmem ztmfl := by_rfl
  -- the maximum
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, q₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 100032 100033
      ztoyk .skip) c₁ c₂ k₂ ∧ k₂ ≤ 2 ∧
      c₂.nreg 100032 = max ztvhe ztbage ∧
      (∀ r, r ≠ 100032 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
    by_cases hlt : c₁.nreg 100032 < c₁.nreg 100033
    · have e := Exec.copyN (P := P) hw₁ 100032 100033
      refine ⟨_, _, .ifLtN_true hlt (.seq e ztmac), by_omega, ?_, fun r hr => ?_, rfl⟩
      · zumb
      simp_all
    · refine ⟨_, _, .ifLtN_false hlt ztekd, le_rfl, ?_, fun r _ => rfl, rfl⟩
      simp_all
  obtain ⟨q₂, m₂⟩ := q₂
  zuja
  have e₃ := Exec.addN (P := P) hw₂ 100031 100031 100021 (by
    simp_all)
  have e₄ := Exec.addN (P := P) e₃.wb_right 100030 100030 100020 (by
    simp_all)
  have ex : Exec P W mdBody c _ (ztceh + (k₂ + ztzsk)) :=
    .seq ztzsa (.seq e₂ (.seq e₃ (.seq e₄ ztuvm)))
  refine ⟨_, _, ex, by_omega, ?_, ?_, ?_, ?_, fun r a b d f => ?_⟩
  · simp_all
  · simp_all
  · simp_all
  · omega
  simp_all

/-- **The maximum-degree loop.** -/
theorem mdLoop_exec {P : Polygon} {W : ℕ} {R base Cap : ℕ} {L : ℕ → ℕ}
    (hWb : base + 5 * R ≤ W) (hRW : R + 1 ≤ W) (hCap : ∀ r, r < R → L r ≤ Cap) :
    ∀ (n : ℕ) (c : Config), WordsBounded W c → c.nreg 100020 = 1 → c.nreg 100021 = 5 →
      c.nreg 100034 = R → (∀ r, r < R → c.nmem (base + 5 * r) = L r) →
      c.nreg 100030 + n = R → c.nreg 100031 = base + 5 * c.nreg 100030 →
      c.nreg 100032 ≤ Cap → (∀ r, r < c.nreg 100030 → L r ≤ c.nreg 100032) →
      ∃ c' k, Exec P W mdLoop c c' k ∧ k ≤ 7 * n + 2 ∧ (∀ r, r < R → L r ≤ c'.nreg 100032) ∧
        c'.nreg 100032 ≤ Cap ∧ c'.nmem = c.nmem ∧
        ztegp
  | 0, c, hw, _, _, h34, _, hn, _, hc, hle => by
    refine ⟨c, 2, .whileLtN_false by_omega hw, by_omega,
      fun r hr => hle r by_omega, hc, rfl, fun _ _ _ _ _ => rfl⟩
  | n + 1, c, hw, h20, h21, h34, hL, hn, hp, hc, hle => by
    have hi : c.nreg 100030 < R := by_omega
    obtain ⟨c₁, k₁, e₁, hk₁, v32, v31, v30, m₁, q₁⟩ := mdBody_exec (P := P) c hw h20 h21
      by_omega by_omega
    have hLi : c.nmem ztmfl = L (c.nreg 100030) := by_simp_all
    obtain ⟨c', k₂, e₂, hk₂, hall, hcap, m₂, q₂⟩ := mdLoop_exec hWb hRW hCap n c₁ e₁.wb_right
      by_simp_all
      by_simp_all
      by_simp_all
      ztcvp by_omega
      by_omega
      by_simp_all
      (fun r hr => by
        grind)
    refine ⟨c', _, .whileLtN_true by_omega e₁ e₂, by_omega, hall, hcap,
      by grind, fun r a b d f => by_grind⟩
variable {m m' : ℕ → ℕ}
theorem hostAt_agree {h E : ℕ} {H : Host} (hH : HostAt m h H)
    (hE : h + 3 * H.length + 4 ≤ E) (he : ∀ a, a < E → m' a = m a) : HostAt m' h H := by
  zugpa

  have := h1 i hi
  revert this
  cases H.getD i ztmn with
  | run a l =>
    zufq

  | pt x =>
    cases x with
    | vtx j => intro h; simp only at h ⊢; zundt; exact h
    | onEdge e j =>
      zufq

/-- **Copying a chain descriptor** (host layout below `E`, the five words copied to `d`). -/
theorem chainDescAt_copy {bw d E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' ztfqu = m ztctz) :
    ChainDescAt m' d Q H C := by
  zumm

  refine ⟨?_, h1, by_omega, by_omega, by_omega,
    by simp_all⟩
  zuhkr

/-- **A well-formed copy of a chain descriptor.** -/
theorem chainWF_copy {m m' : ℕ → ℕ} {bw d E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' ztfqu = m ztctz)
    (hd : d + 5 ≤ E') (hEE : E ≤ E') : ChainWF P E' m' d := by
  zuhi

  zubvz

/-- **The copied model descriptor**: `m' A = 0` and the five words of the chain descriptor at
`bw` copied to `A + 1` describe the chain model and are well formed below any `E' ≥ A + 6`. -/
theorem modelDesc_copy {m m' : ℕ → ℕ} {bw A E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C) (hEA : E ≤ A)
    (he : ∀ a, a < E → m' a = m a) (h0 : m' A = 0)
    (hc : ∀ j, j < 5 → m' ztcsp = m ztctz) (hE' : A + 6 ≤ E') :
    ModelDescAt m' A zta ztc ∧ ModelDescWF P E' m' A := by
  zuta
  refine ⟨Or.inl ⟨h0, H, C, chainDescAt_copy hC hEb he hc, rfl⟩, by_omega, fun _ => ?_⟩
  exact chainWF_copy hwf hC he hc by_omega by_omega

/-- **The model descriptor survives** a change of the memory at or above `E` (for a descriptor
of a chain model built as above). -/
theorem modelDesc_agree {m m' : ℕ → ℕ} {A E : ℕ} {H : Host} {C : Chain}
    (hwf : ModelDescWF P E m A) (h0 : m A = 0) (hC : ChainDescAt m ztbo zta H C)
    (he : ∀ a, a < E → m' a = m a) :
    ModelDescAt m' A zta ztc ∧ ModelDescWF P E m' A ∧
      ChainDescAt m' ztbo zta H C ∧ m' A = 0 := by
  have hcw : ChainWF P E m ztbo := hwf.2 h0
  zubks
  have hA6 := hwf.1
  have hc : ∀ j, j < 5 → m' ztcsp = m ztcsp := fun j hj => he _ by_omega
  zudye
  have h0' : m' A = 0 := by_grind
  exact ⟨Or.inl ztfwl, ⟨hA6, fun _ => chainWF_copy hcw hC he hc by_omega le_rfl⟩,
    hC', h0'⟩

/-- The number of edges of a chain with a well-formed descriptor: `2 m + 2 ≤ 128 n`. -/
theorem chain_m_le {E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C) : 2 * C.m + 2 ≤ 128 * P.n := by
  zucxs

  zusu
  have h2 : ztehu := by
    rw [hC.2.1, ← hQ]; zunoo
  have h3 := Host.pts_length_le hHW
  have h4 : ztgak := Nat.mul_le_mul_right _ hl
  omega
