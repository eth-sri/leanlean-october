module
public import Chazelle.Core.ModelAccess
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence
public import Chazelle.Programs.Verification

public import Chazelle.Core.DownPhaseTransSide
public import Chazelle.Core.DownPhaseArcT
public import Chazelle.Core.DownPhaseExtractGeom

/-!
# WP-M (T, part 6): the transition weight `2γ + 1`

With the inner-side shift `c₀` of the top chain (`exists_shift`), the keys `x ∈ [0, m]` of the
interior walk correspond to the chain keys `x + c₀`: the points, the left sectors and the offsets
agree (`pt_eq`, `sec_eq`), so `ArcT.ArcCorr` holds with `κ x = x + c₀` (`transCorr`).  A chain
chord attached on the inner side has its piece attached at the same interior position
(`piece_of_attach`).

**(T3)** Every arc of a region `V ⊆ U` of the pieces has weight at most `2 · weight U + 1`
(`arcWt_le_trans`): its keys in `[0, m]` form at most two straight pieces, each transferred by
`ArcT.arcWt_le`, and the rest lies on the last edge `e_{n-1}`.
-/

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
  vtx : ∀ j, j ≤ C.m → (C.sideWalk C.sideBeta).vtx (j + c₀) = (interiorWalk Q).vtx j

variable {c₀ : ℕ}

theorem chain_n : (chainModel C).W.n = 2 * C.m + 7 := Chain.sideWalk_n _ _

theorem Shift.next_chain (_H : Shift Q C c₀) {j : ℕ} (hj : j < C.m) (h6 : c₀ + C.m ≤ 2 * C.m + 6) :
    (j + c₀ + 1) % (C.sideWalk C.sideBeta).n = (j + 1) + c₀ := by
  block_post [Chain.sideWalk_n, Nat.mod_eq_of_lt]

theorem Shift.prev_chain (_H : Shift Q C c₀) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ C.m) :
    (j + c₀ + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = (j - 1) + c₀ := by
  have := _H.le
  rw [Chain.sideWalk_n, show j + c₀ + (2 * C.m + 7) - 1 = (j - 1 + c₀) + (2 * C.m + 7) by omega,
    Nat.add_mod_right, guarded Nat.mod_eq_of_lt]

theorem next_W (T : Top Q C) {j : ℕ} (hj : j < C.m) :
    (j + 1) % (interiorWalk Q).n = j + 1 := by
  rw [iw_n, Nat.mod_eq_of_lt (by have := T.hm; omega)]

theorem prev_W (T : Top Q C) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ C.m) :
    (j + (interiorWalk Q).n - 1) % (interiorWalk Q).n = j - 1 := by
  have := T.hm
  rw [iw_n, show j + Q.n - 1 = (j - 1) + Q.n by omega, Nat.add_mod_right,
    guarded Nat.mod_eq_of_lt]

/-- **The points agree.** -/
theorem Shift.pt_eq (H : Shift Q C c₀) (T : Top Q C) {j : ℕ} (hj : j < C.m) (s : ℝ) :
    sidePt (C.sideWalk C.sideBeta) (j + c₀) s = sidePt (interiorWalk Q) j s := by
  unfold sidePt
  rw_facts [H.next_chain hj H.le, next_W T, H.vtx j hj.le, H.vtx (j + 1)]

/-- **The left sectors agree.** -/
theorem Shift.sec_eq (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) {j : ℕ} (hj : j < C.m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hsj : s = 0 → 1 ≤ j) (y : Point) :
    sideLeft (C.sideWalk C.sideBeta) (j + c₀) s y ↔ sideLeft (interiorWalk Q) j s y := by
  have hjn : j < (interiorWalk Q).n := by rw [iw_n]; have := T.hm; omega
  rcases hs0.lt_or_eq with hs | hs
  · have hne2 : (interiorWalk Q).vtx j ≠ Chain.sideNext (interiorWalk Q) j :=
      (walkAx_interiorModel hQ).nd j hjn
    have hne1 : (C.sideWalk C.sideBeta).vtx (j + c₀) ≠
        (C.sideWalk C.sideBeta).vtx ((j + c₀ + 1) % (C.sideWalk C.sideBeta).n) := by
      rwa [H.next_chain hj H.le, H.vtx j hj.le, H.vtx (j + 1) hj, ← next_W T hj]
    rw [Chazelle.Chain.sideLeft_edge hne1 ⟨hs, hs1⟩, Chazelle.Chain.sideLeft_edge hne2 ⟨hs, hs1⟩,
      H.next_chain hj H.le, H.vtx j hj.le, H.vtx (j + 1) hj, next_W T hj]
  · subst hs
    have hj1 := hsj rfl
    rw_facts [Chazelle.Chain.sideLeft_zero, Chazelle.Chain.sideLeft_zero, H.prev_chain hj1 hj.le, H.next_chain hj H.le, prev_W T hj1 hj.le, next_W T, H.vtx j hj.le, H.vtx (j + 1), at_index H.vtx (j - 1)]

/-- **The piece of an attached chord is attached.** -/
theorem piece_of_attach (hQ : Q.Simple) (T : Top Q C) {F₀ : Set (Set Point)}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {c : Set Point} (hc : c ∈ F₀) {j : ℕ} {s : ℝ}
    (hA : SideAttach (interiorWalk Q) c j s)
    (hP : sidePt (interiorWalk Q) j s ∉ C.dom) :
    ∃ d ∈ pieces Q F₀, SideAttach (interiorWalk Q) d j s := by
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  obtain ⟨hp, hs0, hs1, hmem, r, hr, hnear⟩ := hA
  obtain ⟨r', hr', hclean⟩ := from_facts FactsInterior.clean
  set P := sidePt (interiorWalk Q) j s with hPdef
  obtain ⟨y, a, b, hch, -, rfl⟩ := hF₀ hc
  have hdom := T.interior_sub_dom hQ
  -- points of the chord near `P` are interior
  have hin : ∀ x ∈ hseg y a b, x ≠ P → dist x P < min r r' → x ∈ Q.filled \ Q.boundary := by
    intro x hx hne hd
    by_contra hxD
    exact hclean x (lt_of_lt_of_le hd (min_le_right _ _)) (by rwa [hWb, hWf]) (hnear x hx hne (lt_of_lt_of_le hd (min_le_left _ _)))
  obtain ⟨hPy, hPa, hPb⟩ := hmem
  have hPab : P.1 = a ∨ P.1 = b := by
    by_contra h; push Not at h
    exact hP (by
      grind [Prod.ext, hch.open_mem])
  have hab := hch.lt
  have hdist : ∀ t : ℝ, dist ((t, y) : Point) P = |t - P.1| := by
    intro t
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hPy, sub_self, abs_zero]
    exact max_eq_left (abs_nonneg _)
  set δ := min (min r r') (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < min r r' := by have := min_le_left (min r r') (b - a); linarith
  have hδ2 : δ < b - a := by have := min_le_right (min r r') (b - a); rw [hδ]; linarith
  have hPne : ∀ t : ℝ, t ≠ P.1 → ((t, y) : Point) ≠ P := fun t ht e => ht (by rw [← e])
  rcases hPab with hPa' | hPb'
  · -- `P` is the left end
    have hz := hin (a + δ, y) ⟨rfl, by linarith, by linarith⟩ (hPne _ (by linarith))
      (by rw_facts [hdist, hPa', show a + δ - a = δ by ring, abs_of_pos]; exact hδ1)
    obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord ⟨by linarith, by linarith⟩
      (fun h => hch.left_not (hdom h)) (fun h => hch.right_not (hdom h)) hz hQ
    have ha'a : a' = a := by
      by_contra hne
      have hlt := lt_of_le_of_ne ha' (Ne.symm hne)
      exact hch'.left_not (hin (a', y) ⟨rfl, ha', by linarith⟩ (hPne _ (by linarith))
        (by rw [hdist, hPa', abs_of_pos (by linarith)]; linarith))
    subst ha'a
    refine ⟨hseg y a' b', ⟨⟨y, a', b', hch', rfl⟩, hseg y a' b, hc, fun q hq =>
      ⟨hq.1, hq.2.1, by linarith [hq.2.2]⟩⟩,
      hp, hs0, hs1, ⟨hPy, by linarith, by linarith⟩, r, hr, fun x hx hne hd =>
      hnear x ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩ hne hd⟩
  · -- `P` is the right end
    have hz := hin (b - δ, y) ⟨rfl, by linarith, by linarith⟩ (hPne _ (by linarith))
      (by rw_facts [hdist, hPb', show b - δ - b = -δ by ring, abs_neg, abs_of_pos]; exact hδ1)
    obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord ⟨by linarith, by linarith⟩
      (fun h => hch.left_not (hdom h)) (fun h => hch.right_not (hdom h)) hz hQ
    have hb'b : b' = b := by
      by_contra hne
      have hlt := lt_of_le_of_ne hb' hne
      exact hch'.right_not (hin (b', y) ⟨rfl, by linarith, hb'⟩ (hPne _ (by linarith))
        (by rw [hdist, hPb', abs_of_neg (by linarith)]; linarith))
    subst hb'b
    refine ⟨hseg y a' b', ⟨⟨y, a', b', hch', rfl⟩, hseg y a b', hc, fun q hq =>
      ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩⟩,
      hp, hs0, hs1, ⟨hPy, by linarith, by linarith⟩, r, hr, fun x hx hne hd =>
      hnear x ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩ hne hd⟩

theorem wrapK_self {n x : ℝ} (hx : x < n) : wrapK n x = x := by unfold wrapK; simp_all

/-- **The key correspondence of the transition.** -/
theorem transCorr (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set (Set Point)} (hF₀ : F₀ ⊆ (chainModel C).Adm) {U V : Set Point} (hVU : V ⊆ U) :
    ArcT.ArcCorr (chainModel C) (interiorModel Q) F₀ (pieces Q F₀) U V 0 C.m
      (fun x => x + c₀) := by
  have hM₁ := walkAx_chainModel hP
  have hmn := T.hm
  have hWn : (Q.interiorModel).W.n = Q.n := iw_n
  have hle := H.le
  have hsix := H.six
  -- the position of a key of `(0, m)`
  have hpos : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) C.m → ⌊x⌋₊ < C.m ∧ 0 ≤ x - ⌊x⌋₊ ∧ x - ⌊x⌋₊ < 1 ∧
      ⌊x + c₀⌋₊ = ⌊x⌋₊ + c₀ ∧ x + c₀ - ⌊x + c₀⌋₊ = x - ⌊x⌋₊ := by
    intro x hx
    have hfl : ⌊x + c₀⌋₊ = ⌊x⌋₊ + c₀ := by
      simp [Nat.floor_add_natCast hx.1.le]
    refine ⟨?_, sub_nonneg.2 (Nat.floor_le hx.1.le), by linarith [Nat.lt_floor_add_one x], hfl, ?_⟩
    · have : (⌊x⌋₊ : ℝ) < C.m := lt_of_le_of_lt (Nat.floor_le hx.1.le) hx.2
      exact_mod_cast this
    · rw [hfl]; push_cast; ring
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWn]; exact_mod_cast T.n_pos
  · rw [hWn, zero_add]; exact_mod_cast (show C.m ≤ Q.n by omega)
  · intro x _ y _ hxy; simp only; linarith
  · intro x hx
    refine ⟨add_nonneg hx.1 (Nat.cast_nonneg _), ?_⟩
    rw [chain_n]
    have : (x : ℝ) + c₀ ≤ C.m + c₀ := by linarith [hx.2]
    have h2 : ((C.m + c₀ : ℕ) : ℝ) < ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    push_cast at h2 ⊢; linarith
  · intro y h1 h2
    refine ⟨y - c₀, ⟨by grind, by linarith⟩, by ring⟩
  · intro x hx hv k hk
    have hkc : c₀ ≤ k := by
      have : (c₀ : ℝ) < k := by rw [← hk]; linarith [hx.1]
      exact_mod_cast this.le
    exact hv (k - c₀) (by push_cast [hkc]; linarith)
  · intro x hx hnv hnv'
    simp [NonVtx] at hnv
    obtain ⟨k, hk⟩ := hnv
    exact hnv' (k + c₀) (by rw [hk]; push_cast; ring)
  · -- cuts
    rintro x hx ⟨c, hc, p₁, t₁, hA₁, he⟩
    obtain ⟨hjm, ht0, ht1, hfl, hfr⟩ := hpos x hx
    set j := ⌊x⌋₊ with hj
    set s := x - j with hs
    have hkey : ((p₁ : ℕ) : ℝ) + t₁ = ((j + c₀ : ℕ) : ℝ) + s := by
      rw [← he, hs]; push_cast; ring
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA₁.2.1 hA₁.2.2.1 ht0 ht1 hkey
    have hsj : s = 0 → 1 ≤ j := by
      intro h0
      by_contra hj0; push Not at hj0
      have : j = 0 := by omega
      have hx0 : x = 0 := by rw [hs, this] at h0; simpa using h0
      exact lt_irrefl _ (hx0 ▸ hx.1)
    have hA₂ : SideAttach (interiorWalk Q) c j s :=
      ExtG.attach_of_sector (H.pt_eq T hjm s).symm
        (fun y hy => (H.sec_eq T hQ hjm ht0 ht1 hsj y).1 hy)
        (by rw [iw_n]; omega) ht0 ht1 hA₁
    have hPd : sidePt (interiorWalk Q) j s ∉ C.dom := by
      rw_facts [← H.pt_eq]
      exact hM₁.trace (j + c₀) (by rw [chain_n]; omega) s ht0 ht1.le
    obtain ⟨d, hd, hAd⟩ := piece_of_attach hQ T hF₀ hc hA₂ hPd
    have hxn : x < (Q.interiorModel.W.n : ℝ) := by
      rw [hWn]
      have : ((C.m : ℕ) : ℝ) < ((Q.n : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith [hx.2]
    refine ⟨d, hd, j, s, hAd, ?_⟩
    rw_facts [wrapK_self, hs]; ring
  · -- faces
    intro x hx _ hfa
    obtain ⟨hjm, ht0, ht1, hfl, hfr⟩ := hpos x hx
    have hxn : x < (Q.interiorModel.W.n : ℝ) := by
      rw [hWn]
      have : ((C.m : ℕ) : ℝ) < ((Q.n : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith [hx.2]
    rw_facts [wrapK_self] at hfa
    rw [hfr, hfl]
    refine ExtG.faces_of_offset (c := 1) one_pos (fun δ => ?_) hVU hfa
    simp
    show Chazelle.Jordan.offset ((C.sideWalk C.sideBeta).vtx (⌊x⌋₊ + c₀))
      ((C.sideWalk C.sideBeta).vtx ((⌊x⌋₊ + c₀ + 1) % (C.sideWalk C.sideBeta).n)) _ δ =
      Chazelle.Jordan.offset ((interiorWalk Q).vtx ⌊x⌋₊)
        ((interiorWalk Q).vtx ((⌊x⌋₊ + 1) % (interiorWalk Q).n)) _ δ
    rw [H.next_chain hjm H.le, next_W T hjm, H.vtx _ hjm.le, H.vtx _ hjm]
  · -- counted
    intro x hx _
    obtain ⟨hjm, -, -, hfl, -⟩ := hpos x hx
    rw [hfl]
    show 6 ≤ ⌊x⌋₊ + c₀ ∧ ⌊x⌋₊ + c₀ < 2 * C.m + 6
    omega

/-- **A straight piece of an arc** inside `[0, m]` weighs at most the weight of `U`. -/
theorem piece_wt (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set (Set Point)} (hF₀ : F₀ ⊆ (chainModel C).Adm) (hfin : F₀.Finite)
    {U V : Set Point} (hU : U ∈ (chainModel C).regions F₀) (hVU : V ⊆ U) {a b a' b' : ℝ}
    (harc : (interiorModel Q).IsArc (pieces Q F₀) V a b) (h0 : 0 ≤ a') (hab' : a' < b')
    (hm : b' ≤ C.m) (hsub : ∀ x, a' < x → x < b' → sideInArc a b x) :
    (interiorModel Q).arcWt a' b' ≤ (chainModel C).weight F₀ U := by
  have hWn : Q.interiorModel.W.n = Q.n := iw_n
  have hmn : (C.m : ℝ) < Q.n := by exact_mod_cast (show C.m < Q.n by have := T.hm; omega)
  have hplain : ∀ x, sideInArc a' b' x ↔ a' < x ∧ x < b' := fun x => by
    grind [sideInArc]
  refine ArcT.arcWt_le (walkAx_chainModel hP) hF₀ hfin hU (from_facts transCorr)
    (aa := a') (bb := b') h0 hab' hm ?_ ?_ ?_ ?_
  · intro x _ hxn hx
    exact ⟨x, (hplain x).1 hx, wrapK_self hxn⟩
  · grind [wrapK_self]
  · intro x hx
    exact harc.2.2.2.2.2.1 x (hsub x ((hplain x).1 hx).1 ((hplain x).1 hx).2)
  · intro p t hp ht0 ht1 hx
    exact harc.2.2.2.2.2.2 p t hp ht0 ht1 (hsub _ ((hplain _).1 hx).1 ((hplain _).1 hx).2)

/-- The keys after `m` meet only the last walk edge. -/
theorem arcWt_last (T : Top Q C) : (interiorModel Q).arcWt C.m 0 ≤ 1 := by
  have hWn : Q.interiorModel.W.n = Q.n := iw_n
  rw [BoxT.arcWt_eq']
  calc (BoxT.edgesIn Q.interiorModel C.m 0).ncard ≤ ({C.m} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton _)
        rintro p ⟨hp, -, t, ht0, ht1, hx⟩
        rw [hWn] at hp
        unfold sideInArc at hx
        rw [guarded ite_eq_right] at hx
        have h1 : (C.m : ℝ) < p + 1 := by
          rcases hx with h | h <;> linarith
        have h2 : C.m < p + 1 := by exact_mod_cast h1
        have := T.hm
        show p = C.m
        omega
    _ = 1 := Set.ncard_singleton _

/-- **(T3) The weight of an arc after the transition** is at most `2 · weight U + 1`. -/
theorem arcWt_le_trans (H : Shift Q C c₀) (T : Top Q C) (hQ : Q.Simple) (hP : C.P.Simple)
    {F₀ : Set (Set Point)} (hF₀ : F₀ ⊆ (chainModel C).Adm) (hfin : F₀.Finite)
    {U V : Set Point} (hU : U ∈ (chainModel C).regions F₀) (hVU : V ⊆ U) {a b : ℝ}
    (harc : (interiorModel Q).IsArc (pieces Q F₀) V a b) :
    (interiorModel Q).arcWt a b ≤ 2 * (chainModel C).weight F₀ U + 1 := by
  set w := C.chainModel.weight F₀ U
  have ha0 : 0 ≤ a := harc.1
  have hb0 : 0 ≤ b := harc.2.2.1
  have hm0 : (0 : ℝ) ≤ C.m := Nat.cast_nonneg _
  have hlast := arcWt_last T
  have pw := fun {a' b' : ℝ} (h0 : 0 ≤ a') (hab' : a' < b') (hm : b' ≤ C.m)
      (hsub : ∀ x > a', x < b' → sideInArc a b x) =>
    from_facts piece_wt
  -- membership in the last edge interval
  have hlastI : ∀ x : ℝ, (C.m : ℝ) < x → sideInArc (C.m : ℝ) 0 x := fun x hx => by
    unfold sideInArc; simp_all
  by_cases hab : a < b
  · have hin : ∀ x, sideInArc a b x ↔ a < x ∧ x < b := fun x => by
      grind [sideInArc]
    by_cases ham : a < C.m
    · -- the piece `(a, min b m)` and the last edge
      have hbm : a < min b C.m := lt_min hab ham
      have h1 := pw ha0 hbm (min_le_right _ _) (fun x h1 h2 =>
        (hin x).2 ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩)
      have hadd := BoxT.arcWt_le_add (M := Q.interiorModel) (a := a) (b := b) (a₁ := a)
        (b₁ := min b C.m) (a₂ := C.m) (b₂ := 0) (fun p _ t _ _ hx => by
          rw [hin] at hx
          by_cases hxm : (p : ℝ) + t < C.m
          · grind [sideInArc]
          · right
            push Not at hxm
            rcases hxm.lt_or_eq with h | h
            · exact hlastI _ h
            · exfalso
              -- a vertex key is not of the form `p + t` with `0 < t < 1`
              have e : (p : ℝ) < C.m := by linarith
              have e' : (C.m : ℝ) < p + 1 := by linarith
              have e1 : p < C.m := by exact_mod_cast e
              have e2 : C.m < p + 1 := by exact_mod_cast e'
              omega)
      omega
    · -- the arc lies on the last edge
      push Not at ham
      have := BoxT.arcWt_le_of_sub (M := Q.interiorModel) (a := a) (b := b) (a' := C.m) (b' := 0)
        (fun p _ t _ _ hx => by
          grind)
      omega
  · -- the arc wraps around: keys above `a` or below `b`
    have hin : ∀ x, sideInArc a b x ↔ a < x ∨ x < b := fun x => by
      grind [sideInArc]
    set b' := min b (C.m : ℝ) with hb'
    have hb'0 : 0 ≤ b' := le_min hb0 hm0
    have hb'm : b' ≤ C.m := min_le_right _ _
    have hK : ∀ x, sideInArc (C.m : ℝ) b' x ↔ (C.m : ℝ) < x ∨ x < b' := fun x => by
      grind [sideInArc]
    -- the wrap-around interval `(m, b')` weighs at most `w + 1`
    have hKw : Q.interiorModel.arcWt (C.m : ℝ) b' ≤ w + 1 := by
      rcases hb'0.lt_or_eq with hpos | hzero
      · have h2 := pw le_rfl hpos hb'm (fun x _ h2 =>
          (hin x).2 (Or.inr (lt_of_lt_of_le h2 (min_le_left _ _))))
        have hadd := BoxT.arcWt_le_add (M := Q.interiorModel) (a := (C.m : ℝ)) (b := b')
          (a₁ := C.m) (b₁ := 0) (a₂ := 0) (b₂ := b') (fun p _ t ht0 _ hx => by
            grind [sideInArc, Nat.cast_nonneg])
        omega
      · grind
    by_cases ham : a < C.m
    · have h1 := pw ha0 ham le_rfl (fun x h1 _ => (hin x).2 (Or.inl h1))
      have hadd := BoxT.arcWt_le_add (M := Q.interiorModel) (a := a) (b := b) (a₁ := a)
        (b₁ := C.m) (a₂ := C.m) (b₂ := b') (fun p _ t ht0 ht1 hx => by
          rw [hin] at hx
          have hne : (p : ℝ) + t ≠ C.m := fun h => by
            have e : (p : ℝ) < C.m := by linarith
            have e' : (C.m : ℝ) < p + 1 := by linarith
            have e1 : p < C.m := by exact_mod_cast e
            have e2 : C.m < p + 1 := by exact_mod_cast e'
            omega
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · grind [sideInArc]
          all_goals grind)
      omega
    · push Not at ham
      have := BoxT.arcWt_le_of_sub (M := Q.interiorModel) (a := a) (b := b) (a' := C.m) (b' := b')
        (fun p _ t ht0 ht1 hx => by
          rw [hin] at hx
          rcases hx with hx | hx
          · grind
          · have hne : (p : ℝ) + t ≠ C.m := fun h => by
              have e : (p : ℝ) < C.m := by linarith
              have e' : (C.m : ℝ) < p + 1 := by linarith
              have e1 : p < C.m := by exact_mod_cast e
              have e2 : C.m < p + 1 := by exact_mod_cast e'
              omega
            rcases lt_or_gt_of_ne hne with hlt | hgt
            all_goals grind)
      omega

end

end Trans

end Chazelle.Core
