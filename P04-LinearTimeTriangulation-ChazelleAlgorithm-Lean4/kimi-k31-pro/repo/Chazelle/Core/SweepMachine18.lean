module

public import Chazelle.Core.SweepMachine17
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# The sweep (WP-D), part 34: the abstract machine, events at the left split vertex

In the left case G the stretch of `C` corresponding to `C₁` passes the top of `C₁` once (walk corner
`tour(2m₁-1) → top₁ → tour(1)`, at offset `lL1` of the stretch: the *split vertex*), while the walk
of `C₁` passes it twice around its slit (the corners `slitTop → top₁ → tour(1)` at walk vertex `6`
and `tour(2m₁-1) → top₁ → slitTop` at walk vertex `2m₁+6`).  `attach_iff` excludes this position;
here:

* `top_corner_sub`: both slit corners of `C₁` are contained in the corner of `C` (`SideGood`);
* `sideLeft_top_first`, `sideLeft_top_last`, `sideLeft_split`: the three sectors;
* `attach_split_of_left`, `attach_split_of_arrival` (**soundness**): a detection hit arriving at
  either copy of the top of `C₁` gives a piece attached at the split vertex of `C`;
* `genuine_of_split` (**completeness**): a shot of `C` hitting the top of `C₁` is genuine in the
  model of `C₁` and arrives at the copy `2m₁+6` (shot to the east, `σ = 1`) or `6` (to the west).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw sideCross sideDot)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

/-- **The slit corners are inside the corner without the slit**: the left sectors of the walk of a
chain at the two copies of its top vertex are contained in the left sector of the corner
`tour(2m-1) → top → tour(1)`. -/
theorem top_corner_sub (C : Chain) (hP : C.P.Simple) (x : Point) :
    (sideLeftOf C.slitTop C.top (C.sideTour C.sideBeta 1) x →
      sideLeftOf (C.sideTour C.sideBeta (2 * C.m - 1)) C.top (C.sideTour C.sideBeta 1) x) ∧
    (sideLeftOf (C.sideTour C.sideBeta (2 * C.m - 1)) C.top C.slitTop x →
      sideLeftOf (C.sideTour C.sideBeta (2 * C.m - 1)) C.top (C.sideTour C.sideBeta 1) x) := by
  set β := C.sideBeta
  have hN0  := sub_ne_zero.2 (C.sideTour_one_ne_top hP β)
  have hP0  := sub_ne_zero.2 (C.sideTour_last_ne_top hP β)
  have hU0  := sub_ne_zero.2 C.sideSlitTop_ne_top
  unfold sideLeftOf
  by_cases hT : C.topIdx = 0 ∨ C.topIdx = C.m
  · rw [← C.sideTour_one_eq_last β hT]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine Or.inr (Or.inr (Or.inr ⟨Chazelle.Chain.sideCross_self _,
        Chazelle.Chain.sideDot_self_pos hN0, ?_⟩))
      by_contra hc
      push Not at hc
      exact Chazelle.Chain.sideCcw_not_ray_left hN0 hc.1 hc.2 h
    · refine Or.inr (Or.inr (Or.inr ⟨Chazelle.Chain.sideCross_self _,
        Chazelle.Chain.sideDot_self_pos hN0, ?_⟩))
      by_contra hc
      push Not at hc
      refine Chazelle.Chain.sideCcw_not_ray_right hN0 ?_ ?_ h
      · rw [Chazelle.Chain.sideCross_swap, hc.1, neg_zero]
      · rw [Chazelle.Chain.sideDot_comm]; exact hc.2
  · have hmain : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
        (C.sideTour β (2 * C.m - 1) - C.top) := by
      rcases C.sideGood_sideBeta hP with h | h | h
      · exact absurd (Or.inl h) hT
      · exact absurd (Or.inr h) hT
      · exact h
    exact ⟨fun h => Chazelle.Chain.sideCcw_sub_left hN0 hmain h,
      fun h => Chazelle.Chain.sideCcw_sub_right hN0 hU0 hP0 hmain h⟩

/-- The left sector at the first copy of the top (walk vertex `6`). -/
theorem sideLeft_top_first (C : Chain) (x : Point) :
    sideLeft (chainModel C).W 6 0 x ↔ sideLeftOf C.slitTop C.top (C.sideTour C.sideBeta 1) x := by
  have hm := C.two_m_pos
  rw [Chazelle.Chain.sideLeft_zero, cm_W, C.sideWalk_n]
  have h1 : (6 + (2 * C.m + 7) - 1) % (2 * C.m + 7) = 5 := by
    rw [show 6 + (2 * C.m + 7) - 1 = 5 + (2 * C.m + 7) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have h2 : (6 + 1) % (2 * C.m + 7) = 1 + 6 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, C.sideWalk_vtx_five, C.sideWalk_vtx_six, C.sideWalk_vtx_tour _ (by omega)]

/-- The left sector at the last copy of the top (walk vertex `2m+6`). -/
theorem sideLeft_top_last (C : Chain) (x : Point) :
    sideLeft (chainModel C).W (2 * C.m + 6) 0 x ↔
      sideLeftOf (C.sideTour C.sideBeta (2 * C.m - 1)) C.top C.slitTop x := by
  have hm := C.two_m_pos
  rw [Chazelle.Chain.sideLeft_zero, cm_W, C.sideWalk_n]
  have h1 : (2 * C.m + 6 + (2 * C.m + 7) - 1) % (2 * C.m + 7) = (2 * C.m - 1) + 6 := by
    rw [show 2 * C.m + 6 + (2 * C.m + 7) - 1 = ((2 * C.m - 1) + 6) + (2 * C.m + 7) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h2 : (2 * C.m + 6 + 1) % (2 * C.m + 7) = 0 := by
    rw [show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]
  rw [h1, h2, C.sideWalk_vtx_tour _ (show 2 * C.m - 1 ≤ 2 * C.m by omega),
    C.sideWalk_vtx_tour _ (le_refl (2 * C.m)), C.sideTour_two_m, C.sideWalk_vtx_zero]

/-- The two copies of the top in the walk of a chain are at the top. -/
theorem sidePt_top_copies (C : Chain) :
    sidePt (chainModel C).W 6 0 = C.top ∧ sidePt (chainModel C).W (2 * C.m + 6) 0 = C.top := by
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, cm_W, C.sideWalk_vtx_six,
    C.sideWalk_vtx_tour _ (le_refl (2 * C.m)), C.sideTour_two_m]
  exact ⟨rfl, rfl⟩

section Split

variable (J : Merge.Junction)

/-- The split vertex of `C` is the top of `C₁` (`sidePt_splitL` without `TopStrict`). -/
theorem sidePt_splitL0 (hP : J.P.Simple) {S₁ : Set (Set Point)}
    (hS₁ : S₁ ⊆ Merge.augChords J.left) (hS₁f : S₁.Finite) (hlt : lL1 J < lL1 J + lL2 J) :
    sidePt (chainModel J.whole).W
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J) % (chainModel J.whole).W.n) 0 = J.left.top := by
  have hC := corr_left0 J hP hS₁ hS₁f
  have hδ : 0 < lδ J := by
    by_contra h0
    have := hC.hδ (by omega)
    omega
  rw [Chazelle.Chain.sidePt_zero]
  have := hC.A2 0 (Nat.zero_le _)
  rw [add_zero, add_zero] at this
  rw [this, show 6 + tpos J.left J.m₁ + lL1 J + lδ J = 6 + tpos J.left J.m₁ + (lL1 J + lδ J) by ring]
  exact left_split_top J hδ

/-- Case G of the left correspondence (a nonempty second piece). -/
theorem left_caseG (hlt : lL1 J < lL1 J + lL2 J) :
    lL1 J = 2 * J.left.m - tpos J.left J.m₁ ∧ lδ J = 7 ∧ 0 < tpos J.left J.m₁ ∧
      tpos J.left J.m₁ < 2 * J.left.m := by
  have := tpos_lt J.left J.m₁
  have hm1 : J.left.m = J.m₁ := rfl
  unfold lL1 lL2 lδ at *
  split_ifs at hlt ⊢ <;> omega

/-- **The left sector at the split vertex** is the corner `tour(2m₁-1) → top₁ → tour(1)` of `C₁`. -/
theorem sideLeft_split (hP : J.P.Simple) (hlt : lL1 J < lL1 J + lL2 J)
    (x : Point) :
    sideLeft (chainModel J.whole).W
        ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J) % (chainModel J.whole).W.n) 0 x ↔
      sideLeftOf (J.left.sideTour J.left.sideBeta (2 * J.left.m - 1)) J.left.top
        (J.left.sideTour J.left.sideBeta 1) x := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  obtain ⟨hL1, hδ, hτ0, hτ⟩ := left_caseG J hlt
  have hm := J.left.two_m_pos
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm1 : J.left.m = J.m₁ := rfl
  rw [Chazelle.Chain.sideLeft_zero, mod_pred_mod hC.n_pos _ (d := lL1 J) (by omega),
    mod_succ_mod]
  have hprev := hC.A1 (lL1 J - 1) (by omega)
  have hcur := hC.A1 (lL1 J) le_rfl
  have hnext : (chainModel J.whole).W.vtx
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + (lL1 J + 1)) % (chainModel J.whole).W.n) =
      (chainModel J.left).W.vtx ((6 + tpos J.left J.m₁ + lL1 J + lδ J + 1) %
        (chainModel J.left).W.n) := by
    have := hC.A2 1 (by omega)
    rwa [Nat.add_assoc (6 + tpos J.whole (J.m₁ + 2 * J.m₂)) (lL1 J) 1] at this
  rw [hprev, hcur, hnext]
  have e1 : (6 + tpos J.left J.m₁ + (lL1 J - 1)) % (chainModel J.left).W.n =
      (2 * J.left.m - 1) + 6 := by
    rwo [hn₁, Nat.mod_eq_of_lt (by omega)]
  have e2 : (6 + tpos J.left J.m₁ + lL1 J) % (chainModel J.left).W.n = 2 * J.left.m + 6 := by
    rwo [hn₁, Nat.mod_eq_of_lt (by omega)]
  have e3 : (6 + tpos J.left J.m₁ + lL1 J + lδ J + 1) % (chainModel J.left).W.n = 1 + 6 := by
    rw [hn₁, show 6 + tpos J.left J.m₁ + lL1 J + lδ J + 1 = (1 + 6) + (2 * J.left.m + 7) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2, e3, cm_W, J.left.sideWalk_vtx_tour _ (show 2 * J.left.m - 1 ≤ 2 * J.left.m by omega),
    J.left.sideWalk_vtx_tour _ (le_refl (2 * J.left.m)), J.left.sideTour_two_m,
    J.left.sideWalk_vtx_tour _ (show 1 ≤ 2 * J.left.m by omega)]

/-- An attachment is transported along an inclusion of left sectors at the same point. -/
theorem attach_of_sector {W W' : Polygon} {c : Set Point} {p p' : ℕ}
    (hA : SideAttach W c p 0) (hp' : p' < W'.n) (hpt : sidePt W' p' 0 = sidePt W p 0)
    (hsec : ∀ x, sideLeft W p 0 x → sideLeft W' p' 0 x) : SideAttach W' c p' 0 := by
  obtain ⟨-, -, -, hw, r, hr, hl⟩ := hA
  refine ⟨hp', le_rfl, zero_lt_one, by rwx [hpt], r, hr, fun x hx hxw hxd => ?_⟩
  exact hsec x (hl x hx (by rwa [hpt] at hxw) (by rwa [hpt] at hxd))

/-- **An attachment at either copy of the top of `C₁` gives an attachment at the split vertex.** -/
theorem attach_split_of_left (hP : J.P.Simple) 
    (hlt : lL1 J < lL1 J + lL2 J) {c : Set Point} {k : ℕ} (hk : k = 6 ∨ k = 2 * J.left.m + 6)
    (hA : SideAttach (chainModel J.left).W c k 0) :
    SideAttach (chainModel J.whole).W c
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J) % (chainModel J.whole).W.n) 0 := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hsplit := sidePt_splitL0 J hP (S₁ := ∅) (empty_subset _) finite_empty hlt
  obtain ⟨h6, h2m⟩ := sidePt_top_copies J.left
  refine attach_of_sector hA (Nat.mod_lt _ hC.n_pos) ?_ fun x hx => ?_
  · rw [hsplit]; rcases hk with rfl | rfl
    · exact h6.symm
    · exact h2m.symm
  · rw [sideLeft_split J hP hlt]
    rcases hk with rfl | rfl
    · exact (top_corner_sub J.left (show J.left.P.Simple from hP) x).1
        ((sideLeft_top_first J.left x).1 hx)
    · exact (top_corner_sub J.left (show J.left.P.Simple from hP) x).2
        ((sideLeft_top_last J.left x).1 hx)

/-- **Soundness at the split vertex**: a detection hit arriving at a copy of the top of `C₁` gives
the piece attached at the split vertex of `C`. -/
theorem attach_split_of_arrival (hP : J.P.Simple) 
    (hlt : lL1 J < lL1 J + lL2 J) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ)
    {k : ℕ} (hk : k = 6 ∨ k = 2 * J.left.m + 6)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ k 0) :
    SideAttach (chainModel J.whole).W (Chazelle.segment a (rayPt a σ τ))
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J) % (chainModel J.whole).W.n) 0 :=
  attach_split_of_left J hP hlt hk (attach_left_of_arrival hσ hτ hA)

/-- **Completeness at the split vertex**: a shot of `C` (free, from a point not above the top of
`C₁`) whose first hit is the top of `C₁` is genuine in the model of `C₁`, arriving at the copy
`2m₁+6` of the top when shot to the east and at the copy `6` when shot to the west. -/
theorem genuine_of_split (hP : J.P.Simple) {a : Point}
    (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ)
    (hend : rayPt a σ (J.whole.hitParam a σ) = J.left.top) :
    Genuine J.left a σ (J.whole.hitParam a σ) ∧
      (σ = 1 → Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
        (2 * J.left.m + 6) 0) ∧
      (σ = -1 → Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ 6 0) := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hM₁  := hC.hM₂
  have hPl  := hP
  set T := J.whole.hitParam a σ with hT
  have hz'  := ha₁.trans J.left_top_le
  obtain ⟨hT0, -, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  obtain ⟨h6, h2m⟩ := sidePt_top_copies J.left
  have hn₁  := cm_n J.left
  have hm := J.left.two_m_pos
  have hNb : (J.left.sideTour J.left.sideBeta 1).2 ≤ J.left.top.2 :=
    J.left.vertex_snd_le_top (J.left.sideIdx_le _ _)
  have hPb : (J.left.sideTour J.left.sideBeta (2 * J.left.m - 1)).2 ≤ J.left.top.2 :=
    J.left.vertex_snd_le_top (J.left.sideIdx_le _ _)
  have hPne := J.left.sideTour_last_ne_top hPl J.left.sideBeta
  have hNne := J.left.sideTour_one_ne_top hPl J.left.sideBeta
  have hW1 : (J.left.sideWalk J.left.sideBeta).vtx (2 * J.left.m - 1 + 6) =
      J.left.sideTour J.left.sideBeta (2 * J.left.m - 1) := J.left.sideWalk_vtx_tour _ (by omega)
  have hW2 : (J.left.sideWalk J.left.sideBeta).vtx ((2 * J.left.m - 1 + 6 + 1) %
      (J.left.sideWalk J.left.sideBeta).n) = J.left.top := by
    rw [J.left.sideWalk_n, show 2 * J.left.m - 1 + 6 + 1 = 2 * J.left.m + 6 by omega,
      Nat.mod_eq_of_lt (by omega), J.left.sideWalk_vtx_tour _ le_rfl, J.left.sideTour_two_m]
  have hW6 : (J.left.sideWalk J.left.sideBeta).vtx (0 + 6) = J.left.top := by
    rw [zero_add]; exact J.left.sideWalk_vtx_six _
  have hW7 : (J.left.sideWalk J.left.sideBeta).vtx ((0 + 6 + 1) %
      (J.left.sideWalk J.left.sideBeta).n) = J.left.sideTour J.left.sideBeta 1 := by
    rw [J.left.sideWalk_n, show 0 + 6 + 1 = 1 + 6 by omega, Nat.mod_eq_of_lt (by omega),
      J.left.sideWalk_vtx_tour _ (by omega)]
  have hya : a.2 = J.left.top.2 := by
    have := congrArg Prod.snd hend; simpa [rayPt] using this
  have hxa : a.1 + σ * T = J.left.top.1 := by
    have := congrArg Prod.fst hend; simpa [rayPt] using this
  -- the neighbours of the top do not lie on the ray before it (the ray is in the domain there)
  have hPw : σ = 1 → ¬ ((J.left.sideTour J.left.sideBeta (2 * J.left.m - 1)).2 = J.left.top.2 ∧
      (J.left.sideTour J.left.sideBeta (2 * J.left.m - 1)).1 ≤ J.left.top.1) := by
    rintro rfl ⟨h1, h2⟩
    set P := J.left.sideTour J.left.sideBeta (2 * J.left.m - 1) with hPdef
    have hlt : P.1 < J.left.top.1 := lt_of_le_of_ne h2 (fun h => hPne (Prod.ext h h1))
    set d := J.left.top.1 - P.1 with hd
    have hd0 : 0 < d := by rwli [hd]
    set ε := min T d / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min hT0 hd0)
    have hεT : ε < T := by rw [hε]; linarith [min_le_left T d]
    have hεd : ε < d := by rw [hε]; linarith [min_le_right T d]
    have hin := hdom (T - ε) (by linarith) (by linarith)
    have hu0 : 0 ≤ 1 - ε / d := by rwli [sub_nonneg, div_le_one hd0]
    have hu1 : 1 - ε / d < 1 := by have := div_pos hε0 hd0; linarith
    have hm := J.left.sideWalk_tour_pt_mem J.left.sideBeta (i := 2 * J.left.m - 1) (by omega)
      (fun h => by omega) hu0 hu1
    unfold sidePt at hm
    rw [hW1, hW2] at hm
    have heq : rayPt a 1 (T - ε) = Geometry.lerp P J.left.top (1 - ε / d) := by
      ext
      · simp only [rayPt_fst, Geometry.lerp_fst]
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hd0.ne']; rwli [hd] at *
      · simp only [rayPt_snd, Geometry.lerp_snd]; rwring [h1, hya]
    rw [← heq] at hm
    exact J.whole.not_mem_set_of_mem_dom hin (J.left_set_subset hm)
  have hNe : σ = -1 → ¬ ((J.left.sideTour J.left.sideBeta 1).2 = J.left.top.2 ∧
      J.left.top.1 ≤ (J.left.sideTour J.left.sideBeta 1).1) := by
    rintro rfl ⟨h1, h2⟩
    set N := J.left.sideTour J.left.sideBeta 1 with hNdef
    have hlt : J.left.top.1 < N.1 := lt_of_le_of_ne h2 (fun h => hNne (Prod.ext h.symm h1))
    set d := N.1 - J.left.top.1 with hd
    have hd0 : 0 < d := by rwli [hd]
    set ε := min T d / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min hT0 hd0)
    have hεT : ε < T := by rw [hε]; linarith [min_le_left T d]
    have hεd : ε < d := by rw [hε]; linarith [min_le_right T d]
    have hin := hdom (T - ε) (by linarith) (by linarith)
    have hu0  := (div_pos hε0 hd0).le
    have hu1 : ε / d < 1 := by rw [div_lt_one hd0]; exact hεd
    have hm := J.left.sideWalk_tour_pt_mem J.left.sideBeta (i := 0) (by omega)
      (fun h => by omega) hu0 hu1
    unfold sidePt at hm
    rw [hW6, hW7] at hm
    have heq : rayPt a (-1) (T - ε) = Geometry.lerp J.left.top N (ε / d) := by
      ext
      · simp only [rayPt_fst, Geometry.lerp_fst]
        rwli [div_mul_cancel₀ _ hd0.ne']
      · simp only [rayPt_snd, Geometry.lerp_snd]; rwring [h1, hya]
    rw [← heq] at hm
    exact J.whole.not_mem_set_of_mem_dom hin (J.left_set_subset hm)
  set N := J.left.sideTour J.left.sideBeta 1
  set P := J.left.sideTour J.left.sideBeta (2 * J.left.m - 1)
  set t := J.left.top with ht
  have hU1 : (J.left.slitTop - t).1 = 0 := by simp [Chazelle.Chain.slitTop, t]
  have hU2 : 0 < (J.left.slitTop - t).2 := by
    simp only [Chazelle.Chain.slitTop, Prod.snd_sub, t]; linarith [J.left.top_snd_lt_radius]
  have hsub : ∀ s : ℝ, rayPt t s 1 - t = ((s, 0) : Point) := by
    intro s; ext <;> simp [rayPt]
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J (hdom s h0 h1) (by simpa [rayPt] using ha₁), ?_⟩, ?_, ?_⟩
  · rw [hend, ← h6]
    exact hM₁.trace 6 (by omega) 0 le_rfl zero_le_one
  · rintro rfl
    refine ⟨by omega, le_rfl, zero_lt_one, by rwx [hend], ?_⟩
    rw [hend, sideLeft_top_last, ← ht]
    unfold sideLeftOf
    rw [hsub]
    refine Chazelle.Chain.sideCcw_west hU1 hU2 rfl (by norm_num)
      (by sil only [Prod.snd_sub]) (sub_ne_zero.2 (J.left.sideTour_last_ne_top hPl _))
      ?_
    unfold sideCross sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; rintro ⟨h1, h2⟩
    exact hPw rfl ⟨by linarith, by linarith⟩
  · rintro rfl
    refine ⟨by omega, le_rfl, zero_lt_one, by rwx [hend], ?_⟩
    rw [hend, sideLeft_top_first, ← ht]
    unfold sideLeftOf
    rw [show -(-1 : ℝ) = 1 by norm_num, hsub]
    refine Chazelle.Chain.sideCcw_east hU1 hU2 rfl one_pos
      (by sil only [Prod.snd_sub]) (sub_ne_zero.2 (J.left.sideTour_one_ne_top hPl _)) ?_
    unfold sideCross sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; rintro ⟨h1, h2⟩
    exact hNe rfl ⟨by linarith, by linarith⟩

end Split

end Sweep

end

end Chazelle.Core
