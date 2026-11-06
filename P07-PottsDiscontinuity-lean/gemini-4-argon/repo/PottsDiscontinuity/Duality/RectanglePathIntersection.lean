module

public import PottsDiscontinuity.Duality.RectangleDualCrossing

@[expose] public section

open Set Topology Filter unitInterval PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

namespace PottsDiscontinuity.FK.Curves

noncomputable section

private def unitClamp (x : ℝ) : ℝ := max 0 (min 1 x)

private lemma unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma unitClamp_of_nonpos {x : ℝ} (hx : x ≤ 0) : unitClamp x = 0 := by
  simp [unitClamp, min_eq_right (hx.trans zero_le_one), max_eq_left hx]

private lemma unitClamp_of_one_le {x : ℝ} (hx : 1 ≤ x) : unitClamp x = 1 := by
  simp [unitClamp, min_eq_left hx]

private lemma unitClamp_sub_le (a b : ℝ) : unitClamp a - unitClamp b ≤ |a - b| := by
  unfold unitClamp
  rcases le_total 0 (min 1 a) with ha | ha <;> rcases le_total 0 (min 1 b) with hb | hb <;>
    rcases le_total 1 a with ha1 | ha1 <;> rcases le_total 1 b with hb1 | hb1 <;>
    linarith [max_eq_left ha, max_eq_right ha, max_eq_left hb, max_eq_right hb,
      min_eq_left ha1, min_eq_right ha1, min_eq_left hb1, min_eq_right hb1,
      le_abs_self (a - b), abs_nonneg (a - b)]

private lemma dist_unitClamp_le (x y : ℝ) : dist (unitClamp x) (unitClamp y) ≤ dist x y := by
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  exact ⟨by linarith [unitClamp_sub_le y x, abs_sub_comm x y], unitClamp_sub_le x y⟩

private def gridPt (n : ℕ) (z : ℤ × ℤ) : I × I :=
  (⟨unitClamp (z.1 / (n + 1 : ℝ)), unitClamp_mem _⟩,
   ⟨unitClamp (z.2 / (n + 1 : ℝ)), unitClamp_mem _⟩)

private lemma dist_gridPt_le (n : ℕ) (z w : ℤ × ℤ)
    (h1 : |z.1 - w.1| ≤ 1) (h2 : |z.2 - w.2| ≤ 1) :
    dist (gridPt n z) (gridPt n w) ≤ 1 / (n + 1 : ℝ) := by
  have hcoord (a b : ℤ) (hab : |a - b| ≤ 1) :
      dist (unitClamp (a / (n + 1 : ℝ))) (unitClamp (b / (n + 1 : ℝ))) ≤ 1 / (n + 1 : ℝ) := by
    refine (dist_unitClamp_le _ _).trans ?_
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    gcongr
    exact_mod_cast hab
  exact max_le (hcoord z.1 w.1 h1) (hcoord z.2 w.2 h2)

private lemma walk_sign_change {V : Type*} (G : SimpleGraph V) (g : V → ℝ) {b t : V}
    (W : G.Walk b t) (hb : g b ≤ 0) (ht : 0 ≤ g t) :
    b = t ∨ ∃ u v, G.Adj u v ∧ g u ≤ 0 ∧ 0 ≤ g v := by
  induction W with
  | nil => exact Or.inl rfl
  | @cons u w t hadj W' ih =>
    by_cases hw : 0 ≤ g w
    · exact Or.inr ⟨u, w, hadj, hb, hw⟩
    · rcases ih (le_of_not_ge hw) ht with rfl | h
      · exact Or.inr ⟨u, w, hadj, hb, ht⟩
      · exact Or.inr h

private lemma bond_coords_close (b : LatticeBond) :
    (|b.source.1 - b.base.1| ≤ 1 ∧ |b.source.2 - b.base.2| ≤ 1) ∧
    (|b.target.1 - b.base.1| ≤ 1 ∧ |b.target.2 - b.base.2| ≤ 1) ∧
    (∀ s, |(b.faceBase s).1 - b.base.1| ≤ 1 ∧ |(b.faceBase s).2 - b.base.2| ≤ 1) := by
  rcases b with ⟨⟨x, y⟩, ax⟩
  refine ⟨by simp [LatticeBond.source], by cases ax <;> simp [LatticeBond.target],
    fun s => by cases ax <;> cases s <;> simp [LatticeBond.faceBase]⟩

private theorem exists_grid_quadruple
    (f₁ f₂ : I × I → ℝ)
    (hf₁_0 : ∀ t : I, f₁ (0, t) ≤ 0) (hf₁_1 : ∀ t : I, 0 ≤ f₁ (1, t))
    (hf₂_0 : ∀ s : I, f₂ (s, 0) ≤ 0) (hf₂_1 : ∀ s : I, 0 ≤ f₂ (s, 1)) (n : ℕ) :
    ∃ x₀ x₁ x₂ y₁ y₂ : I × I,
      dist x₁ x₀ ≤ 1 / (n + 1 : ℝ) ∧ dist x₂ x₀ ≤ 1 / (n + 1 : ℝ) ∧
      dist y₁ x₀ ≤ 1 / (n + 1 : ℝ) ∧ dist y₂ x₀ ≤ 1 / (n + 1 : ℝ) ∧
      f₁ x₁ ≤ 0 ∧ 0 ≤ f₁ x₂ ∧ f₂ y₁ ≤ 0 ∧ 0 ≤ f₂ y₂ := by
  let N := n + 1
  let cut : RectangleVertex (0, 0) N N → Bool :=
    fun v => if v.1.1 = (N : ℤ) then false else decide (f₁ (gridPt n v.1) ≤ 0)
  have hN_div : ((N : ℤ) : ℝ) / (n + 1 : ℝ) = 1 := by
    push_cast [N]; exact div_self (by positivity)
  have hσ_true (v : RectangleVertex (0, 0) N N) (hv : cut v = true) : f₁ (gridPt n v.1) ≤ 0 := by
    dsimp [cut] at hv; split_ifs at hv; exact of_decide_eq_true hv
  have hσ_false (v : RectangleVertex (0, 0) N N) (hv : cut v = false) : 0 ≤ f₁ (gridPt n v.1) := by
    dsimp [cut] at hv
    split_ifs at hv with hN
    · have h1 : gridPt n v.1 = (1, (gridPt n v.1).2) :=
        Prod.ext (Subtype.ext (by dsimp [gridPt]; rw [hN, hN_div]; exact unitClamp_of_one_le le_rfl)) rfl
      rw [h1]; exact hf₁_1 _
    · exact le_of_not_ge (of_decide_eq_false hv)
  obtain ⟨bp, hbp, tp, htp, ⟨W⟩⟩ := rectangleLabelCutDual_bottom_top_reachable (0, 0) N N cut
    (fun v hv => by
      have h0 : gridPt n v.1 = (0, (gridPt n v.1).2) :=
        Prod.ext (Subtype.ext (by dsimp [gridPt]; rw [hv]; exact unitClamp_of_nonpos (by simp))) rfl
      dsimp [cut]; rw [ite_eq_right (by omega), decide_eq_true_iff, h0]
      exact hf₁_0 _)
    (fun v hv => by dsimp [cut]; exact ite_eq_left (by omega))
  have hbp_y : bp.1.2 = -1 := by rcases Finset.mem_image.1 hbp with ⟨_, _, rfl⟩; rfl
  have htp_y : tp.1.2 = (N : ℤ) := by rcases Finset.mem_image.1 htp with ⟨_, _, rfl⟩; simp [rectangleDualTopPortVertex]
  have hbp_f2 : f₂ (gridPt n bp.1) ≤ 0 := by
    have h0 : gridPt n bp.1 = ((gridPt n bp.1).1, 0) :=
      Prod.ext rfl (Subtype.ext (by
        dsimp [gridPt]; rw [hbp_y]
        exact unitClamp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))))
    rw [h0]; exact hf₂_0 _
  have htp_f2 : 0 ≤ f₂ (gridPt n tp.1) := by
    have h1 : gridPt n tp.1 = ((gridPt n tp.1).1, 1) :=
      Prod.ext rfl (Subtype.ext (by dsimp [gridPt]; rw [htp_y, hN_div]; exact unitClamp_of_one_le le_rfl))
    rw [h1]; exact hf₂_1 _
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    (walk_sign_change (rectangleLabelCutDualGraph (0, 0) N N cut) (fun z => f₂ (gridPt n z.1)) W hbp_f2 htp_f2).resolve_left
      fun heq => by have := congrArg (fun z : RectangleDualVertex (0, 0) N N => z.1.2) heq; omega
  obtain ⟨bond, hs, ht, hdiff, huv⟩ := (rectangleLabelCutDual_adj_iff_bond (0, 0) N N cut u v).1 hadj
  have hclose := bond_coords_close bond
  have hd_src := dist_gridPt_le n _ _ hclose.1.1 hclose.1.2
  have hd_tgt := dist_gridPt_le n _ _ hclose.2.1.1 hclose.2.1.2
  have hd_u : dist (gridPt n u.1) (gridPt n bond.base) ≤ 1 / (n + 1 : ℝ) := by
    rcases huv with ⟨hu', _⟩ | ⟨hu', _⟩ <;> rw [hu'] <;>
      exact dist_gridPt_le n _ _ (hclose.2.2 _).1 (hclose.2.2 _).2
  have hd_v : dist (gridPt n v.1) (gridPt n bond.base) ≤ 1 / (n + 1 : ℝ) := by
    rcases huv with ⟨_, hv'⟩ | ⟨_, hv'⟩ <;> rw [hv'] <;>
      exact dist_gridPt_le n _ _ (hclose.2.2 _).1 (hclose.2.2 _).2
  cases hsrc : cut ⟨bond.source, hs⟩ <;> cases htgt : cut ⟨bond.target, ht⟩
  · simp [hsrc, htgt] at hdiff
  · exact ⟨gridPt n bond.base, gridPt n bond.target, gridPt n bond.source, gridPt n u.1, gridPt n v.1,
      hd_tgt, hd_src, hd_u, hd_v, hσ_true _ htgt, hσ_false _ hsrc, hu, hv⟩
  · exact ⟨gridPt n bond.base, gridPt n bond.source, gridPt n bond.target, gridPt n u.1, gridPt n v.1,
      hd_src, hd_tgt, hd_u, hd_v, hσ_true _ hsrc, hσ_false _ htgt, hu, hv⟩
  · simp [hsrc, htgt] at hdiff

theorem pathRectangle_crossing_intersection
    {a b : ℝ × ℝ} {p₀ p₁ q₀ q₁ : ℝ × ℝ}
    (P : Path p₀ p₁) (Q : Path q₀ q₁)
    (hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2)
    (hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2)
    (hPleft : (P 0).1 = a.1) (hPright : (P 1).1 = b.1)
    (hQbottom : (Q 0).2 = a.2) (hQtop : (Q 1).2 = b.2) :
    ∃ s t : I, P s = Q t := by
  let f₁ : I × I → ℝ := fun z => (P z.1).1 - (Q z.2).1
  let f₂ : I × I → ℝ := fun z => (Q z.2).2 - (P z.1).2
  have hf₁_cont : Continuous f₁ := by fun_prop
  have hf₂_cont : Continuous f₂ := by fun_prop
  choose x₀ x₁ x₂ y₁ y₂ hd₁ hd₂ hd₃ hd₄ hf₁_le hf₁_ge hf₂_le hf₂_ge using
    exists_grid_quadruple f₁ f₂
      (fun t => by linarith [hPleft, (hQbox t).1])
      (fun t => by linarith [hPright, (hQbox t).2.1])
      (fun s => by linarith [hQbottom, (hPbox s).2.2.1])
      (fun s => by linarith [hQtop, (hPbox s).2.2.2])
  obtain ⟨z, _, φ, hφ_mono, hφ_lim⟩ := isCompact_univ.isSeqCompact (fun n => Set.mem_univ (x₀ n))
  have hlim_of_dist (w : ℕ → I × I) (hd : ∀ n, dist (w n) (x₀ n) ≤ 1 / (n + 1 : ℝ)) :
      Tendsto (w ∘ φ) atTop (𝓝 z) :=
    tendsto_of_tendsto_of_dist hφ_lim <| squeeze_zero (fun _ => dist_nonneg)
      (fun i => by rw [dist_comm]; exact (hd (φ i)).trans (by gcongr; exact hφ_mono.id_le i))
      (@tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _)
  have hz₁ : f₁ z = 0 := le_antisymm
    (le_of_tendsto (hf₁_cont.tendsto z |>.comp (hlim_of_dist x₁ hd₁)) (Eventually.of_forall fun n => hf₁_le (φ n)))
    (ge_of_tendsto (hf₁_cont.tendsto z |>.comp (hlim_of_dist x₂ hd₂)) (Eventually.of_forall fun n => hf₁_ge (φ n)))
  have hz₂ : f₂ z = 0 := le_antisymm
    (le_of_tendsto (hf₂_cont.tendsto z |>.comp (hlim_of_dist y₁ hd₃)) (Eventually.of_forall fun n => hf₂_le (φ n)))
    (ge_of_tendsto (hf₂_cont.tendsto z |>.comp (hlim_of_dist y₂ hd₄)) (Eventually.of_forall fun n => hf₂_ge (φ n)))
  exact ⟨z.1, z.2, Prod.ext (sub_eq_zero.1 hz₁) (sub_eq_zero.1 hz₂).symm⟩

end
end PottsDiscontinuity.FK.Curves
