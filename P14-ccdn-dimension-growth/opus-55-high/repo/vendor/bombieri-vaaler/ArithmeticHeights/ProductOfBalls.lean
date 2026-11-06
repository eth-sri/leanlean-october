/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/

import ArithmeticHeights.SliceBound

/-!
# The slice bound for a product of balls of volume one

**Bombieri–Gubler, Lemma C.3.7.** Partition the coordinates of `ι → ℝ` into blocks by a map
`blk : ι → κ`, and let `prodBallPi blk` be the product over the blocks of the euclidean ball of
volume one in that block's coordinates. Then for every measurable convex symmetric `A`, the Gauss
measure of `A` is at most `vol (A ∩ prodBallPi blk)`.

The induction is on the number of coordinates, splitting off the block of a chosen coordinate; the
remaining blocks keep the same label type `κ`, with one label whose block has become empty — and an
empty block imposes no condition, so no re-indexing of the labels is needed.

## Main definitions

* `gaussPi`, the Gauss density on `ι → ℝ` for the euclidean norm.
* `ballRadius n`, the radius of the ball of volume one in `n` dimensions.
* `prodBallPi blk`, the product of the balls of volume one over the blocks of `blk`.

## Main results

* `hasSliceBound_ballPi`: the case of a single block.
* `hasSliceBound_prodBallPi`: **Bombieri–Gubler, Lemma C.3.7**, on `ι → ℝ`.
* `hasSliceBound_prodBallEuclidean`: the same on `EuclideanSpace ℝ ι`.
* `hasPrekopaLeindler_innerProductSpace`: Prékopa–Leindler on any finite-dimensional real inner
  product space, which is what Lemma C.3.4 is applied to in Layer 4.5's endgame.

## Implementation notes

⚠ **The induction is on coordinates, not on blocks, and that removes all re-indexing.** Splitting
off the block of one coordinate leaves a smaller coordinate set with the *same* label type; the
label just peeled off now has an empty block, and the condition attached to an empty block —
`0 ≤ ballRadius 0 ^ 2` — is vacuous. Inducting on the number of blocks instead would force the
labels to be renumbered at every step.

⚠ **The radius is indexed by the cardinality of the block, not by the block.** `ballRadius n` is
the radius of the ball of volume one in `EuclideanSpace ℝ (Fin n)`; a block is a subtype, and
`unitVolumeRadius_euclideanSpace` identifies its radius with `ballRadius` of its cardinality. This
is the one place where the index type is changed, and it is done once rather than at every step of
the induction.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma C.3.7.

This is Layer 4.5 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

open MeasureTheory Measure Set ENNReal
open scoped Real

section
variable {ι : Type*} [Fintype ι]

/-- The Gauss density on `ι → ℝ` for the euclidean norm. -/
noncomputable def gaussPi (x : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-π * ∑ i, (x i) ^ 2))

@[fun_prop]
theorem measurable_gaussPi : Measurable (gaussPi : (ι → ℝ) → ℝ≥0∞) := by
  unfold gaussPi; fun_prop

theorem gaussPi_le_one (x : ι → ℝ) : gaussPi x ≤ 1 := by
  rw [gaussPi, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_le_one_iff]
  have h : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := by positivity
  nlinarith [Real.pi_pos]

theorem gaussPi_neg (x : ι → ℝ) : gaussPi (-x) = gaussPi x := by
  have h : ∑ i, ((-x) i) ^ 2 = ∑ i, (x i) ^ 2 := by simp_all
  rw [gaussPi, gaussPi, h]

theorem gaussPi_eq_gaussDensity (x : ι → ℝ) :
    gaussPi x = gaussDensity (WithLp.toLp 2 x : EuclideanSpace ℝ ι) := by
  rw [gaussPi, gaussDensity_def, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp

/-- The Gauss density is log-concave: the quadratic form `∑ x i ^ 2` is convex. -/
theorem logConcave_gaussPi : LogConcave (gaussPi : (ι → ℝ) → ℝ≥0∞) := by
  intro a b ha hb hab x y
  have hkey : ∑ i, ((a • x + b • y) i) ^ 2 ≤ a * ∑ i, (x i) ^ 2 + b * ∑ i, (y i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp
    nlinarith [sq_nonneg (x i - y i), mul_nonneg ha.le hb.le]
  rw [gaussPi, gaussPi, gaussPi, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

end

/-- The radius of the ball of volume one in `n` dimensions: Bombieri–Gubler's `ρ(n)`. -/
noncomputable def ballRadius (n : ℕ) : ℝ := unitVolumeRadius (EuclideanSpace ℝ (Fin n))

theorem volume_ball_euclideanSpace_congr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    volume (Metric.ball (0 : EuclideanSpace ℝ α) 1)
      = volume (Metric.ball (0 : EuclideanSpace ℝ β) 1) := by
  let f : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ β :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hpre : f ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ β) 1)
      = Metric.ball (0 : EuclideanSpace ℝ α) 1 := by
    ext x
    simp
  rw [← hpre, f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]

section
variable (α : Type*) [Fintype α]

theorem unitVolumeRadius_euclideanSpace :
    unitVolumeRadius (EuclideanSpace ℝ α) = ballRadius (Fintype.card α) := by
  rw [ballRadius, unitVolumeRadius, unitVolumeRadius,
    volume_ball_euclideanSpace_congr (Fintype.equivFin α)]
  simp

/-- **The slice bound for a single block**: the ball of volume one in `α → ℝ`. -/
theorem hasSliceBound_ballPi :
    HasSliceBound (volume : Measure (α → ℝ)) gaussPi
      {y : α → ℝ | ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card α) ^ 2} := by
  have h := HasSliceBound.of_measurePreserving (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm
    (PiLp.volume_preserving_toLp α) (PiLp.volume_preserving_ofLp α).measurable
    measurable_gaussDensity measurableSet_closedBall
    (hasSliceBound_closedBall volume unitVolumeRadius_pos volume_closedBall_unitVolumeRadius lintegral_gaussDensity_eq_one)
  have hdens : (fun x =>
      gaussDensity ((WithLp.linearEquiv 2 ℝ (α → ℝ)).symm x)) = gaussPi :=
    funext fun x => (gaussPi_eq_gaussDensity x).symm
  have hset : (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℝ α) (unitVolumeRadius (EuclideanSpace ℝ α))
      = {y : α → ℝ | ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card α) ^ 2} := by
    ext y
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq,
      unitVolumeRadius_euclideanSpace,
      Real.sqrt_le_left (unitVolumeRadius_euclideanSpace α ▸
        (unitVolumeRadius_pos).le)]
    simp
  rwa [hdens, hset] at h

end

theorem hasSliceBound_univ_of_le_one {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    {μ : Measure E} {g : E → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) {Q : Set E} (hQ : ∀ x, x ∈ Q) :
    HasSliceBound μ g Q := by
  intro A _ _ _
  calc ∫⁻ x in A, g x ∂μ ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun x => hg x
    _ = μ A := setLIntegral_one A
    _ = μ (A ∩ Q) := by rw [Set.inter_eq_self_of_subset_left fun x _ => hQ x]

section
variable {ι S : Type*} [Fintype S] (f : S → ι) (c : ℝ)

theorem convex_setOf_sum_sq_le :
    Convex ℝ {x : ι → ℝ | ∑ j : S, (x (f j)) ^ 2 ≤ c} := by
  intro x hx y hy a b ha hb hab
  have hpt : ∑ j : S, ((a • x + b • y) (f j)) ^ 2
      ≤ a * ∑ j : S, (x (f j)) ^ 2 + b * ∑ j : S, (y (f j)) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    simp
    nlinarith [sq_nonneg (x (f j) - y (f j)), mul_nonneg ha hb]
  calc ∑ j : S, ((a • x + b • y) (f j)) ^ 2
      ≤ a * ∑ j : S, (x (f j)) ^ 2 + b * ∑ j : S, (y (f j)) ^ 2 := hpt
    _ ≤ a * c + b * c := by bound
    _ = c := by grind

theorem neg_mem_setOf_sum_sq_le
    {x : ι → ℝ} (hx : x ∈ {x : ι → ℝ | ∑ j : S, (x (f j)) ^ 2 ≤ c}) :
    -x ∈ {x : ι → ℝ | ∑ j : S, (x (f j)) ^ 2 ≤ c} := by
  have h : ∑ j : S, ((-x) (f j)) ^ 2 = ∑ j : S, (x (f j)) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by simp
  change ∑ j : S, ((-x) (f j)) ^ 2 ≤ c
  rw [h]; exact hx

end

section
variable {ι κ : Type*} [Fintype ι] [DecidableEq κ] (blk : ι → κ)

/-- The product over the blocks of `blk` of the euclidean ball of volume one in that block's
coordinates: Bombieri–Gubler's `Q_N = B_{ρ(n₁)} × ⋯ × B_{ρ(n_r)}`. -/
def prodBallPi :
    Set (ι → ℝ) :=
  {x | ∀ k : κ, ∑ j : {j : ι // blk j = k}, (x j) ^ 2
    ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2}

theorem prodBallPi_eq_iInter :
    prodBallPi blk = ⋂ k : κ, {x : ι → ℝ | ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
      ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} := by
  ext x; simp [prodBallPi]

theorem measurableSet_prodBallPi [Countable κ]
    : MeasurableSet (prodBallPi blk) := by
  rw [prodBallPi_eq_iInter]
  exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const

theorem convex_prodBallPi :
    Convex ℝ (prodBallPi blk) := by
  rw [prodBallPi_eq_iInter]
  exact convex_iInter fun k => convex_setOf_sum_sq_le _ _

theorem neg_mem_prodBallPi
    {x : ι → ℝ} (hx : x ∈ prodBallPi blk) :
    -x ∈ prodBallPi blk := by
  rw [prodBallPi_eq_iInter] at hx ⊢
  simp only [Set.mem_iInter] at hx ⊢
  exact fun k => neg_mem_setOf_sum_sq_le _ _ (hx k)

end

section
variable (α : Type*) [Fintype α]

/-- Prékopa–Leindler on `α → ℝ` for an arbitrary finite index type. -/
theorem hasPrekopaLeindler_pi' :
    HasPrekopaLeindler (volume : Measure (α → ℝ)) :=
  HasPrekopaLeindler.of_measurePreserving (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm
    (PiLp.volume_preserving_toLp α) (PiLp.volume_preserving_ofLp α).measurable
    (show HasPrekopaLeindler (volume : Measure (EuclideanSpace ℝ α)) by
        let f : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card α)) :=
          LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
        exact HasPrekopaLeindler.of_measurePreserving f.toLinearEquiv f.measurePreserving
          f.symm.continuous.measurable (hasPrekopaLeindler_euclideanSpace _))

end

/-- **Prékopa–Leindler on a finite-dimensional real inner product space.** -/
theorem hasPrekopaLeindler_innerProductSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    HasPrekopaLeindler (volume : Measure E) := by
  let f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := (stdOrthonormalBasis ℝ E).repr
  exact HasPrekopaLeindler.of_measurePreserving f.toLinearEquiv f.measurePreserving
    f.symm.continuous.measurable (hasPrekopaLeindler_euclideanSpace _)

theorem hasSliceBound_prodBallPi_aux.{u} {κ : Type*} [DecidableEq κ] [Countable κ]
    (n : ℕ) :
    ∀ (α : Type u) [Fintype α] (blk : α → κ),
      Fintype.card α ≤ n →
      HasSliceBound (volume : Measure (α → ℝ)) gaussPi (prodBallPi blk) := by
  have hempty : ∀ (α : Type u) [Fintype α] (blk : α → κ), IsEmpty α →
      HasSliceBound volume gaussPi (prodBallPi blk) := by
    intro α _ blk hα
    refine hasSliceBound_univ_of_le_one gaussPi_le_one fun x k => ?_
    have h : (Finset.univ : Finset {j : α // blk j = k}) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j _ => hα.elim j.1
    rw [h, Finset.sum_empty]
    exact sq_nonneg _
  induction n with
  | zero =>
    intro α _ blk hcard
    exact hempty α blk (Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro α _ blk hcard
    rcases isEmpty_or_nonempty α with hα | hα
    · grind
    obtain ⟨j₀⟩ := hα
    have hcards : 0 < Fintype.card {j : α // blk j = blk j₀} :=
      Fintype.card_pos_iff.mpr ⟨⟨j₀, rfl⟩⟩
    have hcardt : Fintype.card {j : α // ¬ (blk j = blk j₀)} ≤ n := by
      have h := Fintype.card_subtype_compl (fun j => blk j = blk j₀)
      omega
    let L : (α → ℝ) ≃ₗ[ℝ]
        (({j : α // blk j = blk j₀} → ℝ) × ({j : α // ¬ (blk j = blk j₀)} → ℝ)) :=
      { Equiv.piEquivPiSubtypeProd (fun j => blk j = blk j₀) (fun _ => ℝ) with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let blkt : {j : α // ¬ (blk j = blk j₀)} → κ := fun j => blk j.val
    have hMP : MeasurePreserving L volume
        (volume : Measure ((({j : α // blk j = blk j₀}) → ℝ)
          × (({j : α // ¬ (blk j = blk j₀)}) → ℝ))) := by
      rw [Measure.volume_eq_prod]
      exact measurePreserving_piEquivPiSubtypeProd (fun _ => (volume : Measure ℝ))
        (fun j => blk j = blk j₀)
    have hsymm :=
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℝ)
        (fun j => blk j = blk j₀)).symm.measurable
    have hprod : HasSliceBound (volume : Measure ((({j : α // blk j = blk j₀}) → ℝ)
        × (({j : α // ¬ (blk j = blk j₀)}) → ℝ)))
        (fun q => gaussPi q.1 * gaussPi q.2)
        ({y : {j : α // blk j = blk j₀} → ℝ |
            ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card {j : α // blk j = blk j₀}) ^ 2}
          ×ˢ prodBallPi blkt) := by
      rw [Measure.volume_eq_prod]
      exact HasSliceBound.prod measurable_gaussPi gaussPi_neg logConcave_gaussPi
        measurable_gaussPi (measurableSet_prodBallPi blkt) (convex_prodBallPi blkt)
        (fun _ hz => neg_mem_prodBallPi blkt hz)
        (hasPrekopaLeindler_pi' _) (hasPrekopaLeindler_pi' _)
        (hasSliceBound_ballPi _) (ih _ blkt hcardt)
    have hdens : (fun x => gaussPi (L x).1 * gaussPi (L x).2) = gaussPi := by
      funext x
      have h1 : ∑ j : {j : α // blk j = blk j₀}, ((L x).1 j) ^ 2
          = ∑ j : {j : α // blk j = blk j₀}, (x j.val) ^ 2 := rfl
      have h2 : ∑ j : {j : α // ¬ (blk j = blk j₀)}, ((L x).2 j) ^ 2
          = ∑ j : {j : α // ¬ (blk j = blk j₀)}, (x j.val) ^ 2 := rfl
      have hsum : ∑ i, (x i) ^ 2
          = (∑ j : {j : α // blk j = blk j₀}, (x j.val) ^ 2)
            + ∑ j : {j : α // ¬ (blk j = blk j₀)}, (x j.val) ^ 2 :=
        (Fintype.sum_subtype_add_sum_subtype _ _).symm
      rw [gaussPi, gaussPi, gaussPi, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        h1, h2, hsum]
      grind
    have hiff : ∀ (x : α → ℝ) (k : κ), k ≠ blk j₀ →
        ((∑ j : {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k}, (x j.1.1) ^ 2
            ≤ ballRadius (Fintype.card {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k}) ^ 2)
          ↔ (∑ j : {j : α // blk j = k}, (x j.1) ^ 2
            ≤ ballRadius (Fintype.card {j : α // blk j = k}) ^ 2)) := by
      intro x k hk
      let e : {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k} ≃ {j : α // blk j = k} :=
        { toFun := fun j => ⟨j.1.1, j.2⟩
          invFun := fun j => ⟨⟨j.1, fun hcon => hk (by grind)⟩, j.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.sum_equiv e (fun j => (x j.1.1) ^ 2) (fun j => (x j.1) ^ 2)
        (fun _ => rfl), Fintype.card_congr e]
    have hset : (L : (α → ℝ) → _) ⁻¹' ({y : {j : α // blk j = blk j₀} → ℝ |
          ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card {j : α // blk j = blk j₀}) ^ 2}
        ×ˢ prodBallPi blkt) = prodBallPi blk := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩ k
        by_cases hk : k = blk j₀
        · aesop
        · exact (hiff x k hk).mp (h2 k)
      · intro h
        exact ⟨h (blk j₀), fun k => by
          by_cases hk : k = blk j₀
          · subst hk
            have hz : (Finset.univ :
                Finset {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = blk j₀}) = ∅ :=
              Finset.eq_empty_iff_forall_notMem.mpr fun j _ => j.1.2 j.2
            rw [hz, Finset.sum_empty]
            nlinarith
          · aesop⟩
    have hmeasg : Measurable (fun q : (({j : α // blk j = blk j₀}) → ℝ)
        × (({j : α // ¬ (blk j = blk j₀)}) → ℝ) => gaussPi q.1 * gaussPi q.2) :=
      (measurable_gaussPi.comp measurable_fst).mul (measurable_gaussPi.comp measurable_snd)
    have hfin := HasSliceBound.of_measurePreserving L hMP hsymm hmeasg
      ((measurableSet_le (by fun_prop) measurable_const).prod
        (measurableSet_prodBallPi blkt)) hprod
    rwa [hdens, hset] at hfin

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ] (blk : ι → κ)

/-- The product of balls of volume one, in `EuclideanSpace ℝ ι`. -/
def prodBall :
    Set (EuclideanSpace ℝ ι) :=
  {x | ∀ k : κ, ∑ j : {j : ι // blk j = k}, (x j) ^ 2
    ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2}

theorem prodBall_eq_preimage :
    prodBall blk = (WithLp.linearEquiv 2 ℝ (ι → ℝ)) ⁻¹' prodBallPi blk := rfl

theorem measurableSet_prodBall [Countable κ]
    : MeasurableSet (prodBall blk) := by
  rw [prodBall_eq_preimage]
  exact (PiLp.volume_preserving_ofLp ι).measurable (measurableSet_prodBallPi blk)

theorem convex_prodBall :
    Convex ℝ (prodBall blk) := by
  rw [prodBall_eq_preimage]
  exact (convex_prodBallPi blk).linear_preimage
    (WithLp.linearEquiv 2 ℝ (ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] (ι → ℝ))

theorem neg_mem_prodBall
    {x : EuclideanSpace ℝ ι} (hx : x ∈ prodBall blk) : -x ∈ prodBall blk := by
  rw [prodBall_eq_preimage] at hx ⊢
  have hneg : (WithLp.linearEquiv 2 ℝ (ι → ℝ)) (-x) = -((WithLp.linearEquiv 2 ℝ (ι → ℝ)) x) :=
    map_neg _ _
  simpa using neg_mem_prodBallPi blk hx

/-- **Bombieri–Gubler, Lemma C.3.7 on `EuclideanSpace ℝ ι`.** -/
theorem hasSliceBound_prodBall [Countable κ]
    :
    HasSliceBound (volume : Measure (EuclideanSpace ℝ ι)) gaussDensity (prodBall blk) := by
  have h := HasSliceBound.of_measurePreserving (WithLp.linearEquiv 2 ℝ (ι → ℝ))
    (PiLp.volume_preserving_ofLp ι) (PiLp.volume_preserving_toLp ι).measurable
    measurable_gaussPi (measurableSet_prodBallPi blk) (hasSliceBound_prodBallPi_aux _ ι blk le_rfl)
  have hdens : (fun x =>
      gaussPi ((WithLp.linearEquiv 2 ℝ (ι → ℝ)) x)) = gaussDensity := by
    funext x
    rw [gaussPi_eq_gaussDensity]
    rfl
  have hset : (WithLp.linearEquiv 2 ℝ (ι → ℝ)) ⁻¹' prodBallPi blk = prodBall blk := rfl
  rwa [hdens, hset] at h
