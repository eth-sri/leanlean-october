module

public import QPBT.Games.Sandwich.Pasting.PinchedReduction
public import QPBT.Games.Sandwich.Pasting.OverlapCalculus

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

open Pasting

section ProductComparison

variable {X R S ι : Type*}
  [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]

/-- The cross term in the squared distance between the two orders of a product. -/
private noncomputable def orderedCross (P : Measurement R ι) (Q : Measurement S ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : ℝ :=
  ∑ a, ∑ b, stateQForm ψ (heteroKron 1 (Q.effect b * P.effect a * Q.effect b * P.effect a))

section

variable (D : Distribution X) (P : X → Measurement R ι)
    (Q : X → Measurement S ι)
include D P Q

private theorem overlap_product_eq (ψ : EuclideanSpace ℂ (ι × ι)) :
    overlap D (fun x (ab : R × S) => heteroKron 1 ((P x).effect ab.1 * (Q x).effect ab.2))
      (fun x ab => heteroKron 1 ((Q x).effect ab.2 * (P x).effect ab.1)) ψ =
    avgOver D (fun x => orderedCross (P x) (Q x) ψ) := by
  simp only [overlap, orderedCross, Fintype.sum_prod_type, heteroKron_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul, measurement_effect_hermitian,
    heteroKron_mul, one_mul, mul_assoc]

section

variable (ψ : EuclideanSpace ℂ (ι × ι))
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
include ψ hD hψ

private theorem ordered_mass_le :
    opFamilyDistSq D (fun x (ab : R × S) => heteroKron 1 ((P x).effect ab.1 * (Q x).effect ab.2))
      (fun _ _ => 0) ψ ≤ 1 := by
  let L x := Measurement.rightPlacement (ιA := ι) (P x)
  let R x := Measurement.rightPlacement (ιA := ι) (Q x)
  exact (by simpa only [L, R, Measurement.rightPlacement_effect, heteroKron_mul, one_mul,
    mul_zero] using product_distance_mono D L (fun x b => (R x).effect b) (fun _ _ => 0) ψ :
    _ ≤ opFamilyDistSq D (fun x b => (R x).effect b) (fun _ _ => 0) ψ).trans
      (measurement_mass_le_one D R ψ hD hψ)

private theorem ordered_mass_rev_le :
    opFamilyDistSq D (fun x (ab : R × S) => heteroKron 1 ((Q x).effect ab.2 * (P x).effect ab.1))
      (fun _ _ => 0) ψ ≤ 1 := by
  rw [opFamilyDistSq_reindex D (Equiv.prodComm R S) _ _ ψ]
  exact ordered_mass_le D Q P ψ hD hψ

end

/-- Both orders of the coarse product are close to the joint projective measurement. -/
private theorem avg_orderedCross_ge
    (A : X → Measurement (R × S) ι) (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hA : ∀ x, QPBT.Measurement.IsProjective (A x))
    (h₁ : bipartiteDefect D
      (fun x => (A x).postprocess Prod.fst)
      P ψ ≤ δ)
    (h₂ : bipartiteDefect D
      (fun x => (A x).postprocess Prod.snd)
      Q ψ ≤ δ) :
    1 - 2 * Real.sqrt (8 * δ) ≤ avgOver D (fun x => orderedCross (P x) (Q x) ψ) := by
  classical
  let J (x : X) := Measurement.leftPlacement (ιB := ι) (A x)
  let A₁ x := Measurement.leftPlacement (ιB := ι) ((A x).postprocess Prod.fst)
  let A₂ x := Measurement.leftPlacement (ιB := ι) ((A x).postprocess Prod.snd)
  let B₁ x := Measurement.rightPlacement (ιA := ι) (P x)
  let B₂ x := Measurement.rightPlacement (ιA := ι) (Q x)
  have h₁' := placed_dist_le D (fun x => (A x).postprocess Prod.fst) P ψ h₁
  have h₂' := placed_dist_le D (fun x => (A x).postprocess Prod.snd) Q ψ h₂
  have hj (x : X) : QPBT.Measurement.IsProjective (J x) :=
    Measurement.isProjective_leftPlacement _ (hA x)
  rw [← overlap_product_eq]
  refine overlap_lower D _ _ (fun x => (J x).effect) ψ ?_ ?_
    (ordered_mass_rev_le D P Q ψ hD hψ) (projective_mass_eq_one D J ψ hD hψ hj)
  · have h := product_distance_le D B₁ A₁ B₂ A₂ ψ (fun x a b =>
      (left_right_commute _ _).symm)
    simp only [A₁, A₂, B₁, B₂, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, heteroKron_mul, one_mul, mul_one,
      joint_marginal_product_rev _ (hA _)] at h
    exact h.trans (by linarith)
  · rw [opFamilyDistSq_reindex D (Equiv.prodComm R S) _ _ ψ]
    have h := product_distance_le D B₂ A₂ B₁ A₁ ψ (fun x b a =>
      (left_right_commute _ _).symm)
    simp only [A₁, A₂, B₁, B₂, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, heteroKron_mul, one_mul, mul_one,
      joint_marginal_product _ (hA _)] at h
    exact h.trans (by linarith)

end

private noncomputable def pinchedOverlap (P : Measurement R ι) (Q H : Measurement S ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : ℝ :=
  ∑ b, stateQForm ψ (heteroKron (H.effect b) (∑ a, P.effect a * Q.effect b * P.effect a))

private theorem avg_orderedCross_sub_le
    (D : Distribution X) (P : X → Measurement R ι) (Q H : X → Measurement S ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) {d : ℝ}
    (h : opFamilyDistSq D (fun x b => heteroKron 1 ((Q x).effect b))
      (fun x b => heteroKron ((H x).effect b) 1) ψ ≤ d) :
    |avgOver D (fun x => orderedCross (P x) (Q x) ψ) -
        avgOver D (fun x => pinchedOverlap (P x) (Q x) (H x) ψ)| ≤ Real.sqrt d := by
  let U (x : X) (ab : R × S) := heteroKron (1 : Op ι) ((P x).effect ab.1 * (Q x).effect ab.2)
  let V (x : X) (ab : R × S) := heteroKron ((H x).effect ab.2) ((P x).effect ab.1)
  let W (x : X) (ab : R × S) := heteroKron (1 : Op ι) ((Q x).effect ab.2 * (P x).effect ab.1)
  have huv : opFamilyDistSq D U V ψ ≤ d := by
    have h' := product_distance_mono D (fun x => Measurement.rightPlacement (ιA := ι) (P x))
      (fun x b => heteroKron 1 ((Q x).effect b)) (fun x b => heteroKron ((H x).effect b) 1) ψ
    simpa only [U, V, Measurement.rightPlacement_effect, heteroKron_mul, mul_one, one_mul] using
      h'.trans h
  have hw := abs_overlap_sub_le_sqrt D U V W ψ huv (ordered_mass_rev_le _ _ _ _ hD hψ)
  have e : overlap D V W ψ = avgOver D (fun x => pinchedOverlap (P x) (Q x) (H x) ψ) := by
    simp only [overlap, V, W, pinchedOverlap, Fintype.sum_prod_type, heteroKron_conjTranspose,
      measurement_effect_hermitian, heteroKron_mul, mul_one]
    simp_rw [heteroKron_finset_sum_right, stateQForm_finset_sum, mul_assoc]
    exact avgOver_congr _ _ _ fun _ => Finset.sum_comm
  rw [show overlap D U W ψ = _ from overlap_product_eq D P Q ψ, e] at hw
  exact hw

end ProductComparison
section FineComparison

variable {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂]
  [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]

local notation "Ques" => (X × Y₁) × Y₂

/-- Coarsening the pinched overlap adds just the colliding off-diagonal pairs. -/
private theorem pinchedOverlap_coarse_sub (P : Measurement R₁ ι) (G H : Measurement Γ₂ ι)
    (f : Γ₂ → R₂) (ψ : EuclideanSpace ℂ (ι × ι)) :
    pinchedOverlap P (G.postprocess f) (H.postprocess f) ψ - pinchedOverlap P G H ψ =
      ∑ g, ∑ g', if g = g' then 0 else if f g = f g' then
        stateQForm ψ (heteroKron (H.effect g) (pinchOp P (G.effect g'))) else 0 := by
  change (∑ r, stateQForm ψ (heteroKron ((H.postprocess f).effect r)
    (pinchOp P ((G.postprocess f).effect r)))) - _ = _
  simp only [Measurement.postprocess_effect, pinchOp_sum]
  rw [diagonal_fiber_stateQForm_eq_pair_sum]
  exact sum_colliding_sub_diagonal f _

/-- The fine commutator is small when the coarse ordered cross term has mass near one. -/
private theorem fine_commutator_le
    (D : Distribution Ques) (eval₂ : Γ₂ → Y₂ → R₂)
    (G H : X → Measurement Γ₂ ι) (P : X × Y₁ → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η t εc εf : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : HasConditionalCollisionBound D eval₂ η)
    (hcoarse : 1 - t ≤ avgOver D (fun q =>
      orderedCross (P q.1) ((G q.1.1).postprocess (fun g => eval₂ g q.2)) ψ))
    (hc : opFamilyDistSq D
      (fun q b => heteroKron 1 (((G q.1.1).postprocess (fun g => eval₂ g q.2)).effect b))
      (fun q b => heteroKron (((H q.1.1).postprocess (fun g => eval₂ g q.2)).effect b) 1) ψ ≤ εc)
    (hf : opFamilyDistSq D (fun q g => heteroKron 1 ((G q.1.1).effect g))
      (fun q g => heteroKron ((H q.1.1).effect g) 1) ψ ≤ εf) :
    avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
      (heteroKron 1 ((P q.1).effect a * (G q.1.1).effect g -
        (G q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) ≤
      2 * t + 2 * η + 2 * Real.sqrt εc + 2 * Real.sqrt εf := by
  classical
  let Gc (q : Ques) := (G q.1.1).postprocess (fun g => eval₂ g q.2)
  let Hc (q : Ques) := (H q.1.1).postprocess (fun g => eval₂ g q.2)
  have hC := (abs_le.mp (avg_orderedCross_sub_le D (fun q => P q.1) Gc Hc ψ hD hψ hc)).2
  have hF := (abs_le.mp (avg_orderedCross_sub_le D (fun q => P q.1) (fun q => G q.1.1)
    (fun q => H q.1.1) ψ hD hψ hf)).1
  have hcoll' := avgOver_pinched_collision_le_distinct_families D eval₂ G H P ψ η hD hψ hη hcoll
  have hgap : avgOver D (fun q => pinchedOverlap (P q.1) (Gc q) (Hc q) ψ) -
      avgOver D (fun q => pinchedOverlap (P q.1) (G q.1.1) (H q.1.1) ψ) ≤ η := by
    rw [← avgOver_sub]
    exact (avgOver_congr D _ _ (fun q => pinchedOverlap_coarse_sub _ _ _ _ ψ)).le.trans hcoll'
  change 1 - t ≤ avgOver D (fun q => orderedCross (P q.1) (Gc q) ψ) at hcoarse
  have hmass := ordered_mass_le D (fun q => P q.1) (fun q => G q.1.1) ψ hD hψ
  have hmass' := ordered_mass_rev_le D (fun q => P q.1) (fun q => G q.1.1) ψ hD hψ
  calc
    _ = opFamilyDistSq D
        (fun q (p : R₁ × Γ₂) => heteroKron 1 ((P q.1).effect p.1 * (G q.1.1).effect p.2))
        (fun q p => heteroKron 1 ((G q.1.1).effect p.2 * (P q.1).effect p.1)) ψ := by
      simp only [opFamilyDistSq, Fintype.sum_prod_type, heteroKron_sub_right]
    _ ≤ _ := by
      rw [distance_eq_overlap, overlap_product_eq]
      linarith

end FineComparison

/-- Assemble the marginal estimates. The coarse products track the joint effect,
and the collision bound transfers their overlap to the fine products. -/
theorem consistencyDefect_pasted_le_sqrt_one_sided {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, QPBT.Measurement.IsProjective (G₂ x))
    (hA : ∀ q, QPBT.Measurement.IsProjective (A q))
    (hcoll : HasConditionalCollisionBound D eval₂ η)
    (h₁ : bipartiteDefect D
      (fun q => (A q).postprocess Prod.fst)
      (fun q => (G₁ q.1.1).postprocess
        (fun g => eval₁ g q.1.2)) ψ ≤ δ)
    (h₂ : bipartiteDefect D
      (fun q => (A q).postprocess Prod.snd)
      (fun q => (G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)) ψ ≤ δ) :
    bipartiteDefect D A (pastedEvaluation eval₁ eval₂ G₁ G₂ hG₂) ψ ≤
      2 * δ + Real.sqrt (4 * Real.sqrt (8 * δ) + 2 * η +
        2 * Real.sqrt (4 * δ) + 2 * Real.sqrt (4 * δ + 2 * η)) := by
  classical
  let P (p : X × Y₁) := (G₁ p.1).postprocess (fun g => eval₁ g p.2)
  let Q (q : (X × Y₁) × Y₂) := (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)
  let H x := schmidtMirrorMeasurement ψ (G₂ x)
  let Hc (q : (X × Y₁) × Y₂) := (H q.1.1).postprocess (fun g => eval₂ g q.2)
  have hQ (q : (X × Y₁) × Y₂) : QPBT.Measurement.IsProjective (Q q) :=
    SandwichProduct.postprocess_isProjective _ (hG₂ q.1.1) _
  have hc : bipartiteDefect D Hc
      Q ψ ≤ 2 * δ := by
    have h := consistencyDefect_schmidtMirror_le D (fun q => (A q).postprocess Prod.snd) Q ψ hQ
    simpa only [Hc, H, Q, schmidtMirrorMeasurement_postprocess] using
      h.trans (mul_le_mul_of_nonneg_left h₂ (by norm_num))
  have hf := (consistencyDefect_codeword_fine_le_coarse_add_distinct_families
    D eval₂ G₂ H ψ η hD hψ hη hcoll).trans (add_le_add hc le_rfl)
  have hcDist := placed_dist_le D Hc Q ψ hc
  have hfDist := placed_dist_le D (fun q => H q.1.1) (fun q => G₂ q.1.1) ψ hf
  have hk := fine_commutator_le D eval₂ G₂ H P ψ η (2 * Real.sqrt (8 * δ))
    (4 * δ) (4 * δ + 2 * η) hD hψ hη hcoll
    (avg_orderedCross_ge D (fun q => P q.1) Q A ψ δ hD hψ hA h₁ h₂)
    (hcDist.trans_eq (by ring)) (hfDist.trans_eq (by ring))
  have hpinch := consistencyDefect_pinched_le_marginal_add_sqrt D G₂
    (fun q => P q.1) (fun q => (A q).postprocess Prod.fst) ψ _ hD hψ hG₂ hk
  have hpaste := consistencyDefect_pasted_le_marginal_add_pinched D eval₁ eval₂ G₁ G₂ A ψ hG₂
  have he : 2 * (2 * Real.sqrt (8 * δ)) = 4 * Real.sqrt (8 * δ) := by ring
  rw [he] at hpinch
  linarith

/-- The defect of two placed measurement families on a unit state never exceeds one. -/
theorem consistencyDefect_placed_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    bipartiteDefect μ A
      B ψ ≤ 1 := by
  rw [consistencyDefect_placed_eq_one_sub_overlap μ A B ψ hμ hψ]
  exact sub_le_self _ (avgOver_nonneg _ _ fun x => Finset.sum_nonneg fun a _ =>
    stateQForm_nonneg _ (kronecker_nonneg ((A x).pos a) ((B x).pos a)))

/-- Absorb the square-root errors into the stated power envelope on the unit square. -/
theorem pasting_error_sqrt_le_rpow (δ η : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hη : 0 ≤ η) (hη' : η ≤ 1) :
    2 * δ + Real.sqrt (4 * Real.sqrt (8 * δ) + 2 * η +
      2 * Real.sqrt (4 * δ) + 2 * Real.sqrt (4 * δ + 2 * η)) ≤
      115 * (η ^ (1/4 : ℝ) + δ ^ (1/8 : ℝ)) := by
  let u := δ ^ (1 / 8 : ℝ)
  let v := η ^ (1 / 4 : ℝ)
  have hu : 0 ≤ u := Real.rpow_nonneg hδ _
  have hv : 0 ≤ v := Real.rpow_nonneg hη _
  have hu1 : u ≤ 1 := Real.rpow_le_one hδ hδ' (by norm_num)
  have hv1 : v ≤ 1 := Real.rpow_le_one hη hη' (by norm_num)
  have hu8 : u ^ 8 = δ := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]
    norm_num
  have hv4 : v ^ 4 = η := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
    norm_num
  have hu4 : δ ≤ (u ^ 2) ^ 2 := by
    rw [← hu8, ← pow_mul]
    exact pow_le_pow_of_le_one hu hu1 (by norm_num)
  have hηv : η ≤ v ^ 2 := by
    rw [← hv4]
    exact pow_le_pow_of_le_one hv hv1 (by norm_num)
  have h₈ : Real.sqrt (8 * δ) ≤ 3 * u ^ 2 := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  have h₄ : Real.sqrt (4 * δ) ≤ 2 * u ^ 2 := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  have hsum : Real.sqrt (4 * δ + 2 * η) ≤ 2 * u ^ 2 + 2 * v ^ 2 :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg v)])
  have hs := (Real.sqrt_le_left (show 0 ≤ 5 * (u + v) by positivity)).2
    (show 4 * Real.sqrt (8 * δ) + 2 * η + 2 * Real.sqrt (4 * δ) +
      2 * Real.sqrt (4 * δ + 2 * η) ≤ (5 * (u + v)) ^ 2 by
      nlinarith [mul_nonneg hu hv, sq_nonneg u, sq_nonneg v])
  have hdu : δ ≤ u := by
    rw [← hu8]
    simpa only [pow_one] using (pow_le_pow_of_le_one hu hu1 (show 1 ≤ 8 by omega))
  change _ ≤ 115 * (v + u)
  linarith

end MIPStarRE.QPBT
