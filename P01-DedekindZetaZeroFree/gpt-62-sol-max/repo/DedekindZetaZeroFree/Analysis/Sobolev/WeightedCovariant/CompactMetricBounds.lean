module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

namespace KPCompactInteriorH1

open MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace
















private theorem density_bounds {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (w : E n → ℝ) (Q : InverseMetric Ω)
    (A : Connection (r := r) Ω) (a b κ Λ M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < κ) (hl : 0 < Λ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ C,
      (a ≤ w x ∧ w x ≤ b) ∧
      (∀ v : Fin n → V r, κ * (∑ j, ‖v j‖ ^ 2) ≤ Q.quadratic x v ∧
        Q.quadratic x v ≤ Λ * (∑ j, ‖v j‖ ^ 2)) ∧
      (∀ j, ‖A.A j x‖ ≤ M))
    (f : E n → V r) (g : Fin n → E n → V r)
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
    (hgsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → g j x = 0) :
    let B := b + 2 * b * Λ + 2 * b * Λ * n * M ^ 2
    let D := a⁻¹ + 2 * (a * κ)⁻¹ + 2 * n * M ^ 2 * a⁻¹
    ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      0 ≤ w x * Q.quadratic x (fun j => covariantFirst A f g j x) ∧
      w x * ‖f x‖ ^ 2 + w x * Q.quadratic x (fun j => covariantFirst A f g j x) ≤
        B * (‖f x‖ ^ 2 + ∑ j, ‖g j x‖ ^ 2) ∧
      ‖f x‖ ^ 2 + ∑ j, ‖g j x‖ ^ 2 ≤
        D * (w x * ‖f x‖ ^ 2 + w x * Q.quadratic x (fun j => covariantFirst A f g j x)) := by
  dsimp only
  have hall : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), ∀ j, x ∉ C → g j x = 0 :=
    Filter.eventually_all.mpr hgsupp
  filter_upwards [hfsupp, hall] with x hfx hgx
  by_cases hxC : x ∈ C
  · obtain ⟨hwx, hqx, hax⟩ := hbound x hxC
    let F := ‖f x‖ ^ 2
    let G := ∑ j, ‖g j x‖ ^ 2
    let d := fun j => covariantFirst A f g j x
    let J := ∑ j, ‖d j‖ ^ 2
    have hF : 0 ≤ F := sq_nonneg _
    have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hconn : ∀ j, ‖A.A j x (f x)‖ ≤ M * ‖f x‖ := fun j =>
      ((A.A j x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hax j) (norm_nonneg _))
    have hdg : ∀ j, ‖d j‖ ^ 2 ≤ 2 * ‖g j x‖ ^ 2 + 2 * M ^ 2 * F := by
      intro j
      have hh : ‖d j‖ ≤ ‖g j x‖ + M * ‖f x‖ := (norm_add_le _ _).trans
        (add_le_add_right (hconn j) _)
      dsimp [F]
      nlinarith [norm_nonneg (d j), norm_nonneg (g j x), norm_nonneg (f x),
        mul_nonneg hM (norm_nonneg (f x)), sq_nonneg (‖g j x‖ - M * ‖f x‖)]
    have hgd : ∀ j, ‖g j x‖ ^ 2 ≤ 2 * ‖d j‖ ^ 2 + 2 * M ^ 2 * F := by
      intro j
      have hh : ‖g j x‖ ≤ ‖d j‖ + M * ‖f x‖ := by
        have heq : g j x = d j - A.A j x (f x) := by simp [d, covariantFirst]
        rw [heq]
        exact (norm_sub_le _ _).trans (add_le_add_right (hconn j) _)
      dsimp [F]
      nlinarith [norm_nonneg (d j), norm_nonneg (g j x), norm_nonneg (f x),
        mul_nonneg hM (norm_nonneg (f x)), sq_nonneg (‖d j‖ - M * ‖f x‖)]
    have hJG : J ≤ 2 * G + 2 * n * M ^ 2 * F := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hdg j)
      simpa [J, G, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh
    have hGJ : G ≤ 2 * J + 2 * n * M ^ 2 * F := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hgd j)
      simpa [J, G, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh
    have hqlo : κ * J ≤ Q.quadratic x d := (hqx d).1
    have hqhi : Q.quadratic x d ≤ Λ * J := (hqx d).2
    have hqn : 0 ≤ Q.quadratic x d := (mul_nonneg hk.le hJ).trans hqlo
    have hwqn : 0 ≤ w x * Q.quadratic x d := mul_nonneg (ha.le.trans hwx.1) hqn
    have hWF : w x * F ≤ b * F := mul_le_mul_of_nonneg_right hwx.2 hF
    have hWJ : w x * Q.quadratic x d ≤ b * Λ * J := by
      calc w x * Q.quadratic x d ≤ b * Q.quadratic x d := mul_le_mul_of_nonneg_right hwx.2 hqn
           _ ≤ b * (Λ * J) := mul_le_mul_of_nonneg_left hqhi hb.le
           _ = b * Λ * J := by ring
    have hFrev : F ≤ a⁻¹ * (w x * F) := (le_inv_mul_iff₀ ha).mpr
      (mul_le_mul_of_nonneg_right hwx.1 hF)
    have hJrev : J ≤ (a * κ)⁻¹ * (w x * Q.quadratic x d) := by
      apply (le_inv_mul_iff₀ (mul_pos ha hk)).mpr
      calc a * κ * J = a * (κ * J) := by ring
           _ ≤ a * Q.quadratic x d := mul_le_mul_of_nonneg_left hqlo ha.le
           _ ≤ w x * Q.quadratic x d := mul_le_mul_of_nonneg_right hwx.1 hqn
    have hJG' := mul_le_mul_of_nonneg_left hJG (mul_pos hb hl).le
    have hFrev' := mul_le_mul_of_nonneg_left hFrev
      (by positivity : 0 ≤ 2 * (n : ℝ) * M ^ 2)
    have hJrev' := mul_le_mul_of_nonneg_left hJrev (by norm_num : (0 : ℝ) ≤ 2)
    change 0 ≤ w x * Q.quadratic x d ∧
      w x * F + w x * Q.quadratic x d ≤
        (b + 2*b*Λ + 2*b*Λ*n*M^2) * (F+G) ∧
      F+G ≤ (a⁻¹ + 2*(a*κ)⁻¹ + 2*n*M^2*a⁻¹) * (w x*F + w x*Q.quadratic x d)
    refine ⟨hwqn, ?_, ?_⟩
    · have ht : 0 ≤ b * G + 2*b*Λ*F + 2*b*Λ*n*M^2*G :=
        add_nonneg (add_nonneg (mul_nonneg hb.le hG)
          (mul_nonneg (by positivity) hF)) (mul_nonneg (by positivity) hG)
      nlinarith only [hWF, hWJ, hJG', ht]
    · have hWFpos : 0 ≤ w x * F := mul_nonneg (ha.le.trans hwx.1) hF
      have ht : 0 ≤ a⁻¹*(w x*Q.quadratic x d) + 2*(a*κ)⁻¹*(w x*F) +
          2*n*M^2*a⁻¹*(w x*Q.quadratic x d) :=
        add_nonneg (add_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) hwqn)
          (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_pos ha hk).le)) hWFpos))
          (mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr ha.le)) hwqn)
      nlinarith
  · simp [hfx hxC, hgx, hxC, covariantFirst, InverseMetric.quadratic]



end KPCompactInteriorH1

open KPCompactInteriorH1 MeasureTheory TopologicalSpace
open scoped ContDiff


end DedekindZetaZeroFree

end
