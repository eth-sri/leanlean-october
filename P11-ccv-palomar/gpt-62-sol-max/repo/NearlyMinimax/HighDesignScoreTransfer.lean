module

public import NearlyMinimax.DesignCounts
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighUnionFieldScore


@[expose] public section

/-! Actual iid membership-cell and normalized-design transfers. The
independent count law and unused-observation factors are derived from the
actual product probability experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α)

section
variable (S : Finset (Fin n))

/-- Split the restricted product into its inside and outside coordinates. -/
private theorem iid_membership_split :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α) (fun i => i ∈ S))
      ((Measure.pi (fun _ : Fin n => μ)).restrict (designMembershipCell n A S))
      ((Measure.pi (fun _ : S => μ.restrict A)).prod
        (Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ))) := by
  rw [designMembershipCell, Measure.restrict_pi_pi]
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun i : Fin n => μ.restrict (if i ∈ S then A else Aᶜ)) (fun i => i ∈ S)
  have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  grind

theorem iid_cell_selected_integrable (H : (S → α) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : S => μ.restrict A))) :
    IntegrableOn (fun x : Fin n → α => H (fun i : S => x i.val))
      (designMembershipCell n A S) (Measure.pi (fun _ : Fin n => μ)) :=
  (iid_membership_split μ n A S).integrable_comp_of_integrable (hH.comp_fst _)

/-- Exact selected-coordinate integral on an actual membership cell. -/
theorem iid_selected_membership_integral (H : (S → α) → ℝ) :
    (∫ x in designMembershipCell n A S, H (fun i : S => x i.val)
      ∂Measure.pi (fun _ : Fin n => μ)) =
      (μ.real Aᶜ) ^ (n - S.card) *
        ∫ z, H z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  have hs := (iid_membership_split μ n A S).integral_comp' (fun z => H z.1)
  change (∫ x in designMembershipCell n A S, H (fun i : S => x i.val) ∂Measure.pi (fun _ : Fin n => μ)) = _ at hs
  rw [hs, integral_fun_fst H]
  have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by
    rw [Fintype.card_subtype_compl]; simp
  simp only [Measure.real, Measure.pi_univ, Measure.restrict_apply_univ,
    Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, hcard, smul_eq_mul]

end

theorem design_membership_cells_cover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
  simp [design_membership_cell_iff]

/-- Every measurable iid patch admits the true disjoint membership-cell
partition of an integrable data function. -/
theorem iid_integral_eq_membership_sum (hA : MeasurableSet A)
    (H : (Fin n → α) → ℝ) (hH : Integrable H (Measure.pi (fun _ : Fin n => μ))) :
    (∫ x, H x ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ S : Finset (Fin n), ∫ x in designMembershipCell n A S, H x
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [← setIntegral_univ, ← design_membership_cells_cover n A]
  exact integral_iUnion_fintype (fun S => design_membership_cell_measurable n A hA S)
    (design_membership_cells_disjoint n A) (fun S => hH.integrableOn)

/-- Conditional iid energy is bounded by the actual selected-observation
energies; the unused-observation probability is bounded by one. -/
theorem iid_local_energy_le_selected_sum (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val)) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ S : Finset (Fin n), ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  rw [iid_integral_eq_membership_sum μ n A hA E hE]
  apply Finset.sum_le_sum
  intro S hS
  calc
    _ ≤ ∫ x in designMembershipCell n A S, H S (fun i : S => x i.val) ∂Measure.pi (fun _ : Fin n => μ) := by
      apply integral_mono_ae hE.integrableOn (iid_cell_selected_integrable μ n A S _ (hH S))
      filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
      exact hdom S x hx
    _ = (μ.real Aᶜ) ^ (n - S.card) * ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) :=
      iid_selected_membership_integral μ n A S (H S)
    _ ≤ _ := by
      have hmass : (μ.real Aᶜ) ^ (n - S.card) ≤ 1 := pow_le_one₀ measureReal_nonneg measureReal_le_one
      exact (mul_le_mul_of_nonneg_right hmass (integral_nonneg (hHn S))).trans_eq (one_mul _)

end

end NearlyMinimax
