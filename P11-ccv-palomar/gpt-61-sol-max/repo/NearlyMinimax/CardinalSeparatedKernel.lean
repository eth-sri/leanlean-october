module

public import NearlyMinimax.CardinalSeparatedComposition
public import NearlyMinimax.CardinalPermutation
public import NearlyMinimax.FiniteSigmaProbability
public import NearlyMinimax.HighDensityUpdates

@[expose] public section

/-! One actual finite positive standard Borel mark measure representing the
full integrated cardinal covariance kernel. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev CardinalSeparatedMark d n := Σ i : Fin n, CenteredCardinalMark d n i

def cardinalSeparatedMeasure (d n : ℕ) (T : ℝ) : Measure (CardinalSeparatedMark d n) :=
  ∑ i : Fin n, Measure.map (Sigma.mk i) (centeredCardinalMeasure i d T)

def cardinalSeparatedAmplitude {d n D : ℕ} (lam : ℝ)
    (z : CardinalSeparatedMark d n) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  centeredCardinalAmplitude z.1 lam z.2

def cardinalSeparatedFactor {d n } lam (z : CardinalSeparatedMark d n)
    l x  :=
  centeredCardinalFactor z.1 lam z.2 l x

theorem cardinal_separated_mark_standardBorel d n : StandardBorelSpace (CardinalSeparatedMark d n) :=
  sigma_standardBorel_actual

theorem cardinal_separated_measure_finite d n {T } (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalSeparatedMeasure d n T) := by
  letI : ∀ i : Fin n, IsFiniteMeasure (centeredCardinalMeasure i d T) :=
    fun i => centered_cardinal_measure_finite i d hT
  unfold cardinalSeparatedMeasure
  infer_instance

theorem cardinal_separated_amplitude_measurable {d n D } lam
    (β β' : HighFrameIndex d D) :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedAmplitude lam z β β') :=
  measurable_sigma_of_fibers _ (fun i => centered_cardinal_amplitude_measurable i lam β β')

section
variable {d n : ℕ}

theorem cardinal_separated_factor_measurable  lam l x :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedFactor lam z l x) :=
  measurable_sigma_of_fibers _ (fun i => centered_cardinal_factor_measurable i lam l x)

theorem cardinal_separated_factor_abs_le_one  lam z
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |cardinalSeparatedFactor lam z l x| ≤ 1 :=
  centered_cardinal_factor_abs_le_one z.1 lam z.2 l x hx

section
variable (T : ℝ) (f : CardinalSeparatedMark d n → ℝ) (hf : Measurable f) (hi : ∀ i : Fin n, Integrable (fun z => f ⟨i, z⟩) (centeredCardinalMeasure i d T))
include hf hi

/-- Generic integration over the actual finite disjoint-center mixture. -/
theorem cardinal_separated_integrable_of_fibers   :
    Integrable f (cardinalSeparatedMeasure d n T) := by
  unfold cardinalSeparatedMeasure
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr
  exact hi i

theorem cardinal_separated_integral_eq_sum   :
    (∫ z, f z ∂cardinalSeparatedMeasure d n T) =
      ∑ i : Fin n, ∫ z, f ⟨i, z⟩ ∂centeredCardinalMeasure i d T := by
  unfold cardinalSeparatedMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr (hi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (measurable_sigma_mk_actual i).aemeasurable hf.aestronglyMeasurable
end

end


section
variable {d n D : ℕ}

theorem cardinal_separated_cost_measurable  lam :
    Measurable (separatedMatrixCost (cardinalSeparatedAmplitude (d := d) (n := n) (D := D) lam)) :=
  Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (cardinal_separated_amplitude_measurable lam β β').abs))

theorem cardinal_separated_cost_integrable  lam {T } (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam)) (cardinalSeparatedMeasure d n T) :=
  cardinal_separated_integrable_of_fibers T _ (cardinal_separated_cost_measurable lam)
    (fun i => centered_cardinal_cost_integrable i lam hT)

theorem cardinal_separated_cost_integral_le  (hn : 2 ≤ n) lam
    {T } (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z ∂cardinalSeparatedMeasure d n T) ≤
      n * (1024 * |lam| * d ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  rw [cardinal_separated_integral_eq_sum T _ (cardinal_separated_cost_measurable lam)
    (fun i => centered_cardinal_cost_integrable i lam hT)]
  change (∑ i : Fin n, ∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z
    ∂centeredCardinalMeasure i d T) ≤ _
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => centered_cardinal_cost_integral_le (d := d) (D := D) hn i lam hT)
  simp_all [mul_assoc]

theorem cardinal_separated_product_entry_integrable  lam
    {T } (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) := by
  have hm : Measurable (fun z : CardinalSeparatedMark d n =>
      (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β') :=
    (Finset.measurable_fun_prod _ (fun l _ => cardinal_separated_factor_measurable lam l (U l))).mul
      (cardinal_separated_amplitude_measurable lam β β')
  exact cardinal_separated_integrable_of_fibers T _ hm
    (fun i => centered_cardinal_product_entry_integrable i lam hT U hU β β')

/-- Exact one-measure positive separated representation of the full spatial
cardinal covariance, with its actual symmetric matrix marks. -/
theorem integrated_cardinal_separated_exact  lam (hlam : 0 ≤ lam)
    {T } (hT : 1 ≤ T) U (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' =
      ∫ z, (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T := by
  have hm : Measurable (fun z : CardinalSeparatedMark d n =>
      (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β') :=
    (Finset.measurable_fun_prod _ (fun l _ => cardinal_separated_factor_measurable lam l (U l))).mul
      (cardinal_separated_amplitude_measurable lam β β')
  rw [cardinal_separated_integral_eq_sum T _ hm
    (fun i => centered_cardinal_product_entry_integrable i lam hT U hU β β')]
  unfold integratedCardinalMatrix
  apply Finset.sum_congr rfl
  intro i _
  exact centered_cardinal_integrated_separated_exact i lam hlam hT U hU β β'
end


/-- Symmetrization of the genuine bounded separated factors. -/
def cardinalSeparatedSymmetricFactor {d n } lam
    z (U : Fin n → Covariate d)  :=
  (∑ τ : Equiv.Perm (Fin n), ∏ l, cardinalSeparatedFactor lam z l (U (τ l))) / (n.factorial : ℝ)

theorem cardinal_separated_symmetric_entry_integrable {d n D } lam
    {T } (hT : 1 ≤ T) U (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) := by
  have hi := (integrable_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun (τ : Equiv.Perm (Fin n)) _ =>
    cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β')).div_const (n.factorial : ℝ)
  simpa only [cardinalSeparatedSymmetricFactor, Function.comp_apply, Finset.sum_mul, div_mul_eq_mul_div] using hi

/-- The permutation average is an exact representation, because the actual
cardinal covariance itself is invariant under coordinate reindexing. -/
theorem integrated_cardinal_symmetric_separated_exact {d n D } lam (hlam : 0 ≤ lam)
    {T } (hT : 1 ≤ T) U (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T := by
  have he (z : CardinalSeparatedMark d n) :
      cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β' =
        (∑ τ : Equiv.Perm (Fin n),
          (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β') / (n.factorial : ℝ) := by
    simp only [cardinalSeparatedSymmetricFactor, Finset.sum_mul, div_mul_eq_mul_div]
  simp_rw [he]
  have hsum := integral_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun (τ : Equiv.Perm (Fin n)) _ =>
    cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β')
  change (∫ z, ∑ τ : Equiv.Perm (Fin n),
    (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
    ∂cardinalSeparatedMeasure d n T) = ∑ τ : Equiv.Perm (Fin n),
      ∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T at hsum
  rw [integral_div, hsum]
  have hs (τ : Equiv.Perm (Fin n)) :
      (∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T) = integratedCardinalMatrix lam T U β β' := by
    simpa only [Function.comp_apply] using
      (integrated_cardinal_separated_exact lam hlam hT (U ∘ τ) (fun l r => hU (τ l) r) β β').symm.trans
        (integrated_cardinal_matrix_perm τ lam T U β β')
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- The exact symmetrization used by the genuine density packet is the
same permutation average as the spatial separated representation. -/
theorem cardinal_density_separated_sym_eq {d n } lam
    (z : CardinalSeparatedMark d n) U :
    densitySeparatedSym n (fun i l => cardinalSeparatedFactor lam z l (U i)) Finset.univ =
      cardinalSeparatedSymmetricFactor lam z U := by
  classical
  let e  :=
    (Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)).symm
  rw [densitySeparatedSym_eq_permutation_average n _ Finset.univ e]
  unfold cardinalSeparatedSymmetricFactor
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n)))
  intro τ
  have h := Equiv.prod_comp τ (fun l => cardinalSeparatedFactor lam z l (U (τ.symm l)))
  aesop (add unsafe [Equiv.subtypeUnivEquiv_symm_apply])

end NearlyMinimax
