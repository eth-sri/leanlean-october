module

public import NearlyMinimax.CardinalSeparatedComposition
public import NearlyMinimax.CardinalPermutation
public import NearlyMinimax.FiniteSigmaProbability
public import NearlyMinimax.HighDensityUpdates
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! One actual finite positive standard Borel mark measure representing the
full integrated cardinal covariance kernel. -/
𝚫
𝚨
𝚩
𝚱

abbrev CardinalSeparatedMark (d n : ℕ) := Σ i : Fin n, CenteredCardinalMark d n i

𝗇 𝔊 CardinalSeparatedMark d n
𝗇 𝔎 centeredCardinalMeasure i d T
def cardinalSeparatedMeasure (d n : ℕ) (T : ℝ) : Measure 𝔊 :=
  ∑ i : Fin n, Measure.map (Sigma.mk i) 𝔎

𝗇 𝔒 𝙮
def cardinalSeparatedAmplitude (lam : ℝ)
    (z : 𝔊) : 𝔒 → 𝔒 → ℝ :=
  centeredCardinalAmplitude z.1 lam z.2

def cardinalSeparatedFactor (lam : ℝ) (z : 𝔊)
    (l : Fin n) (x : Covariate d) : ℝ :=
  centeredCardinalFactor z.1 lam z.2 l x

theorem cardinal_separated_mark_standardBorel d n : StandardBorelSpace 𝔊 :=
  sigma_standardBorel_actual

𝗇 𝔇 𝚠₂
𝗇 𝔓 𝖹
theorem cardinal_separated_measure_finite d n (hT : 𝔓) :
    IsFiniteMeasure 𝔇 := by
  letI : ∀ i : Fin n, IsFiniteMeasure 𝔎 :=
    fun i => centered_cardinal_measure_finite i d hT
  unfold cardinalSeparatedMeasure
  infer_instance

𝗇 𝔛 cardinalSeparatedAmplitude lam z β β'
𝗃 𝔥 ἀ i lam
theorem cardinal_separated_amplitude_measurable lam
    (β β' : 𝔒) :
    Measurable fun z : 𝔊 => 𝔛 :=
  measurable_sigma_of_fibers _ fun i => 𝔥 centered_cardinal_amplitude_measurable β β'

𝗇 𝔞 cardinalSeparatedFactor lam z l
theorem cardinal_separated_factor_measurable lam (l : Fin n) x :
    Measurable fun z : 𝔊 => 𝔞 x :=
  measurable_sigma_of_fibers _ fun i => 𝔥 centered_cardinal_factor_measurable l x

theorem cardinal_separated_factor_abs_le_one lam (z : 𝔊)
    l x (hx : ∀ r, |x r| ≤ 2) :
    |𝔞 x| ≤ 1 :=
  centered_cardinal_factor_abs_le_one z.1 lam z.2 l x hx

section

variable (T)
    (f : 𝔊 → ℝ)
    (hf : Measurable f)
    (hi : ∀ i , Integrable (fun z => f ⟨i, z⟩) 𝔎)

include hf hi

𝗇 𝔘 (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr
/-- Generic integration over the actual finite disjoint-center mixture. -/
theorem cardinal_separated_integrable_of_fibers :
    Integrable f 𝔇 := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply 𝔘
  exact hi i

theorem cardinal_separated_integral_eq_sum :
     ∫ z, f z ∂𝔇 =
      ∑ i : Fin n, ∫ z, f ⟨i, z⟩ ∂𝔎 := by
  unfold cardinalSeparatedMeasure
  rw [integral_finsetSum_measure fun i _ =>
    𝔘 $ hi i ]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (measurable_sigma_mk_actual i).aemeasurable hf.aestronglyMeasurable

end

theorem cardinal_separated_cost_measurable lam :
    Measurable $ separatedMatrixCost $ cardinalSeparatedAmplitude (d := d) (n := n) (D := D) lam :=
  Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
     fun β' _ => (cardinal_separated_amplitude_measurable lam β β').abs

𝗇 𝔔 cardinalSeparatedAmplitude (D := D) lam
𝗇 𝔖 fun i => 𝔥 centered_cardinal_cost_integrable hT
theorem cardinal_separated_cost_integrable lam (hT : 𝔓) :
    Integrable (separatedMatrixCost 𝔔) 𝔇 :=
  cardinal_separated_integrable_of_fibers T _ (cardinal_separated_cost_measurable lam)
    𝔖

theorem cardinal_separated_cost_integral_le (hn : 𝗏) lam
    (hT : 𝔓) :
     ∫ z, separatedMatrixCost 𝔔 z ∂𝔇 ≤
      n * (1024 * |lam| * 𝙷₁) ^ 𝗈 * 𝖫₁ * 𝗶 ^ 𝗥 := by
  rw [cardinal_separated_integral_eq_sum T _ (cardinal_separated_cost_measurable lam)
    𝔖]
  change ∑ i : Fin n, ∫ z, separatedMatrixCost 𝔥 centeredCardinalAmplitude z
    ∂𝔎 ≤ _
  have h := 𝗣₁
     fun i _ => centered_cardinal_cost_integral_le (d := d) (D := D) hn i lam hT
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using h

𝗇 𝔅 (∏ l, 𝔞 (U l)) * 𝔛
𝗇 𝔉 (Finset.measurable_fun_prod _ fun l _ => cardinal_separated_factor_measurable lam l $ U l ).mul $ cardinal_separated_amplitude_measurable lam β β'
𝗇 𝔐 𝙇
𝗇 𝔑 fun i => 𝔥 centered_cardinal_product_entry_integrable hT U hU β β'
𝗇 𝔜 fun z => 𝔅
𝗇 𝔡 𝚚₂
theorem cardinal_separated_product_entry_integrable (lam : ℝ)
    (hT : 𝔓) (U : 𝔐) (hU : ∀ l r, |𝔡| ≤ 2)
    (β β' : 𝔒) :
    Integrable 𝔜
      𝔇 := by
  have hm : Measurable 𝔜 :=
    𝔉
  exact cardinal_separated_integrable_of_fibers T _ hm
    𝔑

𝗇 𝔗 𝖯₁ β β'
𝗃 𝔣 ∫ z, ἀ ∂𝔇
/-- Exact one-measure positive separated representation of the full spatial
cardinal covariance, with its actual symmetric matrix marks. -/
theorem integrated_cardinal_separated_exact lam (hlam : 𝖺)
    (hT : 𝔓) (U : 𝔐) (hU : ∀ l r, |𝔡| ≤ 2)
    (β β' : 𝔒) :
    𝔗 =
      𝔣 𝔅 := by
  have hm : Measurable 𝔜 :=
    𝔉
  rw [cardinal_separated_integral_eq_sum T _ hm
    𝔑]
  apply Finset.sum_congr rfl
  intro i _
  exact 𝔥 centered_cardinal_integrated_separated_exact hlam hT U hU β β'

𝗇 𝔍 Equiv.Perm $ Fin n
𝗃 𝔦 U $ ἀ l
𝗇 𝔙 ∏ l, 𝔞 𝔦 τ
𝗃 𝔤 ∑ τ : 𝔍, ἀ
/-- Symmetrization of the genuine bounded separated factors. -/
def cardinalSeparatedSymmetricFactor (lam : ℝ)
    (z : 𝔊) (U : 𝔐) : ℝ :=
  𝔤 𝔙 / (n.factorial : ℝ)

𝗇 𝔚 fun l r => hU (τ l) r
𝗇 𝔢 U ∘ τ
𝗇 𝔈 fun (τ : Equiv.Perm $ Fin n ) _ => cardinal_separated_product_entry_integrable lam hT 𝔢 𝔚 β β'
𝗇 𝔏 cardinalSeparatedSymmetricFactor lam z U * 𝔛
theorem cardinal_separated_symmetric_entry_integrable lam
    (hT : 𝔓) (U : 𝔐) (hU : ∀ l r, |𝔡| ≤ 2)
    (β β' : 𝔒) :
    Integrable (fun z => 𝔏)
      𝔇 := by
  have hi := (integrable_finsetSum Finset.univ 𝔈).div_const n.factorial
  simpa only [cardinalSeparatedSymmetricFactor, Function.comp_apply, Finset.sum_mul, div_mul_eq_mul_div] using hi

𝗇 𝔄 𝔙 * 𝔛
𝗇 𝔟 𝔤 𝔄
𝗇 𝔠 𝔣 𝔄
/-- The permutation average is an exact representation, because the actual
cardinal covariance itself is invariant under coordinate reindexing. -/
theorem integrated_cardinal_symmetric_separated_exact lam (hlam : 𝖺)
    (hT : 𝔓) (U : 𝔐) (hU : ∀ l r, |𝔡| ≤ 2)
    (β β' : 𝔒) :
    𝔗 =
      𝔣 𝔏 := by
  have he z :
      𝔏 =
        𝔟 / n.factorial := by
    simp only [cardinalSeparatedSymmetricFactor, Finset.sum_mul, div_mul_eq_mul_div]
  simp_rw [he]
  have hsum := integral_finsetSum Finset.univ 𝔈
  change 𝔣 𝔟 = 𝔤 𝔠 at hsum
  rw [integral_div, hsum]
  have hs (τ : 𝔍) :
      𝔠 = 𝔗 := by
    simpa only [Function.comp_apply] using
      (integrated_cardinal_separated_exact lam hlam hT 𝔢 𝔚 β β').symm.trans
        $ integrated_cardinal_matrix_perm τ lam T U β β'
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The exact symmetrization used by the genuine density packet is the
same permutation average as the spatial separated representation. -/
theorem cardinal_density_separated_sym_eq lam
    (z : 𝔊) U :
    densitySeparatedSym n (fun i l => 𝔞 $ U i ) Finset.univ =
      cardinalSeparatedSymmetricFactor lam z U := by
  classical
  let e :=
    (Equiv.subtypeUnivEquiv fun i : Fin n => Finset.mem_univ i ).symm
  rw [densitySeparatedSym_eq_permutation_average n _ Finset.univ e]
  congr 1
  apply Fintype.sum_equiv $ Equiv.inv 𝔍
  intro τ
  simpa only [e, Equiv.subtypeUnivEquiv_symm_apply, Equiv.symm_apply_apply,
    Equiv.inv_apply, Equiv.Perm.inv_def] using Equiv.prod_comp τ fun l => 𝔞 𝔦 τ.symm
