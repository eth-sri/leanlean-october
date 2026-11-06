module
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import NearlyMinimax.FinePairUnionMassAnnihilation
public import NearlyMinimax.HighUnionFieldScore
public import NearlyMinimax.HighHistoryLikelihoodScore
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {E : Type*}
section
section
section
variable {E : Type*} [MeasurableSpace E]
end
variable {E : Type*} [MeasurableSpace E] [Nonempty E]
theorem product_centered_mgf_le (n π)
    [∀ i, IsProbabilityMeasure (π i)]
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F (Function.update x i y) - F x| ≤ c) (u ) :
    (∫ x, Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)) ∂Measure.pi π) ≤
      Real.exp (n * u ^ 2 * c ^ 2 / 8) := by
  have h_finiteMarkAppend_eq_snoc (n : ℕ) (fresh : E) (marks : Fin n → E) : historyFiniteMarkAppendEquiv n (fresh, marks) = Fin.snoc marks fresh := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [historyFiniteMarkAppendEquiv_last, Fin.snoc_last]
    · rw [historyFiniteMarkAppendEquiv_old, Fin.snoc_castSucc]
  have h_product_exp_integral_le : (∫ x, Real.exp (u * F x) ∂Measure.pi π) ≤
      Real.exp (u * ∫ x, F x ∂Measure.pi π) * Real.exp (n * u ^ 2 * c ^ 2 / 8) := by
    induction n with
    | zero =>
      let empty : Fin 0 → E := Fin.elim0
      have hf : F = fun _ => F empty := by funext x; congr 1; exact Subsingleton.elim _ _
      rw [hf]
      simp
    | succ n ih =>
      let ν := π (Fin.last n)
      let μ := Measure.pi (fun i : Fin n => π i.castSucc)
      let e := historyFiniteMarkAppendEquiv n (E := E)
      have h_finiteMarkAppend_preserving_varying : MeasurePreserving (historyFiniteMarkAppendEquiv n (E := E))
        ((π (Fin.last n)).prod (Measure.pi (fun i => π i.castSucc))) (Measure.pi π) := by
        simpa only [historyFiniteMarkAppendEquiv, Fin.succAbove_last_apply] using
          (measurePreserving_piFinSuccAbove π (Fin.last n)).symm _
      have hp  := h_finiteMarkAppend_preserving_varying
      let H := fun p => F (e p)
      have hH  := hF.comp e.measurable
      have hHi : Integrable H (ν.prod μ) := Integrable.of_bound hH.aestronglyMeasurable R
        (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbound (e p))
      let G := fun x => ∫ y, H (y, x) ∂ν
      have hG : Measurable G := hH.stronglyMeasurable.integral_prod_left'.measurable
      have hXi : ∀ x, Integrable (fun y => H (y, x)) ν := by
        intro x
        apply Integrable.of_bound (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable R
        exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, Function.comp_apply, Prod.map_apply, id_eq, H] using hbound (e (y, x))
      have hGb : ∀ x, |G x| ≤ R := by
        intro x
        simpa [G, Real.norm_eq_abs] using
          norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => H (y, x)) (C := R)
            (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, H] using hbound (e (y, x)))
      have hGo : ∀ i x y, |G (Function.update x i y) - G x| ≤ c := by
        intro i x y
        rw [← integral_sub (hXi _) (hXi _)]
        have hb : ∀ᵐ z ∂ν, ‖H (z, Function.update x i y) - H (z, x)‖ ≤ c := by
          apply Eventually.of_forall
          intro z
          simpa only [H, e, h_finiteMarkAppend_eq_snoc, Fin.snoc_update, Real.norm_eq_abs] using
            hosc i.castSucc (Fin.snoc x z) y
        simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb
      have hXo : ∀ x y z, |H (y, x) - H (z, x)| ≤ c := by
        intro x y z
        simpa only [H, e, h_finiteMarkAppend_eq_snoc, Fin.update_snoc_last] using
          hosc (Fin.last n) (Fin.snoc x z) y
      have hpoint : ∀ x, (∫ y, Real.exp (u * H (y, x)) ∂ν) ≤
          Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) := by
        intro x
        have hX : Measurable (fun y => H (y, x)) := hH.comp (measurable_id.prodMk measurable_const)
        have hbound  := fun y => hbound (e (y, x))
        have hosc  := hXo x
        have h_centered_mgf_le_of_oscillation (X : E → ℝ) (hX : Measurable X) (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) : (∫ e, Real.exp (u * (X e - ∫ f, X f ∂ν)) ∂ν) ≤ Real.exp (u ^ 2 * c ^ 2 / 8) := by
          let S := Set.range X
          have hne : S.Nonempty := Set.range_nonempty X
          have hbelow : BddBelow S := ⟨-R, by rintro z ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).1⟩
          have habove : BddAbove S := ⟨R, by rintro z ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).2⟩
          have : sSup S ≤ sInf S + c := by
            apply csSup_le hne
            rintro z ⟨e, rfl⟩
            have : X e - c ≤ sInf S := by
              apply le_csInf hne
              rintro z ⟨f, rfl⟩
              have := (abs_le.1 (hosc e f)).2
              linarith
            linarith
          have horder : 0 ≤ sSup S - sInf S := sub_nonneg.2 (csInf_le_csSup hne hbelow habove)
          have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := X)
            (a := sInf S) (b := sSup S) hX.aemeasurable (Eventually.of_forall (by intro e; exact ⟨csInf_le hbelow ⟨e, rfl⟩, le_csSup habove ⟨e, rfl⟩⟩))
          exact (hsg.mgf_le u).trans (Real.exp_le_exp.2 (by simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat, abs_of_nonneg horder]; have hsq : (sSup S - sInf S) ^ 2 ≤ c ^ 2 := (sq_le_sq₀ horder hc).2 (by linarith); nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg u)]))
        have hh := (h_centered_mgf_le_of_oscillation (fun y => H (y, x)) hX hbound hosc)
        have hf : (fun e => Real.exp (u * (fun y => H (y, x)) e)) =
            (fun e => Real.exp (u * ∫ f, (fun y => H (y, x)) f ∂ν) * Real.exp (u * ((fun y => H (y, x)) e - ∫ f, (fun y => H (y, x)) f ∂ν))) := by
          funext e
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hf, integral_const_mul]
        exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      have hmean : (∫ x, F x ∂Measure.pi π) = ∫ x, G x ∂μ := by
        rw [← hp.integral_comp' F, integral_prod_symm H hHi]
      have hEi : Integrable (fun p => Real.exp (u * H p)) (ν.prod μ) := by
        apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hH)).aestronglyMeasurable
          (Real.exp (|u| * R))
        apply Eventually.of_forall
        intro p
        change ‖Real.exp (u * H p)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.2
        exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbound (e p)) (abs_nonneg u))
      have hEGi : Integrable (fun x => Real.exp (u * G x)) μ := by
        apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hG)).aestronglyMeasurable
          (Real.exp (|u| * R))
        apply Eventually.of_forall
        intro x
        change ‖Real.exp (u * G x)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.2
        exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb x) (abs_nonneg u))
      rw [← hp.integral_comp' (fun x => Real.exp (u * F x)), integral_prod_symm _ hEi, hmean]
      calc
        _ ≤ ∫ x, Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) ∂μ :=
          integral_mono (hEi.integral_prod_right) (hEGi.mul_const _) hpoint
        _ = (∫ x, Real.exp (u * G x) ∂μ) * Real.exp (u ^ 2 * c ^ 2 / 8) := integral_mul_const _ _
        _ ≤ Real.exp (u * ∫ x, G x ∂μ) * Real.exp (n * u ^ 2 * c ^ 2 / 8) *
            Real.exp (u ^ 2 * c ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right (ih (fun i => π i.castSucc) G hG hGb hGo) (Real.exp_pos _).le
        _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring
  let m := ∫ y, F y ∂Measure.pi π
  have hf : (fun x => Real.exp (u * (F x - m))) =
      (fun x => Real.exp (-u * m) * Real.exp (u * F x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, integral_const_mul]
  have hprod : Real.exp (-u * m) * Real.exp (u * m) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ ≤ Real.exp (-u * m) *
        (Real.exp (u * m) * Real.exp (n * u ^ 2 * c ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left (h_product_exp_integral_le) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, hprod, one_mul]
end
section
variable {J I E : Type*} [Fintype J] [Fintype I] [MeasurableSpace E]
def labelBlockReconstruct (labels : I → J) (blocks : J → I → E) : I → E :=
  fun i => blocks (labels i) i
theorem labelBlockReconstruct_measurable (labels : I → J) :
    Measurable (labelBlockReconstruct labels (E := E)) := by
  apply measurable_pi_iff.2
  intro i
  exact (measurable_pi_apply i).comp (measurable_pi_apply (labels i))
end
variable {J E : Type*} [Fintype J] [MeasurableSpace E] [Nonempty E]
theorem fintype_product_centered_mgf_le [DecidableEq J] (π )
    [∀ j, IsProbabilityMeasure (π j)]
    (F : (J → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ j x y, |F (Function.update x j y) - F x| ≤ c) (u ) :
    (∫ x, Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)) ∂Measure.pi π) ≤
      Real.exp ((Fintype.card J ) * u ^ 2 * c ^ 2 / 8) := by
  let f := (Fintype.equivFin J).symm
  let e := MeasurableEquiv.piCongrLeft (fun _ => E) f
  have hp  :=
    measurePreserving_piCongrLeft π f
  have he : ∀ (x : Fin (Fintype.card J) → E) i y,
      e (Function.update x i y) = Function.update (e x) (f i) y := by
    intro x i y
    funext j
    obtain ⟨k, rfl⟩ := f.surjective j
    change MeasurableEquiv.piCongrLeft (fun _ => E) f (Function.update x i y) (f k) = _
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    by_cases hk : k = i
    · subst k
      simp
    · have hfki  := fun h => hk (f.injective h)
      rw [Function.update_of_ne hk, Function.update_of_ne hfki]
      exact (MeasurableEquiv.piCongrLeft_apply_apply f (β := fun _ => E) x k).symm
  let G := F ∘ e
  have hh := product_centered_mgf_le (Fintype.card J) (fun i => π (f i)) G
    (hF.comp e.measurable) R c hc (fun x => hbound (e x)) (by intro i x y; dsimp only [G, Function.comp_apply]; rw [he]; exact hosc (f i) (e x) y) u
  have hm : (∫ x, G x ∂Measure.pi (fun i => π (f i))) = ∫ x, F x ∂Measure.pi π :=
    hp.integral_comp' F
  rw [hm] at hh
  change (∫ x, Real.exp (u * (F (e x) - ∫ y, F y ∂Measure.pi π))
    ∂Measure.pi (fun i => π (f i))) ≤ _ at hh
  rw [hp.integral_comp' (fun x => Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)))] at hh
  exact hh
theorem label_block_centered_mgf_le  [Fintype I] [DecidableEq J]
    (labels : I → J) (π : Measure E) [IsProbabilityMeasure π]
    (F : (I → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ marks, |F marks| ≤ R)
    (hosc : ∀ j marks marks', (∀ i, labels i ≠ j → marks i = marks' i) → |F marks - F marks'| ≤ c)
    (u : ℝ) :
    (∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂Measure.pi (fun _ : I => π)))
      ∂Measure.pi (fun _ : I => π)) ≤ Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  let ν := Measure.pi (fun _ : I => π)
  let μ := Measure.pi (fun _ : J => ν)
  let G := F ∘ labelBlockReconstruct labels
  have h_labelBlockReconstruct_preserving : MeasurePreserving (labelBlockReconstruct labels (E := E))
      (Measure.pi (fun _ : J => Measure.pi (fun _ : I => π)))
      (Measure.pi (fun _ : I => π)) := by
    refine ⟨labelBlockReconstruct_measurable labels, ?_⟩
    apply (Measure.pi_eq (μ := fun _ : I => π) ?_).symm
    intro s hs
    rw [Measure.map_apply (labelBlockReconstruct_measurable labels) (MeasurableSet.univ_pi hs)]
    have hp : labelBlockReconstruct labels ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun j : J => Set.univ.pi (fun i : I => if labels i = j then s i else Set.univ)) := by
      ext blocks
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, labelBlockReconstruct]
      constructor
      · intro h j i
        by_cases hij : labels i = j
        · simpa only [hij, ite_true] using h i
        · simp only [hij, ite_false, Set.mem_univ]
      · intro h i
        simpa only [ite_true] using h (labels i) i
    rw [hp, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    have he : ∀ j i, π (if labels i = j then s i else Set.univ) =
        if labels i = j then π (s i) else 1 := by
      intro j i
      split_ifs <;> simp
    simp_rw [he]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    simp
  have hp := h_labelBlockReconstruct_preserving
  have hG  := hF.comp (labelBlockReconstruct_measurable labels)
  have hh := fintype_product_centered_mgf_le (fun _ : J => ν) G hG R c hc
    (fun blocks => hbound (labelBlockReconstruct labels blocks)) (by intro j blocks new; apply hosc j (labelBlockReconstruct labels (Function.update blocks j new)) (labelBlockReconstruct labels blocks); intro i hi; simp [labelBlockReconstruct, Function.update_of_ne hi]) u
  have hm : (∫ blocks, G blocks ∂μ) = ∫ marks, F marks ∂ν := by
    exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (I → E) => ∫ marks, F marks ∂m) hp.map_eq)
  change (∫ blocks, Real.exp (u * (G blocks - ∫ blocks', G blocks' ∂μ)) ∂μ) ≤ _ at hh
  rw [hm] at hh
  have hi : (∫ blocks, Real.exp (u * (G blocks - ∫ marks, F marks ∂ν)) ∂μ) =
      ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂ν := by
    have hmeas : Measurable (fun marks => Real.exp (u * (F marks - ∫ marks', F marks' ∂ν))) :=
      Real.measurable_exp.comp (measurable_const.mul (hF.sub measurable_const))
    exact (integral_map hp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (I → E) => ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂m) hp.map_eq)
  rw [hi] at hh
  exact hh
end
section
variable {Ω : Type*} [MeasurableSpace Ω]
theorem massPowerNormalizer_one_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1) :
    1 ≤ massPowerNormalizer μ m n := by
  have him : Integrable m μ := by simpa only [pow_one] using (massPower_integrable μ m hm 1 l b hl hbound)
  have hh : (∫ ω, 1 + n * (m ω - 1) ∂μ) ≤ ∫ ω, m ω ^ n ∂μ :=
    integral_mono ((integrable_const 1).add ((him.sub (integrable_const 1)).const_mul ↑n)) (massPower_integrable μ m hm n l b hl hbound)
      (fun ω => one_add_mul_sub_le_pow ((by norm_num : (-1 : ℝ) ≤ 0).trans (hl.le.trans (hbound ω).1)) n)
  have he : (∫ ω, 1 + ↑n * (m ω - 1) ∂μ) = 1 := by
    calc
      _ = (∫ _ : Ω, 1 ∂μ) + ∫ ω, n * (m ω - 1) ∂μ :=
        integral_add (integrable_const 1) ((him.sub (integrable_const 1)).const_mul n)
      _ = 1 := by rw [integral_const_mul, integral_sub him (integrable_const 1), hmean]; simp
  rw [he] at hh
  exact hh
theorem massPowerTilt_abs_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (a ε : ℝ) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∫ ω, Real.exp (u * (m ω - 1)) ∂μ) ≤ Real.exp (a * u ^ 2))
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} ≤ 2 * Real.exp (-ε ^ 2 / (8 * a)) := by
  have h_massPowerTilt_real_apply (S : Set Ω) (hS : MeasurableSet S) : (massPowerTilt μ m n).real S =
      ∫ ω, S.indicator (fun ω => m ω ^ n / massPowerNormalizer μ m n) ω ∂μ := by
    let := massPowerTilt_isProbability μ m hm n l b hl hbound
    rw [← integral_indicator_one hS, massPowerTilt,
      integral_withDensity_eq_integral_toReal_smul ((hm.pow_const n).div_const _).ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ S <;> simp [hω, ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (hl.le.trans (hbound ω).1) _) (massPowerNormalizer_pos μ m hm n l b hl hbound).le), smul_eq_mul]
  have h_boundedMass_exp_integrable (u : ℝ) : Integrable (fun ω => Real.exp (u * (m ω - 1))) μ := by
    apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))).aestronglyMeasurable
      (Real.exp (|u| * (|b| + 1)))
    apply Eventually.of_forall
    intro ω
    change ‖Real.exp (u * (m ω - 1))‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have : |m ω| ≤ |b| := by
      rw [abs_of_pos (hl.trans_le (hbound ω).1)]
      exact (hbound ω).2.trans (le_abs_self b)
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by have hh := abs_sub (m ω) 1; norm_num only [abs_one] at hh; linarith) (abs_nonneg u))
  let := massPowerTilt_isProbability μ m hm n l b hl hbound
  have he0  := (by positivity : ↑0 ≤ 8 * a * ↑n).trans hε
  have : (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    have h_massTilt_exponent_right : 0 ≤ ε / (2 * a) - ↑n ∧
      -(ε / (2 * a) - ↑n) * ε + a * (↑n + (ε / (2 * a) - ↑n)) ^ 2 ≤
        -ε ^ 2 / (8 * a) := by
      have : ↑0 ≤ n := Nat.cast_nonneg n
      have he0  := (by positivity : ↑0 ≤ 8 * a * ↑n).trans hε
      have hu : 0 ≤ ε / (2 * a) - ↑n := by
        apply sub_nonneg.2
        apply (le_div_iff₀ (by positivity : ↑0 < 2 * a)).2
        nlinarith
      have : ↑n * ε ≤ ε ^ 2 / (8 * a) := by
        apply (le_div_iff₀ (by positivity : ↑0 < 8 * a)).2
        nlinarith [mul_nonneg he0 (sub_nonneg.2 hε)]
      have hid : -(ε / (2 * a) - ↑n) * ε + a * (↑n + (ε / (2 * a) - ↑n)) ^ 2 =
          ↑n * ε - 2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
      exact ⟨hu, by rw [hid]; simp only [neg_div]; linarith⟩
    have hs := h_massTilt_exponent_right
    have h_massPowerTilt_right_chernoff (u) (hu : 0 ≤ u) : (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤
        Real.exp (-u * ε) * ∫ ω, Real.exp ((n + u) * (m ω - 1)) ∂μ := by
      let S := {ω | ε < m ω - 1}
      have hS : MeasurableSet S := measurableSet_lt measurable_const (hm.sub measurable_const)
      rw [h_massPowerTilt_real_apply S hS, ← integral_const_mul]
      apply integral_mono (((massPower_integrable μ m hm n l b hl hbound).div_const _).indicator hS)
        ((h_boundedMass_exp_integrable (n + u)).const_mul _)
      intro ω
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
        have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
        have hpow : m ω ^ n ≤ Real.exp (n * (m ω - 1)) := by
          have := Real.add_one_le_exp (m ω - 1)
          calc
            _ ≤ Real.exp (m ω - 1) ^ n := pow_le_pow_left₀ hm0 (by linarith) n
            _ = _ := (Real.exp_nat_mul _ _).symm
        calc
          _ ≤ m ω ^ n := div_le_self (pow_nonneg hm0 n) (massPowerNormalizer_one_le μ m hm n l b hl hbound hmean)
          _ ≤ Real.exp (n * (m ω - 1)) := hpow
          _ ≤ _ := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_nonneg hu (sub_nonneg.2 (hω.le))]
      · simp only [Set.indicator_of_notMem hω]
        positivity
    calc
      _ ≤ Real.exp (-(ε / (2 * a) - ↑n) * ε) *
          ∫ ω, Real.exp ((↑n + (ε / (2 * a) - ↑n)) * (m ω - 1)) ∂μ :=
        (h_massPowerTilt_right_chernoff _ hs.1)
      _ ≤ Real.exp (-(ε / (2 * a) - ↑n) * ε) *
          Real.exp (a * (↑n + (ε / (2 * a) - ↑n)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 hs.2
  have : (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    have hid : -(ε / (2 * a)) * ε + a * (-(ε / (2 * a))) ^ 2 =
        -2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
    have h_massPowerTilt_left_chernoff (u) (hu : 0 ≤ u) : (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤
        Real.exp (-u * ε) * ∫ ω, Real.exp ((-u) * (m ω - 1)) ∂μ := by
      let S := {ω | m ω - 1 < -ε}
      have hS : MeasurableSet S := measurableSet_lt (hm.sub measurable_const) measurable_const
      rw [h_massPowerTilt_real_apply S hS, ← integral_const_mul]
      apply integral_mono (((massPower_integrable μ m hm n l b hl hbound).div_const _).indicator hS)
        ((h_boundedMass_exp_integrable (-u)).const_mul _)
      intro ω
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
        have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
        calc
          _ ≤ m ω ^ n := div_le_self (pow_nonneg hm0 n) (massPowerNormalizer_one_le μ m hm n l b hl hbound hmean)
          _ ≤ 1 := pow_le_one₀ hm0 (by have : m ω - 1 < -ε := hω; linarith)
          _ ≤ _ := by
            rw [← Real.exp_add]
            apply Real.one_le_exp_iff.2
            nlinarith [mul_nonneg hu (sub_nonneg.2 (hω.le))]
      · simp only [Set.indicator_of_notMem hω]
        positivity
    calc
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * ∫ ω, Real.exp ((-(ε / (2 * a))) * (m ω - 1)) ∂μ :=
        (h_massPowerTilt_left_chernoff _ (div_nonneg he0 (by positivity)))
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * Real.exp (a * (-(ε / (2 * a))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by rw [hid]; simp only [neg_div]; have : 0 ≤ ε ^ 2 / (8 * a) := div_nonneg (sq_nonneg _) (by positivity); linarith)
  have hset : {ω | ε < |m ω - 1|} = {ω | ε < m ω - 1} ∪ {ω | m ω - 1 < -ε} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [hset]
  exact (measureReal_union_le _ _).trans (by linarith)
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedReference_integral_le_of_fiber_bound (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
     [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (R C : ℝ) (hbound : ∀ h, |F h| ≤ R)
    (hconditional : ∀ g, (∫ marks, F ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) ≤ C) :
    (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤ C := by
  let μ := historyMarkedReferenceRaw dependent Δ π
  let : IsFiniteMeasure μ := historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  let : IsProbabilityMeasure (historyMarkedReference dependent Δ π) :=
    historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable R
    (Eventually.of_forall fun h => by simpa only [Real.norm_eq_abs] using hbound h)
  have hc : Integrable (fun _ => C) μ := integrable_const C
  have hr : (∫ h, F h ∂μ) ≤ ∫ _ : HistoryMarked dependent E, C ∂μ := by
    change (∫ h, F h ∂Measure.sum _) ≤ ∫ _ : HistoryMarked dependent E, C ∂Measure.sum _
    rw [integral_sum_measure hi, integral_sum_measure hc]
    apply Summable.tsum_le_tsum (fun g => ?_)
      (hasSum_integral_measure hi).summable (hasSum_integral_measure hc).summable
    rw [integral_smul_measure, integral_smul_measure,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable hF.aestronglyMeasurable,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable measurable_const.aestronglyMeasurable]
    simp only [smul_eq_mul]
    simpa using mul_le_mul_of_nonneg_left (hconditional g) (ENNReal.toReal_nonneg)
  have he : (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤
      ∫ _ : HistoryMarked dependent E, C ∂historyMarkedReference dependent Δ π := by
    unfold historyMarkedReference
    rw [integral_smul_measure, integral_smul_measure]
    exact mul_le_mul_of_nonneg_left hr ENNReal.toReal_nonneg
  simpa using he
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedReference_mean_one (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
     [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m) (R : ℝ) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1) :
    (∫ h, m h ∂historyMarkedReference dependent Δ π) = 1 := by
  have := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π m hm R 1 hbound (fun g => (hmean g).le)
  have hl := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π (fun h => -m h) hm.neg R (-1) (fun h => by simpa only [abs_neg] using hbound h)
    (fun g => by rw [integral_neg, hmean g])
  rw [integral_neg] at hl
  linarith
theorem historyMarkedReference_mass_mgf (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
     [MeasurableSpace E] [Nonempty E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m)
    (R c : ℝ) (hc : 0 ≤ c) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1)
    (hosc : ∀ g j (marks marks' : Fin (historyShapeLength dependent g) → E),
      (∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) →
        |m ⟨g, marks⟩ - m ⟨g, marks'⟩| ≤ c) (u ) :
    (∫ h, Real.exp (u * (m h - 1)) ∂historyMarkedReference dependent Δ π) ≤
      Real.exp ((Fintype.card J ) * u ^ 2 * c ^ 2 / 8) := by
  let F := fun h => Real.exp (u * (m h - 1))
  have hFb : ∀ h, |F h| ≤ Real.exp (|u| * (R + 1)) := by
    intro h
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc
      _ ≤ |u * (m h - 1)| := le_abs_self _
      _ = |u| * |m h - 1| := abs_mul _ _
      _ ≤ |u| * (R + 1) := mul_le_mul_of_nonneg_left
        (by have hh := abs_sub (m h) 1; norm_num only [abs_one] at hh; linarith [hbound h]) (abs_nonneg _)
  apply historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels π F (Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const)))
    (Real.exp (|u| * (R + 1))) _ hFb
  intro g
  have hh := label_block_centered_mgf_le (historyShapeCanonicalLabels dependent g) π
    (fun marks => m ⟨g, marks⟩) (hm.comp (historyMarked_measurable_mk dependent g)) R c hc (fun marks => hbound ⟨g, marks⟩) (hosc g) u
  rw [hmean g] at hh
  exact hh
end
def highHistoryMassParameter (d k : ℕ) (a b : ℝ) : ℝ :=
  k^d * ((2 / k)^d * (b-a))^2 / 8
section ActualPacket
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)
include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hmB hB hinit
end ActualPacket
section
variable {J : Type*} [Fintype J] [LinearOrder J]
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_invariant_law (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E X : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (f : HistoryMarked dependent E → X) (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator (fun _ : X => (1 : ℝ)))
        (f (historyMarkedAppend dependent hsymm j (h, e))) * a e ∂π = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map f (historyMarkedPrior dependent Δ t π a) =
      Measure.map f (historyMarkedReference dependent Δ π) := by
  have hi : Integrable a π := Integrable.of_bound ha.aestronglyMeasurable B
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  let := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t B ht.1 hB π a hi hcenter habound ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB) (historyReferenceRho_pos Δ).le).trans hsmall)
  let := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  let F := (f ⁻¹' S).indicator (fun _ : HistoryMarked dependent E => (1 : ℝ))
  have hzero : ∀ j h, ∫ e, F (historyMarkedAppend dependent hsymm j (h, e)) * a e ∂π = 0 := by
    intro j h
    have hFi : ∀ h : HistoryMarked dependent E, F h = S.indicator (fun _ : X => (1 : ℝ)) (f h) := by
      intro h
      by_cases hh : f h ∈ S <;> simp [F, hh]
    simp_rw [hFi]
    exact hkill j h S hS
  have h_historyMarkedPrior_invariant_observable (hF : Measurable F) (M) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) : (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
    let μ := historyMarkedReference dependent Δ π
    let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
    let f := historyMarkedExpectation dependent (historyReferenceRho Δ) μ a F
    have hs : ∀ u ∈ Icc 0 T, u * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * Δ ^ 2) := by
      intro u hu
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB)
        (historyReferenceRho_pos Δ).le).trans hsmall
    have hρ : 0 < (historyReferenceRho Δ) := historyReferenceRho_pos Δ
    have h_historyMarkedExpectation_lipschitzOn (ρ : ℝ) (hρ : 0 < ρ) (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) : LipschitzOnWith ⟨M * (ρ⁻¹ * Fintype.card J  * B * (3 / 2 ) ^ Fintype.card J), by positivity⟩
        (historyMarkedExpectation dependent ρ μ a F) (Icc 0 T) := by
      let D : ℝ := ρ⁻¹ * (Fintype.card J ) * B * (3 / 2 ) ^ Fintype.card J
      have hs : ∀ u ∈ Icc 0 T, u * B / ρ ≤ 1 / (2 + 8 * Δ ^ 2) := by
        intro u hu
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
      have hi : ∀ u ∈ Icc 0 T, Integrable (fun h => F h * historyMarkedDensity dependent ρ u a h) μ :=
        fun u hu => historyMarkedDensityObservable_integrable dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB
          μ a ha habound (hs u hu) F hF M hM hFbound
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      rw [Real.dist_eq, historyMarkedExpectation, historyMarkedExpectation, ← integral_sub (hi u hu) (hi v hv)]
      change ‖∫ h, F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h ∂μ‖ ≤
        M * D * dist u v
      have hb : ∀ᵐ h ∂μ, ‖F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h‖ ≤
          M * D * dist u v := by
        apply Eventually.of_forall
        intro h
        rw [← mul_sub, norm_mul, Real.norm_eq_abs]
        have hl := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
        rw [dist_eq_norm] at hl
        change ‖historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h‖ ≤ D * dist u v at hl
        exact (mul_le_mul_of_nonneg_right (hFbound h) (norm_nonneg _)).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl hM)
      simpa using norm_integral_le_of_norm_le_const hb
    have hl := (h_historyMarkedExpectation_lipschitzOn (historyReferenceRho Δ) hρ hsmall)
    have hAC : AbsolutelyContinuousOnInterval f 0 T :=
      (by rw [← uIcc_of_le hT] at hl; exact hl.absolutelyContinuousOnInterval)
    have hn0 : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
    have hnT : ∀ᵐ u : ℝ, u ≠ T := by rw [ae_iff]; simp
    have hzero : ∀ᵐ u : ℝ, u ∈ uIcc 0 T → HasDerivAt f 0 u := by
      filter_upwards [hn0, hnT] with u hu0 huT hu
      rw [uIcc_of_le hT] at hu
      have h_historyMarkedExpectation_weak_transport : HasDerivAt (historyMarkedExpectation dependent (historyReferenceRho Δ)
        (historyMarkedReference dependent Δ π) a F)
        (historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) u
          (historyMarkedReference dependent Δ π) π a F) u := by
        have ht : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have htT : u < T := lt_of_le_of_ne hu.2 huT
        let := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
        have hd := (historyMarkedExpectation_hasDerivAt dependent hrefl hsymm Δ hlabels
          (historyReferenceRho Δ) T B u (historyReferenceRho_pos Δ) ht htT hB
          (historyMarkedReference dependent Δ π) a ha habound hsmall F hF M hM hFbound).2
        rw [historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
          u B ht.le hB π a ha habound ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htT.le hB) (historyReferenceRho_pos Δ).le).trans hsmall) F hF M hM hFbound] at hd
        exact hd
      have hd := h_historyMarkedExpectation_weak_transport
      have h_historyMarkedGeneratorExpectation_eq_zero : historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) u
        (historyMarkedReference dependent Δ π) π a F = 0 := by
        have hsmall : u * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * Δ ^ 2) := hs u hu
        let μ := historyMarkedReference dependent Δ π
        let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
        unfold historyMarkedGeneratorExpectation
        apply Finset.sum_eq_zero
        intro j hj
        let G := fun p =>
          F (historyMarkedAppend dependent hsymm j p) * a p.2 *
            historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1
        have hG : Measurable G :=
          ((hF.comp (historyMarkedAppend_measurable dependent hsymm j)).mul (ha.comp measurable_snd)).mul
            ((historyMarkedDensity_measurable dependent _ u a ha).comp measurable_fst)
        have hInt : Integrable G (μ.prod π) := by
          apply Integrable.of_bound hG.aestronglyMeasurable (M * B * (3 / 2 ) ^ Fintype.card J)
          apply Eventually.of_forall
          intro p
          change ‖F (historyMarkedAppend dependent hsymm j p) * a p.2 *
            historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
            (historyReferenceRho Δ) u B (historyReferenceRho_pos Δ) hu.1 hB a habound hsmall p.1
          have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1 :=
            (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
          rw [abs_of_nonneg hp]
          exact mul_le_mul (mul_le_mul (hFbound _) (habound _) (abs_nonneg _) hM) hb.2 hp (mul_nonneg hM hB)
        change (∫ p, G p ∂μ.prod π) = 0
        rw [integral_prod G hInt]
        have hin : ∀ h, ∫ e, G (h, e) ∂π = 0 := by
          intro h
          dsimp only [G]
          rw [integral_mul_const, hzero j h, zero_mul]
        simp_rw [hin]
        exact integral_zero _ _
      rw [h_historyMarkedGeneratorExpectation_eq_zero] at hd
      exact hd
    obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hzero
    have hft : f t = f 0 := (hC t (by simpa only [uIcc_of_le hT] using ht)).trans
      (hC 0 (by simp only [uIcc_of_le hT, mem_Icc]; exact ⟨le_rfl, hT⟩)).symm
    rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
      t B ht.1 hB π a ha habound (hs t ht) F]
    change f t = _
    rw [hft]
    have h_historyMarkedDensity_zero ρ (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensity dependent ρ 0 a h = 1 := by
      unfold historyMarkedDensity historyScaledUpperDensity
      exact historyUpperDensity_at_zero _ _
    simp [f, μ, historyMarkedExpectation, h_historyMarkedDensity_zero]
  have he := (h_historyMarkedPrior_invariant_observable ((measurable_const : Measurable (fun _ : HistoryMarked dependent E => (1 : ℝ))).indicator (hf hS)) 1 (by norm_num) (by intro h; by_cases hh : f h ∈ S <;> simp [F, hh]))
  change (∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
    ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
        ∂historyMarkedReference dependent Δ π at he
  rw [integral_indicator_one (hf hS), integral_indicator_one (hf hS)] at he
  exact he
end
theorem highNeighbor_dependency_card (d k ) [NeZero k] (j ) :
    (dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j).card ≤ 3^d := by
  have he : dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j =
      highNeighborLabels d k j := by
    ext i
    simp [dependentLabelFinset]
  rw [he]
  exact highNeighborLabels_card_le d k j
theorem massPowerTilt_abs_event_eq_of_massLaw  [MeasurableSpace Ω]
    (μ ν : Measure Ω) (m ) (hm : Measurable m) (n )
    (hlaw : μ.map m = ν.map m) (ε ) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} =
      (massPowerTilt ν m n).real {ω | ε < |m ω - 1|} := by
  have hS : MeasurableSet {z : ℝ | ε < |z - 1|} :=
    measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)
  have h_massPowerTilt_massLaw_eq : (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
    unfold massPowerTilt
    rw [massPowerNormalizer_eq_of_massLaw μ ν m hm n hlaw]
    have hf : Measurable (fun x => ENNReal.ofReal (x ^ n / massPowerNormalizer ν m n)) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.pow_const n).div_const _)
    rw [map_withDensity_pullback μ m hm _ hf, map_withDensity_pullback ν m hm _ hf, hlaw]
  have he := congrArg (fun μ' => μ' {z : ℝ | ε < |z - 1|})
    h_massPowerTilt_massLaw_eq
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS] at he
  exact congrArg ENNReal.toReal he
section ActualMassLaw
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (initial : HighRawState d k F) (hi : Measurable initial.1)
  (T : ℝ) (hT : 0 ≤ T)
  (hsmall : T * (highPacketMarkMass σ a b m r D q C A / δ) / historyReferenceRho (3^d) ≤
    1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))
include hA hcost hpos hδ hδ1 hmB hi hT hsmall
variable (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδlt : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1) (hinit : ∀ x, initial.1 x = 1)
include ha hab hr hδlt hR ha1 hb1 hW hδW hB hinit
end ActualMassLaw
section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
include G hpos
theorem highUnionSourceActivation_bound (e ) :
    |highUnionActivation R (highCenterMix C) e| ≤
      highRowTotalMass R.rowMass / highCenterMix C :=
  highCenteredRowUnionActivation_bound R.rowMass hpos G.total_positive R.rowActivation
    G.activation_bound _ (highCenterMix_mem C).1 e
theorem highUnionSourceActivation_centered :
    (∫ e, highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  letI := G.row_probability
  exact highUnionActivation_centered R G.mass_nonneg G.activation_measurable
    (fun i => Integrable.of_bound (G.activation_measurable i).aestronglyMeasurable (R.rowMass i)
      (Filter.Eventually.of_forall (fun e => by simpa only [Real.norm_eq_abs] using G.activation_bound i e)))
    G.activation_centered _ (highCenterMix_mem C).1 (highCenterMix_mem C).2.le
theorem highUnionSourcePrior_probability (T ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2)) (t ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  have hB  :=
    div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hi : Integrable (highUnionActivation R (highCenterMix C))
      (highUnionLaw R (highCenterMix C)) :=
    Integrable.of_bound (highUnionActivation_measurable R G.activation_measurable (highCenterMix C)).aestronglyMeasurable _ (Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using highUnionSourceActivation_bound C R G hpos e)
  have hs : t * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB)
      (historyReferenceRho_pos _).le).trans hsmall
  exact historyMarkedPrior_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : ↑1 ≤ 3)) (highNeighbor_dependency_card d k)
    t _ ht.1 hB _ _ hi (highUnionSourceActivation_centered C R G hpos)
    (highUnionSourceActivation_bound C R G hpos) hs
theorem highUnionSourceMass_prior_law_of_append_annihilation (T ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))
    (hkill : ∀ j h S, MeasurableSet S →
      (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
        (highUnionSourceMass C R (historyMarkedAppend
          (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
        highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0)
    (t ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C R)
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) =
    Measure.map (highUnionSourceMass C R)
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact historyMarkedPrior_invariant_law _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : 1 ≤ 3)) (highNeighbor_dependency_card d k)
    T _ hT (div_nonneg G.total_positive.le (highCenterMix_mem C).1.le)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
    (highUnionActivation_measurable R G.activation_measurable _)
    (highUnionSourceActivation_centered C R G hpos) (highUnionSourceActivation_bound C R G hpos)
    hsmall _ (highUnionSourceMass_measurable C R G) hkill t ht
end Generic
section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN
end ActualFinePair
section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
def highUnionSourceRegression (η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ :=
  highFrameField d k η (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)) x
theorem highUnionSourceRegression_joint_measurable [∀ i, StandardBorelSpace (E i)]
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R) (η : ℝ) :
    Measurable (fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceRegression C R η hx.1 hx.2) :=
by
  let Ω := HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
    (HighUnionMark E)
  have h_highUnionSourceState_measurable  := historyMarkedRawState_measurable (fun i j => j ∈ highNeighborLabels d k i)
    (highUnionRawUpdate R (highCenterMix C))
    (fun j => highUnionRawUpdate_measurable R G.slope_measurable G.intercept_measurable
      G.vector_measurable G.time_measurable (highCenterMix C) j) highUnionVacuum
  have h_highFrameField_joint_measurable (c : Ω → HighWindowLabels d k → HighFrameIndex d F → ℝ) (hc : Measurable c) : Measurable (fun ωx : Ω × Covariate d =>
      highFrameField d k η (fun j => highFramePolynomial (c ωx.1 j)) ωx.2) := by
    simp_rw [highFrameField_finite_evaluation]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro γ hγ
    have hchart : Measurable (fun ωx : Ω × Covariate d =>
        highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) ωx.2) :=
      (highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (highFrameMonomial γ))
        (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).continuous.measurable.comp
          measurable_snd
    exact (((measurable_pi_apply γ).comp ((measurable_pi_apply j).comp hc)).comp measurable_fst).mul hchart
  exact h_highFrameField_joint_measurable (fun h => (highUnionSourceState C R h).2) (measurable_snd.comp h_highUnionSourceState_measurable)
end
theorem highMarkedLocalScore_sum_of_partition {J ι E : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {n : ℕ}
    (π : J → Measure E) (activation : J → E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : J → E → Fin n → ℝ)
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (hpartition : ∀ i, ∑ j, (w j i)^2 = 1) (y : Fin n → Fin 3) :
    (∑ j, highMarkedLocalScore (π j) (activation j) a V η p (pReset j)
      (cReset j) (g j) (w j) (φ j) (c j) y) =
    ((∑ j, highMarkedResponseAction (π j) (activation j) a V η
      (pReset j) (cReset j) (g j) (w j) (φ j) y) -
      η^2*(∏ i, p i)*∑ i, ternaryVarianceDerivative a (y i)*
        ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f l) V (y l)) /
      ((∏ i, p i)*∏ i, ternaryMass a (f i) V (y i)) := by
  unfold highMarkedLocalScore highResponseProduct highResponseVarianceTerm
  simp_rw [hreg]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  congr 2
  calc
    (∑ j, η^2*(∏ i, p i)*∑ i, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l))) =
      η^2*(∏ i, p i)*∑ j, ∑ i, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l)) := by rw [Finset.mul_sum]
    _ = η^2*(∏ i, p i)*∑ i, ∑ j, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l)) := by rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, hpartition, one_mul]
lemma highLocalFieldWithout_update (d k D ) [NeZero k] (η c j u x) :
    highLocalFieldWithout d k D η (Function.update c j u) j x =
      highLocalFieldWithout d k D η c j x := by
  apply congrArg (fun v => η*v)
  apply Finset.sum_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]
lemma highFrameField_update_coefficientRegression (d k D n ) [NeZero k] (hk : 4 ≤ k)
    (η c j u)
    (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) u =
      fun i => highFrameField d k η (fun l => highFramePolynomial (Function.update c j u l)) (x i) := by
  simpa only [Function.update_self, highLocalFieldWithout_update] using (highFrameField_coefficientRegression d k D n hk η (Function.update c j u) j x)
section ActualSource
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k D I E)
lemma highUnionSourceRegression_append (n ) (hk : 4 ≤ k) (η j h e) (x : Fin n → Covariate d) :
    coefficientRegression η
      (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i))
      (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) =
      fun i => highUnionSourceRegression C R η
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) (x i) := by
  unfold highUnionSourceRegression
  have h_highUnionSourceState_append_coefficients : (highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))).2 =
      Function.update (highUnionSourceState C R h).2 j
        (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) := by
    rw [highUnionSourceState_append R C j h e]
    rfl
  rw [h_highUnionSourceState_append_coefficients]
  exact highFrameField_update_coefficientRegression d k D n hk η _ j _ x
def highUnionSourceLocalScore (n ) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highFrameMarkedScore d k D n
    (fun _ => highUnionLaw R (highCenterMix C))
    (fun _ => highUnionActivation R (highCenterMix C)) a V η
    (fun i => highUnionSourceDensity C R h (x i))
    (fun l e i => highUnionSourceDensity C R
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) l (h,e)) (x i))
    (fun l e => highUnionResponseReset R e ((highUnionSourceState C R h).2 l))
    (highUnionSourceState C R h).2 x j y
theorem highUnionSourceLikelihoodScore_eq_sum (n ) (hk : 4 ≤ k) (a V η h x) (y : Fin n → Fin 3) :
    highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η) h (x,y) =
      ∑ j, highUnionSourceLocalScore C R n a V η h x j y := by
  simp only [highUnionSourceLocalScore, highFrameMarkedScore]
  have h_highPeriodicTensor_sq_partition (hk : 2 ≤ k) (x : Covariate d) : (∑ j : HighWindowLabels d k, highPeriodicTensor d k j x ^ 2) = 1 := by
    simp only [highPeriodicTensor, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i (j : ZMod k) => highPeriodicWindow k j (x i) ^ 2)]
    simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]
  rw [highMarkedLocalScore_sum_of_partition
    (hreg := fun j => highFrameField_coefficientRegression d k D n hk η
      (highUnionSourceState C R h).2 j x)
    (hpartition := fun i => (h_highPeriodicTensor_sq_partition (by omega) (x i)))]
  have h_highUnionSourceAppendLikelihoodAction_eq_responseAction (j : HighWindowLabels d k) (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) (x : Fin n → Covariate d) (y : Fin n → Fin 3) : highAppendLikelihoodAction (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
        n a V (highUnionSourceDensity C R) (highUnionSourceRegression C R η) j h (x,y) =
      highMarkedResponseAction (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) a V η
        (fun e i => highUnionSourceDensity C R
          (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
            (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) (x i))
        (fun e => highUnionResponseReset R e ((highUnionSourceState C R h).2 j))
        (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
        (fun i => highPeriodicTensor d k j (x i))
        (fun i => highLocalFrameFeature k j (x i)) y := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun e => by
      dsimp only
      unfold highRawSampleLikelihood
      rw [Finset.prod_mul_distrib]
      unfold highResponseProduct
      rw [highUnionSourceRegression_append C R n hk η j h e x]
      exact (mul_assoc _ _ _).symm
  unfold highHistoryLikelihoodScore highHistoryLikelihoodDerivative
  simp_rw [h_highUnionSourceAppendLikelihoodAction_eq_responseAction]
  unfold highRawSampleLikelihood highRawSampleVarianceDerivative highUnionSourceRegression
  rw [Finset.prod_mul_distrib]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end ActualSource
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
def highUnionSourceResetDensity (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highUnionSourceDensity C R (historyMarkedAppend
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) x
def highUnionSourceResetCoefficient (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) : HighFrameIndex d D → ℝ :=
  highUnionResponseReset R e ((highUnionSourceState C R h).2 j)
include G in
theorem highUnionSourceDensity_coarse_interval
    (h x) : C.densityLower ≤ highUnionSourceDensity C R h x ∧
      highUnionSourceDensity C R h x ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_interval C R G h x
  have hM : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  constructor <;> linarith [hb.1,hb.2,one_div_pos.mpr hM]
include G in
theorem highUnionSourceResetDensity_measurable (j h) :
    Measurable (Function.uncurry (highUnionSourceResetDensity C R j h)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  have ha : Measurable (fun ex : HighUnionMark E × Covariate d =>
      historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,ex.1)) :=
    (historyMarkedAppend_measurable (E := HighUnionMark E)
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j).comp
      (measurable_const.prodMk measurable_fst)
  exact (highUnionSourceDensity_joint_measurable C R G).comp (ha.prodMk measurable_snd)
include G in
theorem highUnionSourceResetDensity_abs_le (j h e x) :
    |highUnionSourceResetDensity C R j h e x| ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_coarse_interval C R G
    (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) x
  rw [highUnionSourceResetDensity,abs_of_nonneg (C.densityLower_pos.le.trans hb.1)]
  exact hb.2
include G in
theorem highUnionSourceResetCoefficient_measurable (j h γ) :
    Measurable (fun e => highUnionSourceResetCoefficient C R j h e γ) := by
  exact (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
    measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
      (highUnionResponseVector_measurable R G.vector_measurable γ))
theorem highUnionSourceResetDensity_outside (j h e x) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceResetDensity C R j h e x = highUnionSourceDensity C R h x :=
  highUnionSourceDensity_append_of_not_mem R C j h e x hx
end NearlyMinimax
