module

public import RequestProject.Defs
public import RequestProject.Counting

/-!
# The Neumann spectrum (Section 3 of the paper)
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

variable (Ω : Set ℂ)

/-- Every subspace of dimension `j + 2` contains a subspace of dimension `j + 1`. -/
lemma exists_submodule_finrank_succ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (j : ℕ) (hS : Module.finrank ℂ S = j + 2) :
    ∃ T : Submodule ℂ V, T ≤ S ∧ Module.finrank ℂ T = j + 1 := by
  haveI : Module.Finite ℂ S := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq ℂ S hS
  let v : Fin (j + 1) → V := fun i => b (Fin.castSucc i)
  refine ⟨Submodule.span ℂ (Set.range v), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castSucc i)).2
  · rw [finrank_span_eq_card (by
    exact (b.linearIndependent.comp _ (Fin.castSucc_injective _)).map' S.subtype (Submodule.ker_subtype S))]; simp

/-- The min–max values are nondecreasing: `μ_j ≤ μ_{j+1}`. -/
lemma neumannEigenvalue_le_succ (j : ℕ) :
    neumannEigenvalue Ω j ≤ neumannEigenvalue Ω (j + 1) := by
  refine le_iInf₂ fun S hS => ?_
  obtain ⟨T, hTS, hT⟩ := exists_submodule_finrank_succ S j (by assumption)
  refine (iInf₂_le T hT).trans ?_
  exact iSup₂_mono' fun u hu => ⟨u, hTS hu, le_rfl⟩

/-- Lemma 3.3 (ordering): the Neumann eigenvalues are nondecreasing. -/
lemma neumannEigenvalue_monotone : Monotone (neumannEigenvalue Ω) :=
  monotone_nat_of_le_succ (neumannEigenvalue_le_succ Ω)

/-- The weak gradient of a constant function is zero. -/
lemma isWeakGradient_const [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    IsWeakGradient Ω (Lp.const 2 (volume.restrict Ω) c) 0 := by
  intro φ hφ i
  obtain ⟨hsmooth, hcpt, hsupp⟩ := hφ
  have hzero : (fun w => (0 : Fin 2 → L2 Ω) i w * φ w) =ᵐ[volume.restrict Ω]
      fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    simp_all
  rw [integral_congr_ae hzero]
  have hconst : (fun w => Lp.const 2 (volume.restrict Ω) c w *
      fderiv ℝ φ w (coordDir i)) =ᵐ[volume.restrict Ω]
      fun w => c * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [Lp.coeFn_const 2 (volume.restrict Ω) c] with w hw
    simp_all
  rw [integral_congr_ae hconst, integral_const_mul]
  have hsub : ∫ w in Ω, fderiv ℝ φ w (coordDir i) = ∫ w, fderiv ℝ φ w (coordDir i) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have  := fun h => hw (hsupp h)
    simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
  have hcont : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    ((hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const :)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _  => 1)  
    (by simp) (by simpa using hcont.integrable_of_hasCompactSupport (hcpt.fderiv_apply (𝕜 := ℝ) _))
    (by simpa using hsmooth.continuous.integrable_of_hasCompactSupport hcpt)
    (fun _ _ => differentiableAt_const _) (fun x _ => hsmooth.differentiable (by simp) x)
  simp_all

/-- The energy of a constant function is zero. -/
lemma neumannEnergy_const [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    neumannEnergy Ω (Lp.const 2 (volume.restrict Ω) c) = 0 := by
  apply le_antisymm _ (zero_le)
  refine (iInf₂_le 0 (isWeakGradient_const Ω c)).trans ?_
  simp

/-- Lemma 3.3: `μ_0(Ω) = 0` for a nonempty bounded open set. -/
theorem neumannEigenvalue_zero (Ω : Set ℂ) (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) : neumannEigenvalue Ω 0 = 0 := by
  haveI : Fact (volume Ω < ⊤) := ⟨hb.measure_lt_top⟩
  apply le_antisymm _ (zero_le)
  have hpos  := hΩ.measure_pos volume hne
  refine (iInf₂_le (ℂ ∙ Lp.const 2 (volume.restrict Ω) 1) (by
    rw [finrank_span_singleton (by
    intro h
    have h1 : ‖Lp.const 2 (volume.restrict Ω) (1 : ℂ)‖ = 0 := by simp_all
    haveI : NeZero (volume.restrict Ω) := ⟨by
      intro h0
      simp_all⟩
    rw [Lp.norm_const 2 (volume.restrict Ω) 1 (by norm_num)] at h1
    have : (volume.restrict Ω).real Set.univ ≠ 0 := by
      rw [measureReal_def, Measure.restrict_apply_univ]
      exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hb.measure_lt_top.ne⟩
    simp_all)])).trans ?_
  refine iSup₂_le fun u hu => iSup_le fun _ => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have : a • Lp.const 2 (volume.restrict Ω) 1 = Lp.const 2 (volume.restrict Ω) a := by
    ext1
    filter_upwards [Lp.coeFn_smul a (Lp.const 2 (volume.restrict Ω) (1 : ℂ)),
      Lp.coeFn_const 2 (volume.restrict Ω) (1 : ℂ),
      Lp.coeFn_const 2 (volume.restrict Ω) a] with w h1 h2 h3
    simp_all
  simp [rayleigh, this, neumannEnergy_const]

end PolyaNeumann

end
