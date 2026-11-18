module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
section

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- **Parabolic Duhamel lemma** (Lemma 2.3), without the transport data. -/
theorem parabolic_duhamel (hH : HormanderHypoellipticityStatement)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel Ω γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) (zIndependentCoefficient B) K)
    (T : ℝ) (g : TimeVelocity d → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1}) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1} ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        0 ≤ parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ∧
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ≤
          (T - p.1) * ⨆ q, g q) ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        scalarParabolicOperator B (fun _ _ => 0)
          (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
          p = -g p) ∧
      ContinuousOn
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 ≤ T ∧ p.2 ∈ closure (movingDomain Ω γ p.1)} ∧
      (∀ p : TimeVelocity d, p.1 = T →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p = 0) ∧
      (∀ p : TimeVelocity d, p.2 ∈ frontier (movingDomain Ω γ p.1) →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p =
          0) := by
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hγc : Continuous γ := hγ.1
  obtain ⟨hsmooth, heq⟩ := duhamel_smooth_equation K hH hΩ hγc hB hP g hg0 hgs hgc T hgU
  have hg : ∀ r, Measurable (fun v => g (r, v)) := fun r =>
    hgs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hbdd : BddAbove (range g) := ⟨C, by
    rintro _ ⟨p, rfl⟩
    exact (le_abs_self _).trans (by simpa using hC p)⟩
  have hgb : ∀ p, g p ≤ ⨆ q, g q := fun p => le_ciSup hbdd p
  refine ⟨hsmooth, fun p hp => ⟨parabolicDuhamelPotential_nonneg K hΩm T g hg hg0 p,
    parabolicDuhamelPotential_le K hΩm T g hg hg0 _ hgb p hp.1.le⟩, heq,
    continuousOn_duhamelPotential K hΩ hγc hP g hg0 hgs hgc T hgU,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_terminal_le K hΩm T g p hp.ge,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_not_mem K hΩm T g p ?_⟩
  rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩ p.1).frontier_eq] at hp
  exact hp.2

end

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

variable {d : ℕ}

/-- **Proposition 4.2.** -/
theorem occupation_potential (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      (zIndependentCoefficient B) K)
    (F : TimeVelocity d → ℝ) (hF0 : ∀ p, 0 ≤ F p) (hFs : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) :
    (∀ p, 0 ≤ parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F p) ∧
      BddAbove ((parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) ''
          (Icc (0 : ℝ) 1 ×ˢ univ)) ∧
      sSup ((parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) ''
          (Icc (0 : ℝ) 1 ×ˢ univ)) ≤ ⨆ z, F z ∧
      (∀ v, parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F (1, v) = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F)
        {p : TimeVelocity d | p.1 < 1} ∧
      ∀ p : TimeVelocity d, p.1 < 1 →
        scalarParabolicOperator B (fun _ _ => 0) (parabolicDuhamelPotential K
          (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) p =
          -F p := by
  have hΩ := wholeSpace_admissible d
  have hγ := zeroCurve_piecewiseC1 d
  have hU : tsupport F ⊆ {p : TimeVelocity d | p.1 < 1 ∧
      p.2 ∈ movingDomain (wholeSpace d) (fun _ => 0) p.1} := by
    intro p hp
    have := hFsupp hp
    exact ⟨this.1.2, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩
  obtain ⟨hsm, -, heq, -, -, -⟩ := parabolic_duhamel hH hΩ hγ hB K hP 1 F hF0 hFs hFc hU
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hg : ∀ r, Measurable (fun v => F (r, v)) := fun r =>
    hFs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  have hbdd : BddAbove (range F) := ⟨C, by
    rintro _ ⟨p, rfl⟩
    exact (le_abs_self _).trans (by simpa using hC p)⟩
  have hgb : ∀ p, F p ≤ ⨆ q, F q := fun p => le_ciSup hbdd p
  have hsup0 := (hF0 (0, 0)).trans (hgb _)
  have hle : ∀ p : TimeVelocity d, p.1 ∈ Icc 0 1 →
      parabolicDuhamelPotential K hΩm 1 F p ≤ ⨆ q, F q := by
    intro p hp
    refine (parabolicDuhamelPotential_le K hΩm 1 F hg hF0 _ hgb p hp.2).trans ?_
    exact mul_le_of_le_one_left hsup0 (by linarith [hp.1])
  refine ⟨fun p => parabolicDuhamelPotential_nonneg K hΩm 1 F hg hF0 p, ?_, ?_,
    fun v => parabolicDuhamelPotential_eq_zero_of_terminal_le K hΩm 1 F (1, v) le_rfl, ?_, ?_⟩
  · exact ⟨⨆ q, F q, by
      rintro _ ⟨p, hp, rfl⟩
      exact hle p hp.1⟩
  · refine csSup_le ⟨_, ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩⟩ ?_
    rintro _ ⟨p, hp, rfl⟩
    exact hle p hp.1
  · exact hsm.mono fun p hp => ⟨hp, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩
  · intro p hp
    exact heq p ⟨hp, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

