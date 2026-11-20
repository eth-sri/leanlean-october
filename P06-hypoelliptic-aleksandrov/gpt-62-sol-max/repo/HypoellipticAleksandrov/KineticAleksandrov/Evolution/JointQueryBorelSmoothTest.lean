module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelJointTest

/-! # Jointly measurable smooth ambient test integrals

Increasing compact time-state cutoffs exhaust the actual moving graph. Their integrals
are jointly measurable, and dominated convergence removes the cutoffs using the support of the
terminal measures.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "μT" => terminalMeasure data
local notation "κ" => terminalFiberKernel data

local notation "P₀" => terminalOperators data

/-- Integrals of arbitrary bounded ambient smooth probes against the terminal measures
are jointly measurable, without any terminal-support premise on the probe. -/
theorem measurable_integral_terminal_smooth
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Measurable (fun q : EvolutionQuery Ω γ => ∫ x, F x ∂(μT q)) := by
  obtain ⟨χ, hχ, hb, _, hcover⟩ := exists_increasing_smooth_interior_cutoffs
    (isOpen_terminal_state_graph (isOpen_of_isAdmissibleEvolutionDomain data.domain) data.curve.1)
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  have hbound (j : ℕ) (z : ℝ × EvolutionAmbientState n) : |χ j z * F z.2| ≤ C := by
    rw [abs_mul, abs_of_nonneg (hb j z).1]
    exact (mul_le_mul_of_nonneg_right (hb j z).2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hC z.2)
  let Φ (j : ℕ) : BoundedBorel (ℝ × EvolutionAmbientState n) :=
    ⟨fun z => χ j z * F z.2,
      ((hχ j).1.continuous.measurable.mul (F.measurable.comp measurable_snd)),
      ⟨C, hC0, hbound j⟩⟩
  have hΦr (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Φ j) :=
    (hχ j).1.mul (hF.comp contDiff_snd)
  have hΦc (j : ℕ) : HasCompactSupport (Φ j) := (hχ j).2.1.mul_right
  have hΦs (j : ℕ) : tsupport (Φ j) ⊆
      {z : ℝ × EvolutionAmbientState n | z.2 ∈ evolutionStateSet Ω γ z.1} :=
    tsupport_mul_subset_left.trans (hχ j).2.2
  apply measurable_of_tendsto_metrizable
    (fun j => measurable_joint_terminal_probe data (Φ j) (hΦr j) (hΦc j) (hΦs j))
  apply tendsto_pi_nhds.mpr
  intro q
  have hspec := terminalMeasure_spec data q
  have : IsFiniteMeasure (μT q) := ⟨hspec.1.trans_lt ENNReal.one_lt_top⟩
  have hU : MeasurableSet (evolutionStateSet Ω γ q.1.2.1) :=
    measurableSet_evolutionStateSet_of_isOpen (isOpen_of_isAdmissibleEvolutionDomain data.domain)
  have ha : ∀ᵐ x ∂(μT q), x ∈ evolutionStateSet Ω γ q.1.2.1 := by
    apply ae_iff.mpr
    change (μT q) (evolutionStateSet Ω γ q.1.2.1)ᶜ = 0
    rw [← hspec.2.1, Measure.restrict_apply hU.compl]
    simp only [Set.compl_inter_self, measure_empty]
  apply tendsto_integral_of_dominated_convergence
    (F := fun j x => Φ j (q.1.2.1, x)) (f := fun x => F x) (fun _ => C)
    (fun j => ((Φ j).measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      change |χ j (q.1.2.1, x) * F x| ≤ C
      exact hbound j (q.1.2.1, x))
  filter_upwards [ha] with x hx
  obtain ⟨N, hN⟩ := hcover (q.1.2.1, x) hx
  apply tendsto_const_nhds.congr'
  apply eventually_atTop.mpr
  refine ⟨N, fun j hj => ?_⟩
  change F x = χ j (q.1.2.1, x) * F x
  rw [hN j hj, one_mul]

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
