module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Smooth compactly supported probes are uniformly dense in `C_c` of an open fiber

For an open set `U` of a finite-dimensional real normed space, every compactly supported
continuous function on the subtype `U` is within any `ε > 0` (uniformly on `U`) of a smooth
function on the whole space with compact support inside `U`.  The proof extends by zero,
convolves with a normed bump function of small radius, and uses uniform continuity of the
extension.  The terminal-evolution form (`exists_smooth_terminal_test_close`) packages the
approximant as a `BoundedBorel` smooth compact terminal datum on the open state fiber.
-/

 public section



open Set MeasureTheory Metric Function
  HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped CompactlySupported Convolution Pointwise ContDiff MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The extension by zero of a compactly supported continuous function on an open subtype is
continuous, with compact support. -/
theorem extendByZero_continuous_hasCompactSupport {U : Set E} (hU : IsOpen U) (f : C_c(U, ℝ)) :
    Continuous (Subtype.val.extend (f : U → ℝ) 0) ∧
      HasCompactSupport (Subtype.val.extend (f : U → ℝ) 0) :=
  ⟨f.hasCompactSupport.continuous_extend_zero hU f.continuous,
    f.hasCompactSupport.extend_zero continuous_subtype_val⟩

/-- Smooth uniform approximation of a compactly supported continuous function on an open
subset by a smooth function with compact support inside the subset. -/
theorem exists_smooth_compactSupport_close {U : Set E} (hU : IsOpen U) (f : C_c(U, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : E → ℝ, ContDiff ℝ PDE.smoothOrder φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      ∀ x : U, |φ x - f x| ≤ ε := by
  set g : E → ℝ := Subtype.val.extend (f : U → ℝ) 0 with hg
  obtain ⟨hgc, hgs⟩ := extendByZero_continuous_hasCompactSupport hU f
  have hgx : ∀ x : U, g x = f x := (Subtype.val_injective.extend_apply _ _)
  set K : Set E := Subtype.val '' tsupport (f : U → ℝ) with hKdef
  have hKc  := f.hasCompactSupport.isCompact.image continuous_subtype_val


  obtain ⟨δ0, hδ0, hthick⟩ := hKc.exists_cthickening_subset_open hU (show K ⊆ U by
      rintro _ ⟨x, -, rfl⟩
      exact x.2)
  obtain ⟨δ1, hδ1, hδ1g⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) ε hε
  set r : ℝ := min δ0 δ1 with hr
  have hrpos : 0 < r := lt_min hδ0 hδ1
  set φb : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hrpos, half_lt_self hrpos⟩ with hφb
  set μ : Measure E := Measure.addHaar with hμ


  have hconv_supp : HasCompactSupport ((φb.normed μ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) :=
    φb.hasCompactSupport_normed.convolution _ hgs


  refine ⟨_, (φb.hasCompactSupport_normed.contDiff_convolution_left _ φb.contDiff_normed hgc.locallyIntegrable), hconv_supp, ?_, ?_⟩
  · refine (show tsupport ((φb.normed μ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) ⊆
      closedBall (0 : E) r + K by
      refine closure_minimal ?_ ((isCompact_closedBall (0 : E) r).add hKc).isClosed
      refine (support_convolution_subset _).trans (add_subset_add ?_ ?_)
      · exact subset_tsupport _ |>.trans (φb.tsupport_normed_eq (μ := μ)).subset
      · exact subset_tsupport _ |>.trans (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val)).trans ?_
    rintro _ ⟨a, ha, k, hk, rfl⟩
    refine hthick (mem_cthickening_of_dist_le (a + k) k δ0 K hk ?_)
    have : dist (a + k) k = ‖a‖ := by simp [dist_eq_norm]
    rw [this]
    exact (mem_closedBall_zero_iff.mp ha).trans (min_le_left _ _)
  · intro x
    rw [← hgx x]
    have := φb.dist_normed_convolution_le (μ := μ) (x₀ := (x : E)) (ε := ε)
      hgc.aestronglyMeasurable (fun y hy => (hδ1g (lt_of_lt_of_le (mem_ball.mp hy)
        (min_le_right _ _))).le)
    rw [Real.dist_eq] at this
    exact this

end General

section Outside

/-- Smooth compactly supported terminal data approximate every compactly supported continuous
test on the open terminal fiber uniformly, for an admissible base domain.  This is the
outside-context form of `exists_smooth_terminal_test_close`, and needs only openness. -/
theorem exists_smooth_terminal_test_close_of_isOpen {n : ℕ} {Ω : PDE.VelocityRegion n}
    (hΩ : IsOpen Ω) (γ : ℝ → PDE.Vec n) (τ : ℝ) (f : C_c(EvolutionState Ω γ τ, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : BoundedBorel (EvolutionAmbientState n),
      IsSmoothCompactTerminalDatum Ω γ τ F ∧
      ∀ p : EvolutionState Ω γ τ, |F p.1 - f p| ≤ ε := by

  obtain ⟨φ, hφs, hφc, hφU, hφε⟩ := exists_smooth_compactSupport_close ((isOpen_movingDomain hΩ τ).prod isOpen_univ) f ε hε
  have hcont  := hφs.continuous
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hcont
  refine ⟨⟨φ, hcont.measurable, ⟨max C 0, le_max_right _ _,
    fun x => (hC x).trans (le_max_left _ _)⟩⟩, ⟨hφs, hφc, hφU⟩, hφε⟩

end Outside



end HypoellipticAleksandrov.KineticAleksandrov
