module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitLinear
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalOperator

/-! # Compact terminal cutoffs recover the lost parabolic mass

The supersolution is an internal comparison argument. Compact smooth terminal data
are constructed here, so no additional terminal-solver input is assumed.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Set MeasureTheory
open SectionTwo Decay

/-- A smooth positive supersolution dominating one on the lateral face bounds
lost marginal mass. Every supersolution premise is discharged by the exponential barrier. -/
theorem ballExit_marginal_loss_le {d : ℕ} {lam Lam R σ τ : ℝ}
    (v₀ : PDE.Vec d) (hR : 0 < R) (hστ : σ < τ)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.euclideanBall v₀ R) stationary
      (PDE.isOpen_euclideanBall v₀ R).measurableSet (zIndependentCoefficient B) K)
    (Ψ : TimeVelocity d → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨpos : ∀ p ∈ scalarParabolicClosedCylinder σ τ (PDE.euclideanBall v₀ R), 0 ≤ Ψ p)
    (hΨop : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      scalarParabolicOperator B 0 Ψ p ≤ 0)
    (hΨlat : ∀ p ∈ scalarParabolicLateralFace σ τ (PDE.euclideanBall v₀ R), 1 ≤ Ψ p)
    (v : PDE.Vec d) (hv : v ∈ PDE.euclideanBall v₀ R) :
    1 - (parabolicMarginalKernel K (PDE.isOpen_euclideanBall v₀ R).measurableSet
      σ τ hστ.le ⟨v, by simpa using hv⟩).real univ ≤
        Ψ (σ, v) := by
  let D := PDE.euclideanBall v₀ R
  let hD := (PDE.isOpen_euclideanBall v₀ R).measurableSet
  let y : EvolutionPosition D stationary σ :=
    ⟨v, by simpa using hv⟩
  let μ := parabolicMarginalKernel K hD σ τ hστ.le y
  have := isFiniteKernel_parabolicMarginalKernel K hD σ τ hστ.le
  obtain ⟨Q, _hfirst, _hid, _hpos, _hsub, _hcomp, hrepr,
    _hmeas, _hend, _hkc, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  have hεbound : ∀ ε : ℝ, 0 < ε → 1 - Ψ (σ, v) - ε ≤ μ.real univ := by
    intro ε hε
    let C  := closure D ∩ {w | ε ≤ 1 - Ψ (τ, w)}
    have hclosed : IsClosed {w : PDE.Vec d | ε ≤ 1 - Ψ (τ, w)} :=
      isClosed_le continuous_const
        (continuous_const.sub (hΨ.continuous.comp (continuous_const.prodMk continuous_id)))
    have hcompact : IsCompact C :=
      (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨v₀, R, hR, rfl⟩)).inter_right
        hclosed
    have hCD : C ⊆ D := by
      intro w hw
      by_contra hn
      have hfront : w ∈ frontier D := by
        rw [(PDE.isOpen_euclideanBall v₀ R).frontier_eq]
        exact ⟨hw.1, hn⟩
      have hl := hΨlat (τ, w) ⟨⟨hστ.le, le_rfl⟩, hfront⟩
      have hh : ε ≤ 1 - Ψ _ := hw.2
      linarith only [hl, hh, hε]
    obtain ⟨φ, hφs, hφc, hφD, hφrange, hφC⟩ :=
      exists_smooth_cutoff hcompact (PDE.isOpen_euclideanBall v₀ R) hCD
    let F : BoundedBorel _ :=
      ⟨φ, hφs.continuous.measurable, ⟨1, zero_le_one, fun w => by
        rw [abs_of_nonneg (hφrange w).1]
        exact (hφrange w).2⟩⟩
    obtain ⟨V, hV, heval, _huniq⟩ := hsolve τ F
      ⟨hφs, hφc, by simpa using hφD⟩
    let U  := fun p => (1 - ε) + (-1) * Ψ p
    have hU : ContDiff ℝ _ U := contDiff_const.add (contDiff_const.mul hΨ)
    have hUV := ball_terminal_lower_comparison v₀ hR hστ hB.1 B hB F V U hV
      hU.continuous.continuousOn (fun p _ => hU.contDiffAt.of_le (by simp))
      (fun p hp => by
        rw [ballExit_operator_add B _ _ contDiff_const
          ((contDiff_const.mul hΨ).of_le (by simp)), ballExit_operator_const,
          ballExit_operator_mul B _ Ψ (hΨ.of_le (by simp))]
        simpa using neg_nonneg.mpr (hΨop p hp))
      (fun w hw => by
        change (1 - ε) + (-1) * Ψ _ ≤ φ w
        by_cases hwC : w ∈ C
        · rw [hφC w hwC]
          have hp := hΨpos (τ, w) ⟨⟨hστ.le, le_rfl⟩, hw⟩
          linarith only [hp, hε]
        · have hn : ¬ε ≤ 1 - Ψ (τ, w) := fun hh => hwC ⟨hw, hh⟩
          have hp := (hφrange w).1
          linarith only [lt_of_not_ge hn, hp])
      (fun p hp => by
        have hh := hΨlat p hp
        linarith only [hh, hε])
      v (subset_closure hv)
    have he := heval σ hστ.le y
    rw [hrepr] at he
    have hi : V (σ, v) ≤ μ.real univ := by
      rw [he]
      calc
        _ ≤ ∫ _ : EvolutionPosition D stationary τ, (1) ∂μ := by
          apply integral_mono (boundedBorel_integrable _ μ)
            (integrable_const 1)
          intro w
          exact (hφrange w.1).2
        _ = μ.real univ := (integral_const (μ := μ) _).trans
          (by simp only [smul_eq_mul, mul_one])
    have hh : 1 - Ψ (σ, v) - ε ≤ V (σ, v) := by
      convert hUV using 1
      ring
    exact hh.trans hi
  have hlim : 1 - Ψ (σ, v) ≤ μ.real univ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hεbound ε hε
    linarith only [h]
  linarith only [hlim]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
