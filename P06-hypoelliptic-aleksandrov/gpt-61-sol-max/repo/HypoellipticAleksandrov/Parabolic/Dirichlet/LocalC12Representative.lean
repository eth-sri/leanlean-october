module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HigherOrderLocalL2Regularity
public import HypoellipticAleksandrov.Parabolic.FiniteOrderSobolevC12Representative
public import Mathlib.MeasureTheory.Measure.OpenPos
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import all HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily

open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityTwo_comm from HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily


/-!
# Local scalar C¹˒² representatives

This module constructs a scalar C¹˒² representative on a positive collar of
a strictly interior closed product box. It identifies the classical jet with
the selected weak jet almost everywhere and upgrades the scalar equation to a
pointwise identity.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set MeasureTheory
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

noncomputable section

private def otime (d : ℕ) : TimeVelocityDerivativeIndex d 2 :=
  TimeVelocityDerivativeIndex.timeSucc (TimeVelocityDerivativeIndex.zero d 2) (by
    simp [TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order])
variable {d : ℕ}

private def ovel  (j : Fin d) : TimeVelocityDerivativeIndex d 2 :=
  TimeVelocityDerivativeIndex.velocitySucc (TimeVelocityDerivativeIndex.zero d 2) j (by
    simp [TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order])
private def ohess  (i j : Fin d) : TimeVelocityDerivativeIndex d 2 :=
  TimeVelocityDerivativeIndex.velocitySucc (ovel j) i (by
    have ho : (ovel j).1.order = 1 := by
      unfold ovel TimeVelocityDerivativeIndex.velocitySucc
      simp [TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
        VelocityMultiIndex.order, timeCoord, velocityCoord,
        TimeVelocityMultiIndex.ofTimeVelocity, Finset.sum_update_of_mem]
    omega)
private theorem coe_otime (d : ℕ) : (otime d).1 = Pi.single (timeCoord d) 1 := by
  bound
variable {d : ℕ}

private theorem coe_ovel  (j : Fin d) :
    (ovel j).1 = Pi.single (velocityCoord j) 1 := by
  funext c
  cases c with
  | inl q => rfl
  | inr k =>
      by_cases h : k = j
      · subst k
        simp [ovel, TimeVelocityDerivativeIndex.velocitySucc,
          TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
          velocityCoord]
      · simp [ovel, TimeVelocityDerivativeIndex.velocitySucc,
          TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
          velocityCoord, h]
variable (i j : Fin d)

private theorem coe_ohess   :
    (ohess i j).1 = Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1 := by
  funext c
  cases c with
  | inl q => rfl
  | inr k =>
      by_cases hki : k = i <;> by_cases hkj : k = j <;> subst_vars <;>
        simp [ohess, ovel, TimeVelocityDerivativeIndex.velocitySucc,
          TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, velocityCoord, *]



private theorem coordinate_jet_ae_eq_strong_jet
     {QJ QD S : HypoellipticAleksandrov.Parabolic.Region d}
    (hQJ : IsOpen QJ) (hSQJ : S ⊆ QJ)
    (J : ParabolicW12Function d QJ (2 ))
    (Dcore : ParabolicWeakDerivativeFamily d (2 * (d + 4)) QD J.toFun)
    (v : HypoellipticAleksandrov.Parabolic.ScalarField d) (hv : ContDiff ℝ 2 v)
    (hlow : ∀ alpha : ParabolicDerivativeIndex d 2,
      Dcore.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ 2 * (d + 4)) alpha) =
        (J.toWeakDerivativeFamily hQJ).representative alpha)
    (hjet : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[timeVelocityVolumeOn S]
        Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha)) :
    scalarTimeDerivative v =ᵐ[timeVelocityVolumeOn S] J.timeDeriv ∧
    (∀ j : Fin d, (fun z ↦ scalarSpatialGradient v z j) =ᵐ[timeVelocityVolumeOn S]
      fun z ↦ J.velocityGrad z j) ∧
    (∀ i j : Fin d, (fun z ↦ scalarSpatialHessian v z i j) =ᵐ[timeVelocityVolumeOn S]
      fun z ↦ J.velocityHessian z j i) := by
  let sharedTerm_5c29b2bb06 := ((by omega : 2 ≤ d + 4))
  let sharedTerm_9673db9bd9 := ((by omega : 2 ≤ 2 * (d + 4)))

  have htcoord := hjet (otime d)

  refine ⟨(by
      filter_upwards [htcoord] with z hz
      rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
      exact (by simpa [coe_otime] using hz.trans (congrFun (show Dcore.ordinaryRepresentative
        (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (otime d)) =
      J.timeDeriv by
          rw [show Dcore.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (otime d)) =
            Dcore.representative (ParabolicDerivativeIndex.castLE
              sharedTerm_9673db9bd9 (ParabolicDerivativeIndex.timeOne d)) by
            rfl]
          rw [hlow, ParabolicW12Function.toWeakDerivativeFamily_representative_timeOne]) z))), ?_, ?_⟩
  · intro j

    have hj := hjet (ovel j)
    filter_upwards [hj] with z hz
    rw [scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
    exact (by simpa [coe_ovel] using hz.trans (congrFun (show Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (ovel j)) =
        fun z ↦ J.velocityGrad z j by
        rw [show Dcore.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (ovel j)) =
          Dcore.representative (ParabolicDerivativeIndex.castLE
            sharedTerm_9673db9bd9 (ParabolicDerivativeIndex.velocityOne j)) by
          rfl]
        rw [hlow, ParabolicW12Function.toWeakDerivativeFamily_representative_velocityOne]) z))
  · intro i j

    have hj := hjet (ohess i j)

    filter_upwards [hj, (show (((J.toWeakDerivativeFamily hQJ).representative (ParabolicDerivativeIndex.velocityTwo j i))) =ᵐ[timeVelocityVolumeOn S]
        fun z ↦ J.velocityHessian z j i by
        rcases le_total j i with hji | hij
        · rw [ParabolicW12Function.toWeakDerivativeFamily_representative_velocityTwo
            hQJ J j i hji]
        · rw [_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityTwo_comm j i,
            ParabolicW12Function.toWeakDerivativeFamily_representative_velocityTwo
              hQJ J i j hij]
          exact (J.velocityHessian_ae_eq_swap hQJ i j).filter_mono
            (ae_mono (Measure.restrict_mono_set volume hSQJ)))] with z hzJ hzswap
    rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
    exact (by simpa [coe_ohess] using
      (hzJ.trans (congrFun (show Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (ohess i j)) =
        (J.toWeakDerivativeFamily hQJ).representative
          (ParabolicDerivativeIndex.velocityTwo j i) by
          rw [show Dcore.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.castLE sharedTerm_5c29b2bb06 (ohess i j)) =
            Dcore.representative (ParabolicDerivativeIndex.castLE
              sharedTerm_9673db9bd9 (ParabolicDerivativeIndex.velocityTwo j i)) by
            rfl]
          exact hlow _) z)).trans hzswap)
private theorem pointwise_scalarPDE_of_ae_jet
     {Q S : HypoellipticAleksandrov.Parabolic.Region d}
    (hS : IsOpen S) (v : HypoellipticAleksandrov.Parabolic.ScalarField d) (hC12 : IsScalarC12On v S)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (ha : ∀ i j : Fin d, ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j) S)
    (hb : ∀ j : Fin d, ContinuousOn (fun z : TimeVelocity d => b z.1 z.2 j) S)
    (hc : ContinuousOn (fun z : TimeVelocity d => c z.1 z.2) S)
    (hF : ContinuousOn (fun z : TimeVelocity d => F z.1 z.2) S)
    (J : ParabolicW12Function d Q (2 ))
    (hEq : (fun z => J.timeDeriv z +
        (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * J.velocityHessian z j i) +
        (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) +
        c z.1 z.2 * J.toFun z) =ᵐ[timeVelocityVolumeOn S]
          fun z => F z.1 z.2)
    (hv : v =ᵐ[timeVelocityVolumeOn S] J.toFun)
    (ht : scalarTimeDerivative v =ᵐ[timeVelocityVolumeOn S] J.timeDeriv)
    (hg : ∀ j : Fin d,
      (fun z => scalarSpatialGradient v z j) =ᵐ[timeVelocityVolumeOn S]
        fun z => J.velocityGrad z j)
    (hh : ∀ i j : Fin d,
      (fun z => scalarSpatialHessian v z i j) =ᵐ[timeVelocityVolumeOn S]
        fun z => J.velocityHessian z j i) :
    ∀ z ∈ S,
      scalarTimeDerivative v z +
          (∑ i : Fin d, ∑ j : Fin d,
            a z.1 z.2 i j * scalarSpatialHessian v z i j) +
        (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient v z j) +
      c z.1 z.2 * v z = F z.1 z.2 := by
  let lhs  := fun z =>
    scalarTimeDerivative v z +
        (∑ i : Fin d, ∑ j : Fin d,
          a z.1 z.2 i j * scalarSpatialHessian v z i j) +
      (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient v z j) +
    c z.1 z.2 * v z
  let weakLhs  := fun z =>
    J.timeDeriv z +
        (∑ i : Fin d, ∑ j : Fin d,
          a z.1 z.2 i j * J.velocityHessian z j i) +
      (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) +
    c z.1 z.2 * J.toFun z



  have hlae  := (show lhs =ᵐ[timeVelocityVolumeOn S] weakLhs by
      exact ((ht.add (by
          filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hh i)] with z hz
          simp_rw [hz])).add (by
          filter_upwards [ae_all_iff.mpr hg] with z hz
          simp_rw [hz])).add
        (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hv)).trans hEq


  have hlhs : ContinuousOn lhs S := by
    exact ((hC12.continuousOn_scalarTimeDerivative.add
      (continuousOn_finset_sum Finset.univ fun i _ =>
        continuousOn_finset_sum Finset.univ fun j _ =>
          (ha i j).mul ((show ∀ i j : Fin d,
      ContinuousOn (fun z => scalarSpatialHessian v z i j) S by
              intro i j
              exact (continuous_apply j).comp_continuousOn
                ((continuous_apply i).comp_continuousOn
                  hC12.continuousOn_scalarSpatialHessian)) i j))).add
      (continuousOn_finset_sum Finset.univ fun j _ =>
        (hb j).mul ((show ∀ j : Fin d,
      ContinuousOn (fun z => scalarSpatialGradient v z j) S by
            intro j
            exact (continuous_apply j).comp_continuousOn
              hC12.continuousOn_scalarSpatialGradient) j))).add
      (hc.mul hC12.continuousOn)

  intro z hz
  exact (show EqOn lhs (fun z => F z.1 z.2) S by
      rw [timeVelocityVolumeOn] at hlae
      exact Measure.eqOn_open_of_ae_eq hlae hS hlhs hF) hz
/-- A selected original-time value representative has a compatible scalar
`C^1,2` representative on a positive collar of every strictly interior closed
product box; its classical jet is the selected weak jet almost everywhere and
it satisfies the original-time equation pointwise. -/
theorem exists_localC12Representative_of_valueRepresentative
     {Ω O₀ O : PDE.VelocityRegion d} (hd : 0 < d)
    (r₀ q₀ s₀ s₁ q₁ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hr₀q₀ : r₀ < q₀)
    (hq₀s₀ : q₀ < s₀) (hs₀s₁ : s₀ < s₁) (hs₁q₁ : s₁ < q₁)
    (hq₁r₁ : q₁ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hO₀open : IsOpen O₀) (hO₀ne : O₀.Nonempty)
    (hO₀compact : IsCompact (closure O₀)) (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hOcompact : IsCompact (closure O)) (hOO₀ : closure O ⊆ O₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 ))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwmem : MemLp w (2 )
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    ∃ (J : ParabolicW12Function d
        (Set.Ioo q₀ q₁ ×ˢ O₀) (2 ))
      (rho : ℝ) (_ : 0 < rho) (v : HypoellipticAleksandrov.Parabolic.ScalarField d),
      J.toFun =ᵐ[timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀)] w ∧
      let S := Metric.thickening rho (Set.Icc s₀ s₁ ×ˢ closure O)
      S ⊆ Set.Ioo q₀ q₁ ×ˢ O₀ ∧
      ContDiff ℝ 2 v ∧
      IsScalarC12On v S ∧
      v =ᵐ[timeVelocityVolumeOn S] w ∧
      scalarTimeDerivative v =ᵐ[timeVelocityVolumeOn S] J.timeDeriv ∧
      (∀ j : Fin d,
        (fun z => scalarSpatialGradient v z j) =ᵐ[timeVelocityVolumeOn S]
          fun z => J.velocityGrad z j) ∧
      (∀ i j : Fin d,
        (fun z => scalarSpatialHessian v z i j) =ᵐ[timeVelocityVolumeOn S]
          fun z => J.velocityHessian z j i) ∧
      ∀ z ∈ S,
        scalarTimeDerivative v z +
            (∑ i : Fin d, ∑ j : Fin d,
              a z.1 z.2 i j * scalarSpatialHessian v z i j) +
          (∑ j : Fin d,
            b z.1 z.2 j * scalarSpatialGradient v z j) +
        c z.1 z.2 * v z = F z.1 z.2 := by
  obtain ⟨Citer, hCiter, hrun⟩ :=
    exists_higherOrderLocalL2WeakDerivativeFamily_of_valueRepresentative
      hd r₀ q₀ s₀ s₁ q₁ r₁ h₀₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁
      hΩ hΩbounded hO₀open hO₀ne hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
      lam Lam hlam hlamLam a b c haSmooth hbSmooth hcSmooth hLower hUpper hcNonpos
  obtain ⟨J, coreLeft, coreRight, Ocore, B, Emax, DcoreRaw,
      hJw, hEq, hq₀coreLeft, hcoreLefts₀, hs₁coreRight, hcoreRightq₁,
      hOcoreOpen, hOcoreNe, hOcoreCompact, hOOcore, hOcoreO₀,
      hB0, hB, hErep, hEnorm, hlow, hDnorm⟩ :=
    hrun F hFSmooth initial u g hdu hu w hwmem hwslice
  have hweight : 2 * d + 8 = 2 * (d + 4) := by omega
  let Dcore  := hweight ▸ DcoreRaw





  obtain ⟨rho, hrho, v, hSCore, hv, hC12, hvJ, hjet⟩ :=
    exists_finiteOrderSobolevC12Representative
      (isOpen_Ioo.prod hOcoreOpen) (isCompact_Icc.prod hOcompact) (by
          rintro z ⟨hztime, hzspace⟩
          exact ⟨⟨hcoreLefts₀.trans_le hztime.1,
            hztime.2.trans_lt hs₁coreRight⟩, hOOcore hzspace⟩) Dcore



  have hSQ₀  := hSCore.trans (show Set.Ioo coreLeft coreRight ×ˢ Ocore ⊆
      Set.Ioo q₀ q₁ ×ˢ O₀ by
      rintro z ⟨hztime, hzspace⟩
      exact ⟨⟨hq₀coreLeft.trans hztime.1,
        hztime.2.trans hcoreRightq₁⟩,
        hOcoreO₀ (subset_closure hzspace)⟩)
  have hvw  := hvJ.trans (hJw.filter_mono
      (ae_mono (Measure.restrict_mono_set volume hSQ₀)))
  obtain ⟨ht, hg, hh⟩ :=
    coordinate_jet_ae_eq_strong_jet (isOpen_Ioo.prod hO₀open) hSQ₀
      J Dcore v hv (by
          assumption) hjet


  have hSCyl  :=
    hSQ₀.trans (show Set.Ioo q₀ q₁ ×ˢ O₀ ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω by
        rintro z ⟨hztime, hzspace⟩
        exact ⟨⟨hr₀q₀.le.trans hztime.1.le,
          hztime.2.le.trans hq₁r₁.le⟩,
          subset_closure (hO₀Ω (subset_closure hzspace))⟩)




  have hEqS := hEq.filter_mono
    (ae_mono (Measure.restrict_mono_set volume hSQ₀))
  have hpoint := pointwise_scalarPDE_of_ae_jet Metric.isOpen_thickening v hC12 a b c F
    (by
        obtain ⟨Ua, hUa, hCylUa, haUa⟩ := haSmooth
        intro i j
        have hi := (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haUa
          (fun _ _ => Set.mem_univ _)
        have hij := (contDiffOn_apply ℝ ℝ j Set.univ).comp hi
          (fun _ _ => Set.mem_univ _)
        exact hij.continuousOn.mono (hSCyl.trans hCylUa)) (by
        obtain ⟨Ub, hUb, hCylUb, hbUb⟩ := hbSmooth
        intro j
        have hj := (contDiffOn_apply ℝ ℝ j Set.univ).comp hbUb
          (fun _ _ => Set.mem_univ _)
        exact hj.continuousOn.mono (hSCyl.trans hCylUb)) (by
        obtain ⟨Uc, hUc, hCylUc, hcUc⟩ := hcSmooth
        exact hcUc.continuousOn.mono (hSCyl.trans hCylUc)) (by
        obtain ⟨UF, hUF, hCylUF, hFUF⟩ := hFSmooth
        exact hFUF.continuousOn.mono (hSCyl.trans hCylUF)) J hEqS hvJ ht hg hh
  refine ⟨J, rho, hrho, v, hJw, ?_⟩
  dsimp only
  exact ⟨hSQ₀, hv, hC12, hvw, ht, hg, hh, hpoint⟩


end

end HypoellipticAleksandrov.Parabolic.Dirichlet
