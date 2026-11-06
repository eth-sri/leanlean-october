module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HigherOrderLocalL2Regularity
public import HypoellipticAleksandrov.Parabolic.FiniteOrderSobolevC12Representative
public import Mathlib.MeasureTheory.Measure.OpenPos
import HypoellipticAleksandrov.Parabolic.GenericPreLiftWeakDerivativeFamilyIteration
import HypoellipticAleksandrov.Parabolic.HigherOrderNestedProductBoxChain
import HypoellipticAleksandrov.Parabolic.HigherOrderSourceWeakDerivativeFamily
import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamilyEquation

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
private def ovel {d } (j : Fin d) : TimeVelocityDerivativeIndex d 2 :=
  TimeVelocityDerivativeIndex.velocitySucc (TimeVelocityDerivativeIndex.zero d 2) j (by
    simp [TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order])
private def ohess {d } (i j : Fin d) : TimeVelocityDerivativeIndex d 2 :=
  TimeVelocityDerivativeIndex.velocitySucc (ovel j) i (by
    have ho : (ovel j).1.order = 1 := by
      unfold ovel TimeVelocityDerivativeIndex.velocitySucc
      simp [TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
        VelocityMultiIndex.order, timeCoord, velocityCoord,
        TimeVelocityMultiIndex.ofTimeVelocity, Finset.sum_update_of_mem]
    omega)
private theorem velocityTwo_comm_local {d } (i j : Fin d) :
    ParabolicDerivativeIndex.velocityTwo i j =
      ParabolicDerivativeIndex.velocityTwo j i := by
  apply Subtype.ext
  funext c
  cases c with
  | inl q => rfl
  | inr k =>
      by_cases hki : k = i
      · subst k
        by_cases hij : i = j
        · subst j; rfl
        · simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne, ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hij]
      · by_cases hkj : k = j
        · subst k
          simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne, ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hki]
        · simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne, ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hki, hkj]
private theorem coordinate_jet_ae_eq_strong_jet
    {d QJ QD S}
    (hQJ : IsOpen QJ) (hSQJ : S ⊆ QJ)
    (J : ParabolicW12Function d QJ (2 : ℝ≥0∞))
    (Dcore : ParabolicWeakDerivativeFamily d (2 * (d + 4)) QD J.toFun)
    (v : TimeVelocity d → ℝ) (hv : ContDiff ℝ 2 v)
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
  have htimeRep : Dcore.ordinaryRepresentative
        (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (otime d)) =
      J.timeDeriv := by
    rw [show Dcore.ordinaryRepresentative
        (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (otime d)) =
      Dcore.representative (ParabolicDerivativeIndex.castLE
        (by omega : 2 ≤ 2 * (d + 4)) (ParabolicDerivativeIndex.timeOne d)) by
      rfl]
    rw [hlow, ParabolicW12Function.toWeakDerivativeFamily_representative_timeOne]
  have htcoord := hjet (otime d)
  have ht : scalarTimeDerivative v =ᵐ[timeVelocityVolumeOn S] J.timeDeriv := by
    filter_upwards [htcoord] with z hz
    rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
    have _h_inl_16 (d) : (otime d).1 = Pi.single (timeCoord d) 1 := by
      funext c
      cases c <;> simp [otime, TimeVelocityDerivativeIndex.timeSucc,
        TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, timeCoord]
    exact (by simpa [_h_inl_16] using hz.trans (congrFun htimeRep z))
  refine ⟨ht, ?_, ?_⟩
  · intro j
    have hgradRep : Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (ovel j)) =
        fun z ↦ J.velocityGrad z j := by
      rw [show Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (ovel j)) =
        Dcore.representative (ParabolicDerivativeIndex.castLE
          (by omega : 2 ≤ 2 * (d + 4)) (ParabolicDerivativeIndex.velocityOne j)) by
        rfl]
      rw [hlow, ParabolicW12Function.toWeakDerivativeFamily_representative_velocityOne]
    have hj := hjet (ovel j)
    filter_upwards [hj] with z hz
    rw [scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
    have _h_inl_16 (j : Fin d) : (ovel j).1 = Pi.single (velocityCoord j) 1 := by
      funext c
      cases c with
      | inl q => simp [ovel, TimeVelocityDerivativeIndex.velocitySucc,
          TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, velocityCoord]
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
    exact (by simpa [_h_inl_16] using hz.trans (congrFun hgradRep z))
  · intro i j
    have hhessRep : Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (ohess i j)) =
        (J.toWeakDerivativeFamily hQJ).representative
          (ParabolicDerivativeIndex.velocityTwo j i) := by
      rw [show Dcore.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) (ohess i j)) =
        Dcore.representative (ParabolicDerivativeIndex.castLE
          (by omega : 2 ≤ 2 * (d + 4)) (ParabolicDerivativeIndex.velocityTwo j i)) by
        rfl]
      exact hlow _
    have hj := hjet (ohess i j)
    have hfamily : (fun z ↦ (J.toWeakDerivativeFamily hQJ).representative
          (ParabolicDerivativeIndex.velocityTwo j i) z) =ᵐ[timeVelocityVolumeOn S]
        fun z ↦ J.velocityHessian z j i := by
      rcases le_total j i with hji | hij
      · rw [ParabolicW12Function.toWeakDerivativeFamily_representative_velocityTwo
          hQJ J j i hji]
      · rw [velocityTwo_comm_local j i,
          ParabolicW12Function.toWeakDerivativeFamily_representative_velocityTwo
            hQJ J i j hij]
        exact (J.velocityHessian_ae_eq_swap hQJ i j).filter_mono
          (ae_mono (Measure.restrict_mono_set volume hSQJ))
    filter_upwards [hj, hfamily] with z hzJ hzswap
    rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hv]
    have _h_inl_18 (i : Fin d) (j) : (ohess i j).1 = Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1 := by
      funext c
      cases c with
      | inl q => simp [ohess, ovel, TimeVelocityDerivativeIndex.velocitySucc,
          TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, velocityCoord,
          timeCoord]
      | inr k =>
          by_cases hki : k = i <;> by_cases hkj : k = j <;> subst_vars <;>
            simp [ohess, ovel, TimeVelocityDerivativeIndex.velocitySucc,
              TimeVelocityDerivativeIndex.zero, TimeVelocityMultiIndex.ofTimeVelocity,
              TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, velocityCoord, *]
    exact (by simpa [_h_inl_18] using
      (hzJ.trans (congrFun hhessRep z)).trans hzswap)
theorem exists_localC12Representative_of_valueRepresentative
    {d } {Ω O₀ O : Set (PDE.Vec d)} (hd : 0 < d)
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
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
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
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (w : TimeVelocity d → ℝ)
    (hwmem : MemLp w (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    ∃ (J : ParabolicW12Function d
        (Set.Ioo q₀ q₁ ×ˢ O₀) (2 : ℝ≥0∞))
      (rho : ℝ) (_ : 0 < rho) (v : TimeVelocity d → ℝ),
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
  obtain ⟨Citer, hCiter, hrun⟩ : ∃ Citer : ℝ, 0 ≤ Citer ∧ ∀ (F : ℝ → PDE.Vec d → ℝ)
      (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω))
      (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (u : ReverseTimeL2V hΩ (r₁ - r₀))
      (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
      (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
      (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial u g hdu) (w : TimeVelocity d → ℝ)
      (hwmem : MemLp w (2 : ℝ≥0∞) (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
      (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (r₁ - r)) y),
      ∃ (J : ParabolicW12Function d (Set.Ioo q₀ q₁ ×ˢ O₀) (2 : ℝ≥0∞))
        (coreLeft coreRight : ℝ) (Ocore : Set (PDE.Vec d))
        (B : ParabolicDerivativeIndex d (2 * d + 6) → ℝ)
        (Emax : ParabolicWeakDerivativeFamily d (2 * d + 6) (Set.Ioo q₀ q₁ ×ˢ O₀)
          (fun z : TimeVelocity d => F z.1 z.2))
        (Dcore : ParabolicWeakDerivativeFamily d (2 * d + 8)
          (Set.Ioo coreLeft coreRight ×ˢ Ocore) J.toFun),
        J.toFun =ᵐ[timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀)] w ∧
        (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀),
          J.timeDeriv z + (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) + c z.1 z.2 * J.toFun z = F z.1 z.2) ∧
        q₀ < coreLeft ∧ coreLeft < s₀ ∧ s₁ < coreRight ∧ coreRight < q₁ ∧
        IsOpen Ocore ∧ Ocore.Nonempty ∧ IsCompact (closure Ocore) ∧
        closure O ⊆ Ocore ∧ closure Ocore ⊆ O₀ ∧ (∀ beta, 0 ≤ B beta) ∧
        (∀ beta z, z ∈ closure (Set.Ioo q₀ q₁ ×ˢ O₀) →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
            (fun x : TimeVelocity d => F x.1 x.2) z| ≤ B beta) ∧
        (∀ beta, Emax.representative beta = TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (fun x : TimeVelocity d => F x.1 x.2)) ∧
        ParabolicWeakDerivativeFamily.squaredL2Norm Emax ≤
          volume.real (Set.Ioo q₀ q₁ ×ˢ O₀) * ∑ beta, (B beta) ^ 2 ∧
        (∀ alpha : ParabolicDerivativeIndex d 2, Dcore.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ 2 * d + 8) alpha) =
          (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
        ParabolicWeakDerivativeFamily.squaredL2Norm Dcore ≤ Citer *
          (ParabolicWeakDerivativeFamily.squaredL2Norm
            (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)) +
           ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
    obtain ⟨Citer, hCiter, hrun⟩ := exists_higherOrderLocalL2WeakDerivativeFamily_of_strongJet
      r₀ q₀ s₀ s₁ q₁ r₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁ hΩ hO₀open
      hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀ lam Lam hlam hlamLam a b c
      haSmooth hbSmooth hcSmooth hLower hUpper
    refine ⟨Citer, hCiter, ?_⟩
    intro F hFSmooth initial u g hdu hu w hwmem hwslice
    obtain ⟨J, hJw, hEq⟩ := exists_originalTimeLocalL2StrongJet_of_valueRepresentative
      hd r₀ q₀ q₁ r₁ h₀₁ hr₀q₀ (hq₀s₀.trans (hs₀s₁.trans hs₁q₁)) hq₁r₁
      hΩ hΩbounded hO₀open hO₀ne hO₀compact hO₀Ω lam Lam hlam hlamLam a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial u g hdu hu
      w hwmem hwslice
    obtain ⟨coreLeft, coreRight, Ocore, B, Emax, Dcore, hrest⟩ := hrun F hFSmooth J hEq
    exact ⟨J, coreLeft, coreRight, Ocore, B, Emax, Dcore, hJw, hEq, hrest⟩
  obtain ⟨J, coreLeft, coreRight, Ocore, B, Emax, DcoreRaw,
      hJw, hEq, hq₀coreLeft, hcoreLefts₀, hs₁coreRight, hcoreRightq₁,
      hOcoreOpen, hOcoreNe, hOcoreCompact, hOOcore, hOcoreO₀,
      hB0, hB, hErep, hEnorm, hlow, hDnorm⟩ :=
    hrun F hFSmooth initial u g hdu hu w hwmem hwslice
  have hweight : 2 * d + 8 = 2 * (d + 4) := by omega
  let Dcore : ParabolicWeakDerivativeFamily d (2 * (d + 4))
      (Set.Ioo coreLeft coreRight ×ˢ Ocore) J.toFun := hweight ▸ DcoreRaw
  have hlow' : ∀ alpha : ParabolicDerivativeIndex d 2,
      Dcore.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ 2 * (d + 4)) alpha) =
        (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha := by
    simpa [Dcore] using hlow
  let Ctarget := Set.Icc s₀ s₁ ×ˢ closure O
  have hCtargetCompact : IsCompact Ctarget :=
    isCompact_Icc.prod hOcompact
  have hCtargetCore : Ctarget ⊆ Set.Ioo coreLeft coreRight ×ˢ Ocore := by
    rintro z ⟨hztime, hzspace⟩
    exact ⟨⟨hcoreLefts₀.trans_le hztime.1,
      hztime.2.trans_lt hs₁coreRight⟩, hOOcore hzspace⟩
  have hCoreOpen : IsOpen (Set.Ioo coreLeft coreRight ×ˢ Ocore) :=
    isOpen_Ioo.prod hOcoreOpen
  obtain ⟨rho, hrho, v, hSCore, hv, hC12, hvJ, hjet⟩ :=
    exists_finiteOrderSobolevC12Representative
      hCoreOpen hCtargetCompact hCtargetCore Dcore
  let S := Metric.thickening rho Ctarget
  have hSOpen : IsOpen S := Metric.isOpen_thickening
  have hCoreQ₀ : Set.Ioo coreLeft coreRight ×ˢ Ocore ⊆
      Set.Ioo q₀ q₁ ×ˢ O₀ := by
    rintro z ⟨hztime, hzspace⟩
    exact ⟨⟨hq₀coreLeft.trans hztime.1,
      hztime.2.trans hcoreRightq₁⟩,
      hOcoreO₀ (subset_closure hzspace)⟩
  have hSQ₀ := hSCore.trans hCoreQ₀
  have hvw : v =ᵐ[timeVelocityVolumeOn S] w := by
    exact hvJ.trans (hJw.filter_mono
      (ae_mono (Measure.restrict_mono_set volume hSQ₀)))
  obtain ⟨ht, hg, hh⟩ :=
    coordinate_jet_ae_eq_strong_jet (isOpen_Ioo.prod hO₀open) hSQ₀
      J Dcore v hv hlow' hjet
  have hq₀q₁ := hq₀s₀.trans (hs₀s₁.trans hs₁q₁)
  have hQ₀Cyl : Set.Ioo q₀ q₁ ×ˢ O₀ ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro z ⟨hztime, hzspace⟩
    exact ⟨⟨hr₀q₀.le.trans hztime.1.le,
      hztime.2.le.trans hq₁r₁.le⟩,
      subset_closure (hO₀Ω (subset_closure hzspace))⟩
  have hSCyl :=
    hSQ₀.trans hQ₀Cyl
  have haCont : ∀ i j : Fin d,
      ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j) S := by
    obtain ⟨Ua, hUa, hCylUa, haUa⟩ := haSmooth
    intro i j
    have hi := (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haUa
      (fun _ _ => Set.mem_univ _)
    have hij := (contDiffOn_apply ℝ ℝ j Set.univ).comp hi
      (fun _ _ => Set.mem_univ _)
    exact hij.continuousOn.mono (hSCyl.trans hCylUa)
  have hbCont : ∀ j : Fin d,
      ContinuousOn (fun z : TimeVelocity d => b z.1 z.2 j) S := by
    obtain ⟨Ub, hUb, hCylUb, hbUb⟩ := hbSmooth
    intro j
    have hj := (contDiffOn_apply ℝ ℝ j Set.univ).comp hbUb
      (fun _ _ => Set.mem_univ _)
    exact hj.continuousOn.mono (hSCyl.trans hCylUb)
  have hcCont : ContinuousOn (fun z : TimeVelocity d => c z.1 z.2) S := by
    obtain ⟨Uc, hUc, hCylUc, hcUc⟩ := hcSmooth
    exact hcUc.continuousOn.mono (hSCyl.trans hCylUc)
  have hFCont : ContinuousOn (fun z : TimeVelocity d => F z.1 z.2) S := by
    obtain ⟨UF, hUF, hCylUF, hFUF⟩ := hFSmooth
    exact hFUF.continuousOn.mono (hSCyl.trans hCylUF)
  have hEqS := hEq.filter_mono
    (ae_mono (Measure.restrict_mono_set volume hSQ₀))
  have hpoint : ∀ z ∈ S,
      scalarTimeDerivative v z +
          (∑ i : Fin d, ∑ j : Fin d,
            a z.1 z.2 i j * scalarSpatialHessian v z i j) +
        (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient v z j) +
      c z.1 z.2 * v z = F z.1 z.2 := by
    let lhs : TimeVelocity d → ℝ := fun z =>
      scalarTimeDerivative v z +
          (∑ i : Fin d, ∑ j : Fin d,
            a z.1 z.2 i j * scalarSpatialHessian v z i j) +
        (∑ j : Fin d, b z.1 z.2 j * scalarSpatialGradient v z j) +
      c z.1 z.2 * v z
    let weakLhs : TimeVelocity d → ℝ := fun z =>
      J.timeDeriv z +
          (∑ i : Fin d, ∑ j : Fin d,
            a z.1 z.2 i j * J.velocityHessian z j i) +
        (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) +
      c z.1 z.2 * J.toFun z
    have hhSum : (fun z => ∑ i : Fin d, ∑ j : Fin d,
          a z.1 z.2 i j * scalarSpatialHessian v z i j) =ᵐ[timeVelocityVolumeOn S]
        fun z => ∑ i : Fin d, ∑ j : Fin d,
          a z.1 z.2 i j * J.velocityHessian z j i := by
      filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hh i j] with z hz
      simp_rw [hz]
    have hgSum : (fun z => ∑ j : Fin d,
          b z.1 z.2 j * scalarSpatialGradient v z j) =ᵐ[timeVelocityVolumeOn S]
        fun z => ∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j := by
      filter_upwards [ae_all_iff.mpr hg] with z hz
      simp_rw [hz]
    have hlw : lhs =ᵐ[timeVelocityVolumeOn S] weakLhs := by
      exact ((ht.add hhSum).add hgSum).add
        (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hvJ)
    have hlae := hlw.trans hEqS
    have hgrad : ∀ j : Fin d,
        ContinuousOn (fun z => scalarSpatialGradient v z j) S := by
      intro j
      exact (continuous_apply j).comp_continuousOn
        hC12.continuousOn_scalarSpatialGradient
    have hhess : ∀ i j : Fin d,
        ContinuousOn (fun z => scalarSpatialHessian v z i j) S := by
      intro i j
      exact (continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn
          hC12.continuousOn_scalarSpatialHessian)
    have hlhs : ContinuousOn lhs S := by
      exact ((hC12.continuousOn_scalarTimeDerivative.add
        (continuousOn_finset_sum Finset.univ fun i _ =>
          continuousOn_finset_sum Finset.univ fun j _ =>
            (haCont i j).mul (hhess i j))).add
        (continuousOn_finset_sum Finset.univ fun j _ =>
          (hbCont j).mul (hgrad j))).add
        (hcCont.mul hC12.continuousOn)
    have heq : EqOn lhs (fun z => F z.1 z.2) S := by
      rw [timeVelocityVolumeOn] at hlae
      exact Measure.eqOn_open_of_ae_eq hlae hSOpen hlhs hFCont
    intro z hz
    exact heq hz
  refine ⟨J, rho, hrho, v, hJw, ?_⟩
  dsimp only
  exact ⟨hSQ₀, hv, hC12, hvw, ht, hg, hh, hpoint⟩


end

end HypoellipticAleksandrov.Parabolic.Dirichlet
