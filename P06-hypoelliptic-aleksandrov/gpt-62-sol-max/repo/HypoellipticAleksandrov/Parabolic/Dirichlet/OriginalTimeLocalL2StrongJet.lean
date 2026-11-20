module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeInteriorGeometry
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentativeUnique
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliTimeDerivative
public import HypoellipticAleksandrov.Parabolic.ParabolicW12TimeReflection

/-!
# Original-time local L2 strong jets

This file reflects the interior reverse-time weak Hessian and time derivative
back to the original-time cylinder.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set IsReverseTimeVariationalEnergySolution
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- A supplied global original-time value representative admits a local
anisotropic `L²` weak jet satisfying the literal original-time equation. -/
theorem exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ s₀ s₁ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hr₀s₀ : r₀ < s₀)
    (hs₀s₁ : s₀ < s₁)
    (hs₁r₁ : s₁ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O)
    (hOnonempty : O.Nonempty)
    (hOcompact : IsCompact (closure O))
    (hOΩ : closure O ⊆ Ω)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (w : TimeVelocity d → ℝ)
    (hwmem : MemLp w (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    ∃ J : ParabolicW12Function d
        (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞),
      J.toFun =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w ∧
      ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
        J.timeDeriv z +
              (∑ i : Fin d, ∑ j : Fin d,
                a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d,
              b z.1 z.2 j * J.velocityGrad z j) +
          c z.1 z.2 * J.toFun z =
        F z.1 z.2 := by
  obtain ⟨Kη, η, Kχ, χ, τ₀, τ₁, τ₂, τ₃, hχΩ, rfl, rfl, rfl, rfl,
      hτ₀, hτ₀τ₁, hτ₁τ₂, hτ₂τ₃, hτ₃⟩ :=
    exists_originalTimeInteriorCaccioppoliGeometry
      r₀ s₀ s₁ r₁ hr₀s₀ hs₀s₁ hs₁r₁ hΩ hOcompact hOΩ
  obtain ⟨Jrev, hU, hUslice, hJrev⟩ := exists_reverseTimeInteriorJet
    hd r₀ r₁ h₀₁ hΩ hΩbounded hOopen subset_closure η χ
    _ _ _ _ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam hlam hlamLam
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial u g hdu hu
  let U := Jrev.toFun
  have hQreflect := reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ s₀ s₁ O
  let J := (Jrev.timeReflect r₁ (measurableSet_Ioo.prod hOopen.measurableSet)).restrict hQreflect.ge
  refine ⟨J, ?_, ?_⟩
  · have hUreflectMem : MemLp (fun z => U (reverseTimeMap r₁ z)) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) := by
      have hglobal := reverseTimeMap_measurePreserving_restrict (d := d) r₁
        (U := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)
        ((measurableSet_Ioo.prod hΩ.measurableSet))
      have hglobalSet : reverseTimeMap r₁ ⁻¹'
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω) =
          Set.Ioo r₀ r₁ ×ˢ Ω := by
        simpa only [reverseTimeOpenInterval, sub_self] using
          reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ r₀ r₁ Ω
      simpa only [Function.comp_def, hglobalSet] using hU.comp_measurePreserving hglobal
    have hUreflectSlice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => U (reverseTimeMap r₁ (r, y))) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y := by
      filter_upwards [(originalTimeReflection_measurePreserving_toReverseTime r₀ r₁).quasiMeasurePreserving.ae hUslice] with r hr
      exact hr
    have hUw := originalTimeL2V_value_product_representative_ae_eq
      r₀ r₁ hΩ u (fun z => U (reverseTimeMap r₁ z)) w
      hUreflectMem.aemeasurable hwmem.aemeasurable hUreflectSlice hwslice
    have hlocal : (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w :=
      hUw.filter_mono (ae_mono (Measure.restrict_mono_set volume (by
        exact Set.prod_mono
          (Set.Ioo_subset_Ioo hr₀s₀.le hs₁r₁.le) (subset_closure.trans hOΩ))))
    change (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
      timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w
    exact hlocal
  · filter_upwards [] with z
    dsimp only [J, ParabolicW12Function.restrict, ParabolicW12Function.timeReflect, Function.comp_apply]
    rw [hJrev]
    simp only [reverseTimeMap_apply, reverseTimeCoefficient,
      reverseTimeVectorCoefficient, reverseTimeScalarCoefficient, sub_sub_cancel]
    ring

/-- A supplied reverse-time variational solution has one global original-time
value representative admitting compatible local anisotropic `L²` weak jets. -/
theorem exists_originalTimeValueRepresentative_localL2StrongJets
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∃ w : TimeVelocity d → ℝ,
      MemLp w (2 : ℝ≥0∞)
          (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) ∧
      (∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y) ∧
      ∀ (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)),
        r₀ < s₀ →
        s₀ < s₁ →
        s₁ < r₁ →
        IsOpen O →
        O.Nonempty →
        IsCompact (closure O) →
        closure O ⊆ Ω →
        ∃ J : ParabolicW12Function d
            (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞),
          J.toFun =ᵐ[
            timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w ∧
          ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
            J.timeDeriv z +
                  (∑ i : Fin d, ∑ j : Fin d,
                    a z.1 z.2 i j * J.velocityHessian z j i) +
                (∑ j : Fin d,
                  b z.1 z.2 j * J.velocityGrad z j) +
              c z.1 z.2 * J.toFun z =
            F z.1 z.2 := by
  obtain ⟨w, hwmem, hwslice⟩ :=
    exists_originalTimeL2V_value_product_representative r₀ r₁ hΩ u
  refine ⟨w, hwmem, hwslice, ?_⟩
  intro s₀ s₁ O hr₀s₀ hs₀s₁ hs₁r₁ hOopen hOnonempty hOcompact hOΩ
  exact exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    hd r₀ s₀ s₁ r₁ h₀₁ hr₀s₀ hs₀s₁ hs₁r₁ hΩ hΩbounded
    hOopen hOnonempty hOcompact hOΩ lam Lam hlam hlamLam a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial u g hdu hu
    w hwmem hwslice

end HypoellipticAleksandrov.Parabolic.Dirichlet
