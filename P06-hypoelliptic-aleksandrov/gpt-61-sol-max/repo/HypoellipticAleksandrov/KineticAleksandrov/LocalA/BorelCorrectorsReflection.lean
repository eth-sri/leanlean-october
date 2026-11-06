module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectors
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus

/-! # Backward homogeneous correctors in the source geometry -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic TheoremA Filter
open scoped Matrix.Norms.Elementwise

/-- Reflection gives actual backward correctors on every compact interior set. -/
theorem exists_backward_homogeneous_correctors
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticityAE lam A)
    (hhi : HasUpperEllipticityAE Lam A)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u : HypoellipticAleksandrov.KineticScalarField d) (hu : IsKineticC112On u (backwardCylinder P₀ R))
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0)
    (L : Set (KineticPoint d)) (hL : IsCompact L) (hLD : L ⊆ backwardCylinder P₀ R) :
    ∃ (B : ℕ → CoefficientField d) (w : ℕ → HypoellipticAleksandrov.KineticScalarField d)
      (O : Set (KineticPoint d)), IsOpen O ∧ L ⊆ O ∧
      (∀ j, IsSmoothCoefficient (B j) ∧ IsSymmetricCoefficient (B j) ∧
        HasLowerEllipticityAE lam (B j) ∧ HasUpperEllipticityAE Lam (B j)) ∧
      (∀ j, IsKineticC112On (w j) O) ∧
      (∀ j, ∀ P ∈ O, backwardOperatorOfTimeVelocityCoefficient (B j) (w j) P = 0) ∧
      TendstoUniformlyOn w u atTop L := by
  let Z := kineticReflection P₀
  let D := forwardCylinder Z R hR
  have hmap : MapsTo (kineticReflection (d := d)) D (backwardCylinder P₀ R) := by
    intro P hP

    dsimp only [D, Z] at hP
    rw [← (kineticReflection_image_backwardCylinder P₀ R hR)] at hP
    rcases hP with ⟨Q, hQ, rfl⟩
    simpa only [kineticReflection_involutive Q] using hQ




  obtain ⟨B, W, V, hV, hKV, _, hB, hW, heW, ht⟩ :=
    exists_borel_homogeneous_correctors hH hLE hd lam Lam hlam hLam
      (kineticReflectedCoefficient A) (isBorelCoefficient_kineticReflectedCoefficient A hA)
      (isSymmetricCoefficient_kineticReflectedCoefficient A hs)
      (ellipticityAE_kineticReflectedCoefficient A lam Lam hlo hhi).1
      (ellipticityAE_kineticReflectedCoefficient A lam Lam hlo hhi).2 Z R hR
      (u ∘ kineticReflection) (comparison_regular_mono (isKineticC112On_kineticReflection u _ hu) hmap) (by
          filter_upwards [((measurePreserving_kineticReflection d).quasiMeasurePreserving.restrict hmap).ae he] with P hP
          rw [reflectedKineticOperator_reflection, hP, neg_zero]) (kineticReflection '' L)
      (hL.image (continuous_kineticReflection d)) (by
          dsimp only [D, Z]
          rw [← kineticReflection_image_backwardCylinder P₀ R hR]
          exact image_mono hLD)


  have hWs j := isKineticC112On_of_contDiffOn hV
    (boundary_physical_smooth_to_native (hW j))
  have hBs j : IsSmoothCoefficient (B j) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro k
    exact (hB j).2.2.1 i k |>.comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := (0 : PDE.Vec d)))))
  refine ⟨fun j => kineticReflectedCoefficient (B j), fun j => W j ∘ kineticReflection,
    (kineticReflection ⁻¹' V), (hV.preimage (continuous_kineticReflection d)), fun P hP => hKV (mem_image_of_mem _ hP), ?_, ?_, ?_, ?_⟩
  · intro j
    have hlo' : HasLowerEllipticityAE lam (B j) :=
      Eventually.of_forall (fun x => (hB j).2.2.2.2.1 x.1 x.2)
    have hhi' : HasUpperEllipticityAE Lam (B j) :=
      Eventually.of_forall (fun x => (hB j).2.2.2.2.2 x.1 x.2)
    exact ⟨isSmoothCoefficient_kineticReflectedCoefficient _ (hBs j),
      isSymmetricCoefficient_kineticReflectedCoefficient _ (hB j).2.2.2.1,
      (ellipticityAE_kineticReflectedCoefficient _ lam Lam hlo' hhi').1,
      (ellipticityAE_kineticReflectedCoefficient _ lam Lam hlo' hhi').2⟩
  · intro j
    exact isKineticC112On_kineticReflection _ _ (hWs j)
  · intro j P hP
    have hh := reflectedKineticOperator_reflection (kineticReflectedCoefficient (B j))
      (W j ∘ kineticReflection) (kineticReflection P)
    have hc : kineticReflectedCoefficient (kineticReflectedCoefficient (B j)) = B j := by
      funext s v
      simp only [kineticReflectedCoefficient, neg_neg]
    have hw : (W j ∘ kineticReflection) ∘ kineticReflection = W j := by
      funext Q
      simp only [Function.comp_apply, kineticReflection_involutive Q]
    rw [hc, hw, kineticReflection_involutive P, heW j _ hP] at hh
    linarith
  ·

    have hu' : (u ∘ kineticReflection) ∘ kineticReflection = u := by
      funext P
      simp only [Function.comp_apply, kineticReflection_involutive P]
    simpa only [hu'] using (ht.comp (kineticReflection )).mono (fun _ h => mem_image_of_mem _ h)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
