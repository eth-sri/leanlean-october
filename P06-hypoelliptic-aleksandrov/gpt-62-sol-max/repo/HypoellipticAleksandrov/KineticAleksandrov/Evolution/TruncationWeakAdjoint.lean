module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord

/-! # Adjoint integration for continuous anisotropic directional jets -/

@[expose] public section

open Set MeasureTheory
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

section
variable {n : ℕ} {U : Set (EvolutionVec n)} (B : FullKineticCoefficient n)
  (b : PDE.Vec n → PDE.Vec n)

/-- Continuous anisotropic directional jets give the exact transported adjoint identity. -/
theorem integral_transportedAdjoint_of_anisotropic_jets
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (u T : EvolutionVec n → ℝ) (V Z : Fin n → EvolutionVec n → ℝ)
    (H : Fin n → Fin n → EvolutionVec n → ℝ)
    (hu : ContinuousOn u U) (hT : ContinuousOn T U)
    (hV : ∀ i, ContinuousOn (V i) U) (hZ : ∀ i, ContinuousOn (Z i) U)
    (hH : ∀ i j, ContinuousOn (H i j) U)
    (hdT : ∀ x ∈ U, HasLineDerivAt ℝ u (T x) x basisT)
    (hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (V i x) x (basisV i))
    (hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (Z i x) x (basisZ i))
    (hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, (T x +
        (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
        (∑ i, b (diffusedCoord n x) i * Z i x)) * ψ x := by
  let A i j (x : EvolutionVec n) :=
    B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j
  let β i (x : EvolutionVec n) := b (diffusedCoord n x) i
  let D (v : EvolutionVec n) (φ : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ φ x v
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (A i j) := fun i j =>
    (hB i j).comp (evolutionProdCLE n).contDiff
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (β i) := fun i =>
    (contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff
  have hD : ∀ v φ, ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (D v φ) :=
    fun v _ hφ => contDiff_fderiv_apply hφ v
  have hDc : ∀ v φ, HasCompactSupport φ → HasCompactSupport (D v φ) :=
    fun v φ hφ => hφ.fderiv_apply (𝕜 := ℝ) v
  have hDs : ∀ v φ, tsupport (D v φ) ⊆ tsupport φ :=
    fun v φ => tsupport_evolution_fderiv_apply φ v
  have eqT : (∫ x in U, u x * D basisT ψ x) = -∫ x in U, T x * ψ x :=
    setIntegral_mul_evolution_directional_test hu hT basisT hdT hψ hc hs
  have eqH : ∀ i j,
      (∫ x in U, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) =
        ∫ x in U, (A i j x * H i j x) * ψ x := by
    intro i j
    have h := setIntegral_mul_evolution_second_test hu (hV i) (hH i j)
      (basisV i) (basisV j) (hdV i) (hdH i j) ((hA i j).mul hψ)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
    convert h using 1
    congr 1
    funext x
    ring
  have eqZ : ∀ i, (∫ x in U, u x * (β i x * D (basisZ i) ψ x)) =
      -∫ x in U, (β i x * Z i x) * ψ x := by
    intro i
    have he : D (basisZ i) (fun y => β i y * ψ y) =
        fun x => β i x * D (basisZ i) ψ x := by
      funext x
      dsimp only [D]
      rw [fderiv_fun_mul ((hβ i).differentiable (by simp) x)
        (hψ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      change β i x * fderiv ℝ ψ x (basisZ i) +
        ψ x * fderiv ℝ (fun y => b (diffusedCoord n y) i) x (basisZ i) = _
      rw [fderiv_drift_transported_zero hb, mul_zero, add_zero]

    have h := setIntegral_mul_evolution_directional_test hu (hZ i) (basisZ i)
      (hdZ i) ((hβ i).mul hψ) hc.mul_left (tsupport_mul_subset_right.trans hs)
    change (∫ z in U, u z * D (basisZ i) (fun y => β i y * ψ y) z) = _ at h
    rw [he] at h
    convert h using 1
    congr 2
    funext x
    ring
  have iT : IntegrableOn (fun x => u x * D basisT ψ x) U volume :=
    (integrable_evolution_mul_test hu (hD basisT ψ hψ).continuous
      (hDc basisT ψ hc) ((hDs basisT ψ).trans hs)).integrableOn (s := U)
  have iH : ∀ i j, IntegrableOn (fun x =>
      u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) U volume := by
    intro i j
    exact (integrable_evolution_mul_test hu
      (hD _ _ (hD _ _ ((hA i j).mul hψ))).continuous
      (hDc _ _ (hDc _ _ hc.mul_left))
      ((hDs _ _).trans ((hDs _ _).trans (tsupport_mul_subset_right.trans hs)))).integrableOn
  have iZ : ∀ i, IntegrableOn (fun x => u x * (β i x * D (basisZ i) ψ x)) U volume :=
    fun i => (integrable_evolution_mul_test hu
      ((hβ i).continuous.mul (hD _ _ hψ).continuous)
      (hDc _ _ hc).mul_left (tsupport_mul_subset_right.trans ((hDs _ _).trans hs))).integrableOn
  have jT : IntegrableOn (fun x => T x * ψ x) U volume :=
    (integrable_evolution_mul_test hT hψ.continuous hc hs).integrableOn (s := U)
  have jH : ∀ i j, IntegrableOn (fun x => (A i j x * H i j x) * ψ x) U volume :=
    fun i j => (integrable_evolution_mul_test ((hA i j).continuous.continuousOn.mul (hH i j))
      hψ.continuous hc hs).integrableOn (s := U)
  have jZ : ∀ i, IntegrableOn (fun x => (β i x * Z i x) * ψ x) U volume :=
    fun i => (integrable_evolution_mul_test ((hβ i).continuous.continuousOn.mul (hZ i))
      hψ.continuous hc hs).integrableOn (s := U)
  have sumInt {ι : Type} [Fintype ι] (f : ι → EvolutionVec n → ℝ)
      (hf : ∀ i, IntegrableOn (f i) U volume) :
      IntegrableOn (fun x => ∑ i, f i x) U volume :=
    integrable_finsetSum _ (fun i _ => hf i)
  change (∫ x in U, u x * (-D basisT ψ x +
    (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
    (∑ i, β i x * D (basisZ i) ψ x))) =
    ∫ x in U, (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x)) * ψ x
  have hleft : (fun x => u x * (-D basisT ψ x +
      (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
      (∑ i, β i x * D (basisZ i) ψ x))) =
      fun x => -(u x * D basisT ψ x) +
        (∑ i, ∑ j, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
        (∑ i, u x * (β i x * D (basisZ i) ψ x)) := by
    funext x
    simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum]

  rw [hleft]
  erw [integral_sub (iT.neg.add (sumInt _ (fun i => sumInt _ (iH i)))) (sumInt _ iZ),
    integral_add iT.neg (sumInt _ (fun i => sumInt _ (iH i))), integral_neg]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (iH i))]
  simp_rw [integral_finsetSum _ (fun j _ => iH _ j)]
  erw [integral_finsetSum _ (fun i _ => iZ i)]
  simp_rw [eqT, eqH, eqZ]
  simp only [neg_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  have hright : (fun x => (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x)) * ψ x) =
      fun x => T x * ψ x + (∑ i, ∑ j, (A i j x * H i j x) * ψ x) +
        (∑ i, (β i x * Z i x) * ψ x) := by
    funext x
    simp only [add_mul, Finset.sum_mul]
  rw [hright]
  erw [integral_add (jT.add (sumInt _ (fun i => sumInt _ (jH i)))) (sumInt _ jZ),
    integral_add jT (sumInt _ (fun i => sumInt _ (jH i)))]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (jH i))]
  simp_rw [integral_finsetSum _ (fun j _ => jH _ j)]
  erw [integral_finsetSum _ (fun i _ => jZ i)]

/-- Integration against the formal adjoint equals integration of the corresponding
continuous anisotropic jet. Every derivative relation is used in integration by parts. -/
theorem integral_regularizedAdjoint_of_jets (ε : ℝ)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (u T : EvolutionVec n → ℝ) (V Z : Fin n → EvolutionVec n → ℝ)
    (H : Fin n → Fin n → EvolutionVec n → ℝ) (K : Fin n → EvolutionVec n → ℝ)
    (hu : ContinuousOn u U) (hT : ContinuousOn T U)
    (hV : ∀ i, ContinuousOn (V i) U) (hZ : ∀ i, ContinuousOn (Z i) U)
    (hH : ∀ i j, ContinuousOn (H i j) U) (hK : ∀ i, ContinuousOn (K i) U)
    (hdT : ∀ x ∈ U, HasLineDerivAt ℝ u (T x) x basisT)
    (hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (V i x) x (basisV i))
    (hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (Z i x) x (basisZ i))
    (hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j))
    (hdK : ∀ i x, x ∈ U → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, (T x +
        (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
        (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x) * ψ x := by
  let D (v : EvolutionVec n) (φ : EvolutionVec n → ℝ) (x : EvolutionVec n) := fderiv ℝ φ x v
  let Δ (x : EvolutionVec n) := ∑ i, D (basisZ i) (D (basisZ i) ψ) x
  have hj (i : Fin n) : IntegrableOn (fun x => K i x * ψ x) U volume :=
    (integrable_evolution_mul_test (hK i) hψ.continuous hc hs).integrableOn (s := U)
  have hi (i : Fin n) : IntegrableOn (fun x => u x * D (basisZ i) (D (basisZ i) ψ) x) U volume :=
    (integrable_evolution_mul_test hu
      (contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _).continuous
      ((hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _)
      ((tsupport_evolution_fderiv_apply _ _).trans
        ((tsupport_evolution_fderiv_apply ψ _).trans hs))).integrableOn
  have hiΔ : IntegrableOn (fun x => u x * Δ x) U volume := by
    simp only [Δ, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => hi i
  have hjΔ : IntegrableOn (fun x => (∑ i, K i x) * ψ x) U volume := by
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ => hj i
  have hLap : (∫ x in U, u x * Δ x) = ∫ x in U, (∑ i, K i x) * ψ x := by
    simp only [Δ, Finset.mul_sum, Finset.sum_mul]
    rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i)]
    exact Finset.sum_congr rfl fun i _ =>
      setIntegral_mul_evolution_second_test hu (hZ i) (hK i) _ _ (hdZ i) (hdK i) hψ hc hs
  have hAdj := (integrable_evolution_mul_test hu
    (contDiff_transportedAdjoint hB hb hψ).continuous (hasCompactSupport_transportedAdjoint hc)
    ((tsupport_transportedAdjoint_subset ψ).trans hs)).integrableOn (s := U)
  have hJet := integral_transportedAdjoint_of_anisotropic_jets B b hB hb u T V Z H
    hu hT hV hZ hH hdT hdV hdZ hdH ψ hψ hc hs
  let F (x : EvolutionVec n) := T x +
    (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
    (∑ i, b (diffusedCoord n x) i * Z i x)
  have hF : ContinuousOn F U := by
    refine (hT.add (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hB i j).comp (evolutionProdCLE n).contDiff).continuous.continuousOn.mul (hH i j))).add ?_
    exact continuousOn_finsetSum _ fun i _ =>
      (((contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff).continuous.continuousOn).mul (hZ i)
  have hFi := (integrable_evolution_mul_test hF hψ.continuous hc hs).integrableOn (s := U)
  change (∫ x in U, u x * (transportedAdjoint B b ψ x + ε * Δ x)) =
    ∫ x in U, (F x + ε * ∑ i, K i x) * ψ x
  simp only [mul_add, add_mul, mul_left_comm (u _) ε, mul_assoc ε]
  rw [integral_add hAdj (hiΔ.const_mul ε), integral_const_mul, hLap,
    integral_add hFi (hjΔ.const_mul ε), integral_const_mul, hJet]

end

section
variable {n : ℕ} {U : Set (EvolutionVec n)} (hU : IsOpen U)
include hU

/-- Integration against the regularized adjoint equals integration of the classical
operator for a C² interior function. -/
theorem integral_regularizedAdjoint_contDiffOn_two {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) (ε : ℝ) {u : EvolutionVec n → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * regularizedAdjoint B b ε ψ x) =
      ∫ x in U, regularizedOperator B b ε u x * ψ x := by
  let D (v : EvolutionVec n) (f : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ f x v
  have hd : ∀ v, ContDiffOn ℝ 1 (D v u) U :=
    fun v => (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hdd : ∀ v w, ContinuousOn (D w (D v u)) U :=
    fun v w => ((hd v).fderiv_of_isOpen (m := 0) hU (by norm_num)).clm_apply
      contDiffOn_const |>.continuousOn
  have hline : ∀ v x, x ∈ U → HasLineDerivAt ℝ u (D v u x) x v := by
    intro v x hx
    exact ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      ).hasFDerivAt.hasLineDerivAt v
  have hline2 : ∀ v w x, x ∈ U →
      HasLineDerivAt ℝ (D v u) (D w (D v u) x) x w := by
    intro v w x hx
    exact (((hd v).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      ).hasFDerivAt.hasLineDerivAt w
  have key := integral_regularizedAdjoint_of_jets B b ε hB hb u (D basisT u)
    (fun i => D (basisV i) u) (fun i => D (basisZ i) u)
    (fun i j => D (basisV j) (D (basisV i) u))
    (fun i => D (basisZ i) (D (basisZ i) u))
    hu.continuousOn (hd basisT).continuousOn
    (fun i => (hd (basisV i)).continuousOn) (fun i => (hd (basisZ i)).continuousOn)
    (fun i j => hdd (basisV i) (basisV j))
    (fun i => hdd (basisZ i) (basisZ i))
    (hline basisT) (fun i => hline (basisV i)) (fun i => hline (basisZ i))
    (fun i j => hline2 (basisV i) (basisV j))
    (fun i => hline2 (basisZ i) (basisZ i)) ψ hψ hc hs
  refine key.trans (setIntegral_congr_fun hU.measurableSet fun x _ => ?_)
  congr 1
  dsimp only [D, regularizedOperator, transportedOperator]
  congr 1
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (congrFun (hBs (timeCoord n x) (diffusedCoord n x)
    (transportedCoord n x)) i) j

private theorem smooth_direction
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v : EvolutionVec n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ u x v) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- The regularized kinetic operator of a smooth function is smooth on an open set. -/
theorem contDiffOn_regularizedOperator
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    {b : PDE.Vec n → PDE.Vec n} (hb : IsSmoothDrift b) (ε : ℝ)
    {u : EvolutionVec n → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (regularizedOperator B b ε u) U := by
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionVec n =>
      B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE n).contDiff
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionVec n => b (diffusedCoord n x) i) :=
    fun i => (contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff
  unfold regularizedOperator transportedOperator
  refine (((smooth_direction hU hu basisT).add ?_).add ?_).add ?_
  · exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hA i j).contDiffOn.mul
      (smooth_direction hU (smooth_direction hU hu (basisV j)) (basisV i))
  · exact ContDiffOn.sum fun i _ => (hβ i).contDiffOn.mul
      (smooth_direction hU hu (basisZ i))
  · exact contDiffOn_const.mul (ContDiffOn.sum fun i _ =>
      smooth_direction hU (smooth_direction hU hu (basisZ i)) (basisZ i))

end

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
