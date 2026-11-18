module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace MatrixOrder







/-- A continuous affine linear field on a compact interval has a solution on that interval. -/
theorem exists_linear_ode_on_Icc
    {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : ℝ → Fin n → ℝ)
    (hA : ContinuousOn A (Set.Icc a b))
    (hf : ContinuousOn f (Set.Icc a b))
    (x0 : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ,
      x a = x0 ∧
      ContinuousOn x (Set.Icc a b) ∧
      ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt x (A t (x t) + f t) (Set.Icc a b) t      := by
  let clip {n : ℕ} (R : NNReal) (z : Fin n → ℝ) :=
    fun i => (Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)
  have clip_eq_self_of_norm_lt {R : NNReal} {z : Fin n → ℝ} (hz : ‖z‖ < R) :
      clip R z = z := by
    ext i
    have hzi :=
      (norm_le_pi_norm z i).trans_lt hz
    rw [Real.norm_eq_abs] at hzi
    have hz_mem : z i ∈ Set.Icc (-(R : ℝ)) (R : ℝ) :=
      ⟨(abs_lt.mp hzi).1.le, (abs_lt.mp hzi).2.le⟩
    change ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
      Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) = z i
    simpa using congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self R.2) hz_mem)
  have norm_clip_le {n : ℕ} (R : NNReal) (z : Fin n → ℝ) :
      ‖clip R z‖ ≤ ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => ?_
    have hzero : (0 : ℝ) ∈ Set.Icc (-(R : ℝ)) (R : ℝ) := by
      exact ⟨neg_nonpos.mpr R.2, R.2⟩
    have h := (LipschitzWith.projIcc (neg_le_self R.2)).dist_le_mul (z i) 0
    have hprojzero :
        ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) 0 :
          Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) = 0 := by
      simpa using congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self R.2) hzero)
    change ‖(Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)‖ ≤ ‖z‖
    rw [← dist_zero_right]
    calc
      dist ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
        Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) 0 =
          dist ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) :
            Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ)
            ((Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) 0 :
              Set.Icc (-(R : ℝ)) (R : ℝ)) : ℝ) := by
        rw [hprojzero]
      _ ≤ (1 : ℝ) * dist (z i) 0 := h
      _ = ‖z i‖ := by simp
      _ ≤ ‖z‖ := norm_le_pi_norm z i
  have norm_clip_le_radius {n : ℕ} (R : NNReal) (z : Fin n → ℝ) :
      ‖clip R z‖ ≤ R := by
    refine (pi_norm_le_iff_of_nonneg R.2).mpr fun i => ?_
    change ‖(Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)‖ ≤ R
    rw [Real.norm_eq_abs]
    exact abs_le.2 (Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i)).property
  have lipschitzWith_clip (R : NNReal) :
      LipschitzWith 1 (clip (n := n) R) := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) dist_nonneg)).mpr fun i => ?_
    change dist (clip R z i) (clip R w i) ≤ (1 : ℝ) * dist z w
    calc
      dist (clip R z i) (clip R w i) ≤ (1 : ℝ) * dist (z i) (w i) := by
        exact (LipschitzWith.projIcc (neg_le_self R.2)).dist_le_mul _ _
      _ ≤ (1 : ℝ) * dist z w := by
        gcongr
        simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (z - w) i
  let t0 : Set.Icc a b := ⟨a, le_rfl, hab⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC_nonneg :=
    (norm_nonneg (A a)).trans (hC a t0.2)
  have hD_nonneg :=
    (norm_nonneg (f a)).trans (hD a t0.2)
  let Cnn : NNReal := Real.toNNReal C
  let Dnn : NNReal := Real.toNNReal D
  have hCnn : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ (Cnn : ℝ) := by
    intro t ht
    simpa only [Cnn, Real.coe_toNNReal _ hC_nonneg] using hC t ht
  have hDnn : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ (Dnn : ℝ) := by
    intro t ht
    simpa only [Dnn, Real.coe_toNNReal _ hD_nonneg] using hD t ht
  let G : ℝ := gronwallBound ‖x0‖ C D (b - a)
  let R : NNReal := Real.toNNReal (|G| + 1)
  let L : NNReal := Cnn * R + Dnn
  let r : NNReal := ‖x0‖₊
  let T : NNReal := Real.toNNReal (b - a)
  let q : NNReal := r + L * T
  let g : ℝ → (Fin n → ℝ) → Fin n → ℝ :=
    fun t z => A t (clip R z) + f t
  have hT_nonneg := sub_nonneg.mpr hab
  have hT : (T : ℝ) = b - a := by
    simp only [T, Real.coe_toNNReal _ hT_nonneg]
  have hG_lt_R : G < (R : ℝ) := by
    dsimp [R]
    exact (lt_add_of_le_of_pos (le_abs_self G) zero_lt_one).trans_le (le_max_left _ _)
  have hPL : IsPicardLindelof g t0 0 q r L Cnn := {
    lipschitzOnWith := by
      intro t ht
      apply (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
      calc
        dist (g t z) (g t w) = dist (A t (clip R z)) (A t (clip R w)) := by
          simp only [g, dist_add_right]
        _ ≤ ‖A t‖ * dist (clip R z) (clip R w) := (A t).dist_le_opNorm _ _
        _ ≤ (Cnn : ℝ) * dist (clip R z) (clip R w) := by
          gcongr
          exact hCnn t ht
        _ ≤ (Cnn : ℝ) * ((1 : ℝ) * dist z w) := by
          gcongr
          exact (lipschitzWith_clip R).dist_le_mul z w
        _ = (Cnn : ℝ) * dist z w := by ring
    continuousOn := by
      intro z hz
      simpa only [g] using
        (hA.clm_apply continuousOn_const).fun_add hf
    norm_le := by
      intro t ht z hz
      calc
        ‖g t z‖ ≤ ‖A t (clip R z)‖ + ‖f t‖ := norm_add_le _ _
        _ ≤ (Cnn : ℝ) * ‖clip R z‖ + (Dnn : ℝ) := by
          gcongr
          · exact (A t).le_of_opNorm_le (hCnn t ht) _
          · exact hDnn t ht
        _ ≤ (Cnn : ℝ) * (R : ℝ) + (Dnn : ℝ) := by
          gcongr
          exact norm_clip_le_radius R z
        _ = (L : ℝ) := by simp only [L, NNReal.coe_add, NNReal.coe_mul]
    mul_max_le := by
      calc
        (L : ℝ) * max (b - (t0 : ℝ)) ((t0 : ℝ) - a) ≤ (L : ℝ) * (b - a) := by
          simp only [t0, sub_self, max_eq_left hT_nonneg]
          exact le_rfl
        _ = (q : ℝ) - (r : ℝ) := by
          dsimp [q]
          rw [NNReal.coe_add, NNReal.coe_mul, hT]
          ring }
  have hx0_ball : x0 ∈ Metric.closedBall (0 : Fin n → ℝ) r := by
    simpa only [r, Metric.mem_closedBall, dist_zero_right, coe_nnnorm] using (le_refl ‖x0‖)
  obtain ⟨x, hx0, hdx⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx0_ball
  have hx_cont : ContinuousOn x (Set.Icc a b) := fun t ht =>
    (hdx t ht).continuousWithinAt
  have hdx_right : ∀ t ∈ Set.Ico a b, HasDerivWithinAt x (g t (x t)) (Set.Ici t) t := by
    intro t ht
    exact (hdx t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hg_bound : ∀ t ∈ Set.Ico a b, ‖g t (x t)‖ ≤ C * ‖x t‖ + D := by
    intro t ht
    calc
      ‖g t (x t)‖ ≤ ‖A t (clip R (x t))‖ + ‖f t‖ := norm_add_le _ _
      _ ≤ ‖A t‖ * ‖clip R (x t)‖ + D := by
        gcongr
        · exact (A t).le_of_opNorm_le le_rfl _
        · exact hD t (Set.Ico_subset_Icc_self ht)
      _ ≤ C * ‖clip R (x t)‖ + D := by
        gcongr
        exact hC t (Set.Ico_subset_Icc_self ht)
      _ ≤ C * ‖x t‖ + D := by
        gcongr
        exact norm_clip_le R (x t)
  have hxG : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ G := by
    intro t ht
    have hxa : ‖x a‖ ≤ ‖x0‖ := by
      rw [show a = (t0 : ℝ) by rfl, hx0]
    refine (norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖x0‖)
      hx_cont hdx_right hxa hg_bound t ht).trans ?_
    · simpa only [G] using
        gronwallBound_mono (norm_nonneg x0) hD_nonneg hC_nonneg
          (sub_le_sub_right ht.2 a)
  have hclip : ∀ t ∈ Set.Icc a b, clip R (x t) = x t := by
    intro t ht
    apply clip_eq_self_of_norm_lt
    exact (hxG t ht).trans_lt hG_lt_R
  refine ⟨x, hx0, hx_cont, ?_⟩
  intro t ht
  simpa only [g, hclip t ht] using hdx t ht




private theorem bilinear_mulVec_eq_coe_submodule_sum
    {I E : Type} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) (L : E →L[ℝ] E →L[ℝ] ℝ)
    (e : I → p) (x : I → ℝ) (i : I) :
    ((fun i j => L (e j : E) (e i : E)) *ᵥ x) i =
      L (↑(∑ j, x j • e j) : E) (e i : E) := by
  have hcoe : (↑(∑ j, x j • e j) : E) = ∑ j, x j • (e j : E) := by
    simpa only [Submodule.coe_smul] using
      (Submodule.coe_sum (p := p) (fun j => x j • e j) Finset.univ)
  change (∑ j, L (e j : E) (e i : E) * x j) =
    L (↑(∑ j, x j • e j) : E) (e i : E)
  calc
    _ = ∑ j, L (x j • (e j : E)) (e i : E) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [L.map_smul, ContinuousLinearMap.smul_apply]
      exact mul_comm _ _
    _ = (∑ j, L (x j • (e j : E))) (e i : E) := by
      exact (map_sum (ContinuousLinearMap.apply ℝ ℝ (e i : E))
        (fun j => L (x j • (e j : E))) Finset.univ).symm
    _ = L (∑ j, x j • (e j : E)) (e i : E) := by rw [← map_sum]
    _ = _ := congrArg (fun u => L u (e i : E)) hcoe.symm







private theorem gram_mulVec_eq_inner_sum
    {I E : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : I → E) (x : I → ℝ) (i : I) :
    (Matrix.gram ℝ v *ᵥ x) i = inner ℝ (∑ j, x j • v j) (v i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, sum_inner, inner_smul_left,
    starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  exact mul_comm _ _


private theorem weak_rows_iff_matrix_rows
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      ∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
          x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i   := by
  have galerkinMass_mulVec_eq_inner_reconstruct {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
      (galerkinMassGram hΩ N *ᵥ x) i =
      inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
    have map_galerkinBasis_sum {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : H10HilbertGraph hΩ →L[ℝ] W) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
        L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
        ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
      have hcoe : (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
          ∑ j, x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
        simpa only [Submodule.coe_smul] using
          (Submodule.coe_sum (p := galerkinSpace hΩ N)
            (fun j => x j • galerkinSpaceBasis hΩ N j) Finset.univ)
      calc
        L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
            L (∑ j, x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) := congrArg L hcoe
        _ = ∑ j, L (x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) :=
          map_sum L (fun j => x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) Finset.univ
        _ = ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
          apply Finset.sum_congr rfl
          intro j _
          exact L.map_smul (x j) (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
    rw [galerkinReconstruct_apply]
    let v : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
      fun j => valueCLM hΩ (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
    calc
      (galerkinMassGram hΩ N *ᵥ x) i = (Matrix.gram ℝ v *ᵥ x) i := rfl
      _ = inner ℝ (∑ j, x j • v j) (v i) := gram_mulVec_eq_inner_sum v x i
      _ = inner ℝ
          (valueCLM hΩ (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ))
          (v i) := congrArg (fun z => inner ℝ z (v i))
            (map_galerkinBasis_sum hΩ N (valueCLM hΩ) x).symm
  have stiffness_mulVec_eq_form {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
      x) i = reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
    have operator_reconstruct_eq_raw_form {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
      exact reverseTimeSpatialFormOperator_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        τ _ _
    have operator_sum_eq_operator_reconstruct {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
      have coe_galerkinReconstruct_eq_sum {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
          (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) := by
        exact congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
          (galerkinReconstruct_apply hΩ N x)
      let L :=
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
      let v := galerkinSpaceBasis hΩ N i
      exact congrArg (fun u => L u v) (coe_galerkinReconstruct_eq_sum hΩ N x).symm
    have stiffness_mulVec_eq_operator_sum {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x) i =
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
      let L :=
        reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
      let e :=
        galerkinSpaceBasis hΩ N
      change ((fun r s => L (e s : H10HilbertGraph hΩ) (e r : H10HilbertGraph hΩ)) *ᵥ x) i = _
      exact bilinear_mulVec_eq_coe_submodule_sum (galerkinSpace hΩ N) L e x i
    calc
      _ = reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) :=
        stiffness_mulVec_eq_operator_sum r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
          N τ x i
      _ = reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) :=
        operator_sum_eq_operator_reconstruct r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
          N τ x i
      _ = _ :=
        operator_reconstruct_eq_raw_form r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
          N τ x i
  constructor <;> intro h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i

private theorem matrix_coordinateEquation_iff
    {I : Type} [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x xdot : I → ℝ) (hdet : IsUnit M.det) :
    (∀ i, (M *ᵥ xdot) i + (K *ᵥ x) i = q i) ↔
      xdot = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
  constructor
  · intro h
    have hmk : M *ᵥ xdot + K *ᵥ x = q := by
      ext i
      exact h i
    have hsolve := (eq_sub_iff_add_eq).2 hmk
    calc
      xdot = (1 : Matrix I I ℝ) *ᵥ xdot := (Matrix.one_mulVec _).symm
      _ = (M⁻¹ * M) *ᵥ xdot := by rw [Matrix.nonsing_inv_mul M hdet]
      _ = M⁻¹ *ᵥ (M *ᵥ xdot) := (Matrix.mulVec_mulVec xdot M⁻¹ M).symm
      _ = M⁻¹ *ᵥ (q - K *ᵥ x) := by rw [hsolve]
      _ = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
        rw [Matrix.mulVec_sub]
        abel
  · intro h
    have hmul : M *ᵥ xdot + K *ᵥ x = q := by
      have hstiff : M *ᵥ (M⁻¹ *ᵥ (K *ᵥ x)) = K *ᵥ x := by
        rw [Matrix.mulVec_mulVec (K *ᵥ x) M M⁻¹, Matrix.mul_nonsing_inv M hdet,
          Matrix.one_mulVec]
      have hsource : M *ᵥ (M⁻¹ *ᵥ q) = q := by
        rw [Matrix.mulVec_mulVec q M M⁻¹, Matrix.mul_nonsing_inv M hdet,
          Matrix.one_mulVec]
      rw [h, Matrix.mulVec_add, Matrix.mulVec_neg, hstiff, hsource]
      abel
    intro i
    exact congrFun hmul i

private theorem matrix_solution_eq_continuousMulVec_rhs
    {I : Type} [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x : I → ℝ) :
    -(M *ᵥ (K *ᵥ x)) + M *ᵥ q =
      (- LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M * K))) x + M *ᵥ q := by
  change -(M *ᵥ (K *ᵥ x)) + M *ᵥ q =
    -((M * K) *ᵥ x) + M *ᵥ q
  rw [Matrix.mulVec_mulVec]

private theorem matrix_solution_eq_reverseTimeGalerkin_rhs
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    -((galerkinMassGram hΩ N)⁻¹ *ᵥ
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x)) +
      (galerkinMassGram hΩ N)⁻¹ *ᵥ
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ =
      reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  change -((galerkinMassGram hΩ N)⁻¹ *ᵥ
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x)) +
      (galerkinMassGram hΩ N)⁻¹ *ᵥ
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ =
      (- LinearMap.toContinuousLinearMap (Matrix.mulVecLin
        ((galerkinMassGram hΩ N)⁻¹ *
          reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
            N τ))) x +
        (galerkinMassGram hΩ N)⁻¹ *ᵥ
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  exact matrix_solution_eq_continuousMulVec_rhs (galerkinMassGram hΩ N)⁻¹
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ)
    (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) x

private theorem eq_iff_eq_of_eq_right {E : Type} (x y z : E) (hyz : y = z) :
    (x = y ↔ x = z) := by
  rw [hyz]

private theorem matrix_rows_iff_reverseTimeGalerkin_rhs
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ *ᵥ x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  let M := galerkinMassGram hΩ N
  let K :=
    reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
  let q :=
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  have hdet := (M.isUnit_iff_isUnit_det).mp (isUnit_galerkinMassGram hΩ N)
  have hrhs := matrix_solution_eq_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N τ x
  exact (matrix_coordinateEquation_iff M K q x xdot hdet).trans
    (eq_iff_eq_of_eq_right xdot (-(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q)
      (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) hrhs)

private theorem reverseTimeGalerkin_coordinateEquation_iff_aux
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
          x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  exact (weak_rows_iff_matrix_rows r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
    hFSmooth N τ x xdot).trans
    (matrix_rows_iff_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth
      hcSmooth hFSmooth N τ x xdot)

/-- The finite weak-coordinate equation is exactly the mass-inverted local linear ODE.
This theorem neither constructs nor solves a curve. -/
theorem reverseTimeGalerkin_coordinateEquation_iff
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
          x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  exact reverseTimeGalerkin_coordinateEquation_iff_aux r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth
    hbSmooth hcSmooth hFSmooth N τ x xdot



/-- A reverse-time finite Galerkin coordinate solution and its reconstruction exist. -/
theorem exists_reverseTimeGalerkin_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun
          (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧
        ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ
                (valueCLM hΩ (galerkinReconstruct hΩ N
                  (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth N τ (x τ) +
                  reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                    H10HilbertGraph hΩ))
                (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
              reverseTimeSpatialForm hΩ r₁ τ.1 a b c
                (u τ : H10HilbertGraph hΩ)
                (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
              reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) := by
  let T := r₁ - r₀
  have hT := sub_nonneg.mpr h₀₁.le
  let x0 :=
    (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial)
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :=
    fun τ => reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
    fun τ => reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  have hA : ContinuousOn A (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N).comp continuous_projIcc).continuousOn
  have hf : ContinuousOn f (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N).comp
      continuous_projIcc).continuousOn
  have hode := exists_linear_ode_on_Icc hT A f hA hf x0
  let x := hode.choose
  have hx0 := hode.choose_spec.1
  have hxcont := hode.choose_spec.2.1
  have hdx := hode.choose_spec.2.2
  let u : ℝ → galerkinSpace hΩ N := fun τ => galerkinReconstruct hΩ N (x τ)
  have hucont : ContinuousOn u (Set.Icc 0 T) := by
    exact (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N)).continuous.continuousOn
      |>.comp hxcont (fun _ _ => Set.mem_univ _)
  refine ⟨x, u, ?_, rfl, hxcont, hucont, ?_⟩
  · simpa only [x0] using hx0
  intro τ
  have hproj : Set.projIcc 0 T hT (τ : ℝ) = τ := Set.projIcc_of_mem hT τ.2
  constructor
  · simpa only [A, f, hproj] using hdx τ τ.2
  · simpa only [u] using
      (reverseTimeGalerkin_coordinateEquation_iff r₀ r₁ h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth N τ (x τ)
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)).mpr rfl



private def galerkinEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

private def galerkinEnergyDeriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  2 * inner ℝ
    (valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
    (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))

private def galerkinGradientEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  ‖gradientCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

private theorem sum_smul_inner_right
    {I E : Type} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (e : I → E) (x : I → ℝ) :
    ∑ i, x i * inner ℝ v (e i) = inner ℝ v (∑ i, x i • e i) := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right]



private theorem reverseTimeGalerkin_rows_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hrows : ∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) :
    inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      reverseTimeSourceFunctional hΩ
        (reverseTimeSourceSlice r₁ τ.1 F
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
            τ.1 τ.2))
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)  := by
  have map_galerkinReconstruct_sum {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (Q : H10HilbertGraph hΩ →L[ℝ] Z) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
      Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
    have coe_galerkinReconstruct_eq_sum {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
        (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
      exact congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
        (galerkinReconstruct_apply hΩ N x)
    calc
      Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
          Q (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
        exact congrArg Q (coe_galerkinReconstruct_eq_sum hΩ N x)
      _ = Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
        have hcoe : (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) =
            ∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
          simpa only [Submodule.coe_smul] using
          (Submodule.coe_sum (p := galerkinSpace hΩ N)
            (fun i => x i • galerkinSpaceBasis hΩ N i) Finset.univ)
        exact congrArg Q hcoe
      _ = ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
        calc
          Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) =
              ∑ i, Q (x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) :=
            map_sum Q (fun i => x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))
              Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            exact Q.map_smul (x i) (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)
  let vdot :=
    valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)
  let u := galerkinReconstruct hΩ N x
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → H10HilbertGraph hΩ :=
    fun i => galerkinSpaceBasis hΩ N i
  let B :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ u
  let q :=
    reverseTimeSourceFunctional hΩ
      (reverseTimeSourceSlice r₁ τ.1 F
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
          τ.1 τ.2))
  have hsum : ∑ i, x i *
      (inner ℝ vdot (valueCLM hΩ (e i)) + B (e i)) =
      ∑ i, x i * q (e i) := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [vdot, e, B, q, reverseTimeSpatialFormOperator_apply,
      reverseTimeGalerkinSource_eq] using congrArg (fun z => x i * z) (hrows i)
  have hsum_left : ∑ i, x i *
      (inner ℝ vdot (valueCLM hΩ (e i)) + B (e i)) =
      inner ℝ vdot (valueCLM hΩ u) + B u := by
    have hvalue := map_galerkinReconstruct_sum hΩ N (valueCLM hΩ) x
    have hform := map_galerkinReconstruct_sum hΩ N B x
    have hinner : ∑ i, x i * inner ℝ vdot (valueCLM hΩ (e i)) =
        inner ℝ vdot (valueCLM hΩ u) := by
      change ∑ i, x i * inner ℝ vdot
        (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) = _
      rw [sum_smul_inner_right]
      exact congrArg (inner ℝ vdot) hvalue.symm
    have hB : ∑ i, x i * B (e i) = B u := by
      change ∑ i, x i * B (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) = B u
      simpa only [smul_eq_mul] using hform.symm
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hinner, hB]
  have hsum_right : (∑ i, x i * q (e i)) = q u := by
    have hq := map_galerkinReconstruct_sum hΩ N q x
    change ∑ i, x i * q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) = q u
    simpa only [smul_eq_mul] using hq.symm
  simpa only [vdot, u, B, q, reverseTimeSpatialFormOperator_apply] using
    hsum_left.symm.trans (hsum.trans hsum_right)



private theorem energy_differential_algebra
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (lam K M : ℝ) (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ)
    (w f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (B : ℝ)
    (hidentity : inner ℝ w (valueCLM hΩ u) + B = -inner ℝ (valueCLM hΩ u) f)
    (hgarding : (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤ B)
    (hsource : ‖f‖ ≤ M) :
    2 * inner ℝ (valueCLM hΩ u) w ≤
      (2 * K + 1) * ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 -
        lam * ‖gradientCLM hΩ u‖ ^ 2 := by
  have hforcing : -inner ℝ (valueCLM hΩ u) f ≤ ‖valueCLM hΩ u‖ * M := by
    calc
      -inner ℝ (valueCLM hΩ u) f ≤ |inner ℝ (valueCLM hΩ u) f| := neg_le_abs _
      _ ≤ ‖valueCLM hΩ u‖ * ‖f‖ := abs_real_inner_le_norm (valueCLM hΩ u) f
      _ ≤ ‖valueCLM hΩ u‖ * M :=
        mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
  have hyoung : 2 * ‖valueCLM hΩ u‖ * M ≤ ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 := by
    nlinarith [sq_nonneg (‖valueCLM hΩ u‖ - M)]
  rw [real_inner_comm]
  nlinarith




private theorem continuousOn_two_mul_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set ℝ} (v w : ℝ → E)
    (hv : ContinuousOn v s) (hw : ContinuousOn w s) :
    ContinuousOn (fun t => 2 * inner ℝ (v t) (w t)) s := by
  exact continuousOn_const.mul (hv.inner hw)

private theorem galerkin_energy_deriv_ineq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam K M : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hGarding : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
      (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u)
    (hsource : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M)
    (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (τ : Set.Icc 0 (r₁ - r₀))
    (hdx : HasDerivWithinAt x
      (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth N τ (x τ) +
      reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
      (Set.Icc 0 (r₁ - r₀)) τ)
    (hrows : ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
              H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) :
    HasDerivWithinAt (galerkinEnergy hΩ N x)
      (galerkinEnergyDeriv hΩ N x
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) τ)
      (Set.Icc 0 (r₁ - r₀)) τ ∧
    galerkinEnergyDeriv hΩ N x
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) τ +
      lam * galerkinGradientEnergy hΩ N x τ ≤
      (2 * K + 1) * galerkinEnergy hΩ N x τ + M ^ 2  := by
  have hasDerivWithinAt_energy_reconstruct {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) {s : Set ℝ} {τ : ℝ} (hx : HasDerivWithinAt x xdot s τ) :
      HasDerivWithinAt
      (fun t => ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2)
      (2 * inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
    have hasDerivWithinAt_value_reconstruct {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) {s : Set ℝ} {τ : ℝ} (hx : HasDerivWithinAt x xdot s τ) :
        HasDerivWithinAt
        (fun t => valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)) s τ := by
      let R :=
        (galerkinSpace hΩ N).subtypeL.comp
          (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
      let V :=
        (valueCLM hΩ).comp R
      have hV := (V.hasFDerivAt).comp_hasDerivWithinAt τ hx
      simpa only [V, R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
        LinearMap.coe_toContinuousLinearMap'] using! hV
    exact (hasDerivWithinAt_value_reconstruct hΩ N x xdot hx).norm_sq
  let xdot := reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth N τ (x τ) +
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  let u := galerkinReconstruct hΩ N (x τ)
  let f :=
    reverseTimeSourceSlice r₁ τ.1 F
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
        τ.1 τ.2)
  have hderiv : HasDerivWithinAt (galerkinEnergy hΩ N x)
      (galerkinEnergyDeriv hΩ N x xdot τ) (Set.Icc 0 (r₁ - r₀)) τ := by
    simpa only [galerkinEnergy, galerkinEnergyDeriv] using!
      hasDerivWithinAt_energy_reconstruct hΩ N x xdot hdx
  refine ⟨hderiv, ?_⟩
  have hid := reverseTimeGalerkin_rows_sum r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N τ (x τ) xdot (by
      intro i
      simpa only [xdot] using hrows i)
  have hid' : inner ℝ
      (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
      (valueCLM hΩ u) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c u u =
      -inner ℝ (valueCLM hΩ u) f := by
    simpa only [u, f, reverseTimeSourceFunctional_apply] using hid
  have hbound := energy_differential_algebra lam K M hΩ u
    (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)) f
    (reverseTimeSpatialForm hΩ r₁ τ.1 a b c u u) hid'
    (hGarding τ.1 τ.2 u)
    (hsource τ.1 τ.2
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
        τ.1 τ.2))
  simpa only [galerkinEnergyDeriv, galerkinGradientEnergy, galerkinEnergy, xdot, u] using
    (le_sub_iff_add_le.mp hbound)

private theorem continuousOn_galerkinEnergyDeriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ)
    (hx : ContinuousOn x s) (hxdot : ContinuousOn xdot s) :
    ContinuousOn (fun t => galerkinEnergyDeriv hΩ N x (xdot t) t) s := by
  let R :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V :=
    (valueCLM hΩ).comp R
  have hVx :=
    V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  have hVxdot :=
    V.continuous.continuousOn.comp hxdot (fun _ _ => Set.mem_univ _)
  simpa only [galerkinEnergyDeriv, V, R, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
    LinearMap.coe_toContinuousLinearMap'] using!
    continuousOn_two_mul_inner _ _ hVx hVxdot

private theorem exists_galerkin_energy_constants
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
          reverseTimeSpatialForm hΩ r₁ τ a b c u u) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
          (2 : ℝ≥0∞) (PDE.volumeOn Ω),
          ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M := by
  obtain ⟨K, hK, hGarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  obtain ⟨M, hM, hsource⟩ :=
    exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
  exact ⟨K, hK, hGarding, M, hM, hsource⟩

private theorem reverseTimeGalerkin_uniform_energy_solution_fixed
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (K M : ℝ) (hK : 0 ≤ K)
    (hGarding : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
      (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u)
    (hsource : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M) :
    ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧ ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ (valueCLM hΩ (galerkinReconstruct hΩ N
              (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth N τ (x τ) +
              reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                H10HilbertGraph hΩ))
              (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
            reverseTimeSpatialForm hΩ r₁ τ.1 a b c (u τ : H10HilbertGraph hΩ)
              (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
            reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
        (∀ t ∈ Set.Icc 0 (r₁ - r₀),
          ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
            gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
        ∀ t ∈ Set.Icc 0 (r₁ - r₀),
          lam * ∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
            ‖initial‖ ^ 2 + (2 * K + 1) * t *
              gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (r₁ - r₀) + M ^ 2 * t    := by
  intro N initial
  have continuousOn_galerkinGradientEnergy {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn (galerkinGradientEnergy hΩ N x) s := by
    let R :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let W := (gradientCLM hΩ).comp R
    have hW :=
      W.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
    simpa only [galerkinGradientEnergy, W, R, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
      LinearMap.coe_toContinuousLinearMap'] using! hW.norm.pow 2
  have galerkinEnergy_zero_le_initial {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (hx0 : x 0 = (galerkinSpaceBasis hΩ N).equivFun
      (galerkinInitialProjection hΩ N initial)) :
      galerkinEnergy hΩ N x 0 ≤ ‖initial‖ ^ 2 := by
    have hrec : (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
        (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
      calc
        (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
            (galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun
              (galerkinInitialProjection hΩ N initial)) : H10HilbertGraph hΩ) :=
          congrArg (fun z => (galerkinReconstruct hΩ N z : H10HilbertGraph hΩ)) hx0
        _ = (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) :=
          congrArg (fun v : galerkinSpace hΩ N => (v : H10HilbertGraph hΩ))
            (galerkinReconstruct_equivFun hΩ N (galerkinInitialProjection hΩ N initial))
    rw [galerkinEnergy, hrec]
    have hnorm := norm_value_galerkinInitialProjection_le hΩ N initial
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  have continuousOn_galerkinEnergy {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn (galerkinEnergy hΩ N x) s := by
    let R :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let V :=
      (valueCLM hΩ).comp R
    have hV : ContinuousOn (fun t => V (x t)) s :=
      V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
    simpa only [galerkinEnergy, V, R, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
      LinearMap.coe_toContinuousLinearMap'] using! hV.norm.pow 2
  have hsol := exists_reverseTimeGalerkin_solution r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N initial
  let x := hsol.choose
  let u := hsol.choose_spec.choose
  have hspec := hsol.choose_spec.choose_spec
  have hx0 := hspec.1
  have hu := hspec.2.1
  have hxcont := hspec.2.2.1
  have hucont := hspec.2.2.2.1
  have hode := hspec.2.2.2.2
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) := fun t =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N
      (Set.projIcc 0 T hT t)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun t =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N (Set.projIcc 0 T hT t)
  let xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun t => A t (x t) + f t
  have hxdot : ContinuousOn xdot (Set.Icc 0 T) := by
    have hA : Continuous A := (continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth N).comp continuous_projIcc
    have hf : Continuous f := (continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F
      hFSmooth N).comp continuous_projIcc
    exact (hA.continuousOn.clm_apply hxcont).add hf.continuousOn
  let D : ℝ → ℝ := fun t => galerkinEnergyDeriv hΩ N x (xdot t) t
  have hDcont : ContinuousOn D (Set.Icc 0 T) :=
    continuousOn_galerkinEnergyDeriv hΩ N x xdot _ hxcont hxdot
  have hEcont := continuousOn_galerkinEnergy hΩ N x (Set.Icc 0 T) hxcont
  have hGcont := continuousOn_galerkinGradientEnergy hΩ N x (Set.Icc 0 T) hxcont
  have hEicc : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (galerkinEnergy hΩ N x) (D t) (Set.Icc 0 T) t := by
    intro t ht
    let τ : Set.Icc 0 (r₁ - r₀) := ⟨t, by simpa only [T] using ht⟩
    have hp : Set.projIcc 0 T hT t = τ := Set.projIcc_of_mem hT ht
    simpa only [D, xdot, A, f, T, hp] using
      (galerkin_energy_deriv_ineq r₀ r₁ lam K M h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hGarding hsource N x τ (hode τ).1
        (by simpa only [hu] using (hode τ).2)).1
  have hEineq : ∀ t ∈ Set.Icc 0 T,
      D t + lam * galerkinGradientEnergy hΩ N x t ≤
        (2 * K + 1) * galerkinEnergy hΩ N x t + M ^ 2 := by
    intro t ht
    let τ : Set.Icc 0 (r₁ - r₀) := ⟨t, by simpa only [T] using ht⟩
    have hp : Set.projIcc 0 T hT t = τ := Set.projIcc_of_mem hT ht
    simpa only [D, xdot, A, f, T, hp] using
      (galerkin_energy_deriv_ineq r₀ r₁ lam K M h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hGarding hsource N x τ (hode τ).1
        (by simpa only [hu] using (hode τ).2)).2
  have hE0 := galerkinEnergy_zero_le_initial hΩ N initial x hx0
  have hEbound : ∀ t ∈ Set.Icc 0 T,
      galerkinEnergy hΩ N x t ≤ gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t := by
    have hbound : ∀ t ∈ Set.Icc 0 T,
        galerkinEnergy hΩ N x t ≤
          gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (t - 0) := by
      apply le_gronwallBound_of_liminf_deriv_right_le hEcont
      · intro t ht r hr
        have hgrad : 0 ≤ lam * galerkinGradientEnergy hΩ N x t :=
          mul_nonneg hlam.le (sq_nonneg _)
        have hDle : D t ≤ (2 * K + 1) * galerkinEnergy hΩ N x t + M ^ 2 :=
          (le_add_of_nonneg_right hgrad).trans (hEineq t (Set.Ico_subset_Icc_self ht))
        exact ((hEicc t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht)).liminf_right_slope_le (hDle.trans_lt hr)
      · simpa only [T] using hE0
      · intro t ht
        have hg : 0 ≤ galerkinGradientEnergy hΩ N x t := sq_nonneg _
        linarith [hEineq t (Set.Ico_subset_Icc_self ht)]
    simpa only [sub_zero] using hbound
  refine ⟨x, u, hx0, hu, hxcont, hucont, hode, ?_, ?_⟩
  · intro t ht
    simpa only [u, hu, galerkinEnergy, T] using hEbound t ht
  intro t ht
  have htT : t ∈ Set.Icc 0 T := by simpa only [T] using ht
  let R := gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) T
  have hA0 : 0 ≤ 2 * K + 1 := by linarith
  have hconst : ∀ s ∈ Set.Icc 0 t,
      D s + lam * galerkinGradientEnergy hΩ N x s ≤ (2 * K + 1) * R + M ^ 2 := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans htT.2⟩
    have hER : galerkinEnergy hΩ N x s ≤ R := (hEbound s hsT).trans
      (gronwallBound_mono (sq_nonneg _) (sq_nonneg _) hA0 (hs.2.trans htT.2))
    have hmult := mul_le_mul_of_nonneg_left hER hA0
    linarith [hEineq s hsT]
  have hleft : IntervalIntegrable (fun s => D s + lam * galerkinGradientEnergy hΩ N x s)
      MeasureTheory.volume 0 t := ((hDcont.add (continuousOn_const.mul hGcont)).mono
        (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 t :=
    (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hGint : IntervalIntegrable (galerkinGradientEnergy hΩ N x)
      MeasureTheory.volume 0 t :=
    (hGcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hLGint : IntervalIntegrable (fun s => lam * galerkinGradientEnergy hΩ N x s)
      MeasureTheory.volume 0 t := hGint.const_mul lam
  have hint := intervalIntegral.integral_mono_on ht.1 hleft
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (2 * K + 1) * R + M ^ 2) MeasureTheory.volume 0 t)
    (by
      intro s hs
      exact hconst s hs)
  have hFTC : (∫ s in 0..t, D s) = galerkinEnergy hΩ N x t - galerkinEnergy hΩ N x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hEcont.mono (Set.Icc_subset_Icc le_rfl htT.2))
    · intro s hs
      have hsIcc : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.le.trans htT.2⟩
      have hsIco : s ∈ Set.Ico 0 T := ⟨hs.1.le, hs.2.trans_le htT.2⟩
      exact (hEicc s hsIcc).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hsIco)
    · exact (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  rw [intervalIntegral.integral_add hDint hLGint, intervalIntegral.integral_const_mul, hFTC,
    intervalIntegral.integral_const] at hint
  have hEt : 0 ≤ galerkinEnergy hΩ N x t := sq_nonneg _
  have hrhs : t * ((2 * K + 1) * R + M ^ 2) =
      (2 * K + 1) * t * R + M ^ 2 * t := by
    ring
  rw [sub_zero, smul_eq_mul, hrhs] at hint
  have hgrad : lam * (∫ s in 0..t, galerkinGradientEnergy hΩ N x s) ≤
      ‖initial‖ ^ 2 + (2 * K + 1) * t * R + M ^ 2 * t := by
    linarith [hint, hE0]
  simpa only [u, hu, galerkinGradientEnergy, R, T, intervalIntegral.integral_of_le ht.1] using
    hgrad

private theorem reverseTimeGalerkin_uniform_energy_solution_aux
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧ ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ (valueCLM hΩ (galerkinReconstruct hΩ N
              (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth N τ (x τ) +
              reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                H10HilbertGraph hΩ))
              (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
            reverseTimeSpatialForm hΩ r₁ τ.1 a b c (u τ : H10HilbertGraph hΩ)
              (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
            reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
        (∀ t ∈ Set.Icc 0 (r₁ - r₀),
          ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
            gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
        ∀ t ∈ Set.Icc 0 (r₁ - r₀),
          lam * ∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
            ‖initial‖ ^ 2 + (2 * K + 1) * t *
              gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (r₁ - r₀) + M ^ 2 * t := by
  let constants := exists_galerkin_energy_constants r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
  let K : ℝ := constants.choose
  have hK : 0 ≤ K := constants.choose_spec.1
  have hGarding := constants.choose_spec.2.1
  let M : ℝ := constants.choose_spec.2.2.choose
  have hM : 0 ≤ M := constants.choose_spec.2.2.choose_spec.1
  have hsource := constants.choose_spec.2.2.choose_spec.2
  refine ⟨K, hK, M, hM, ?_⟩
  exact reverseTimeGalerkin_uniform_energy_solution_fixed r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth K M hK hGarding hsource

/-- Smooth finite Galerkin systems have uniform primal energy bounds. -/
theorem exists_reverseTimeGalerkin_uniform_energy_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
          ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
            ∃ u : ℝ → galerkinSpace hΩ N,
              x 0 = (galerkinSpaceBasis hΩ N).equivFun
                (galerkinInitialProjection hΩ N initial) ∧
              u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
              ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧
              ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
              (∀ τ : Set.Icc 0 (r₁ - r₀),
                HasDerivWithinAt x
                  (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth N τ (x τ) +
                  reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
                  (Set.Icc 0 (r₁ - r₀)) τ ∧
                ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
                  inner ℝ
                      (valueCLM hΩ (galerkinReconstruct hΩ N
                        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                          haSmooth hbSmooth hcSmooth N τ (x τ) +
                        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                          H10HilbertGraph hΩ))
                      (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
                    reverseTimeSpatialForm hΩ r₁ τ.1 a b c
                      (u τ : H10HilbertGraph hΩ)
                      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
                    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
              (∀ t ∈ Set.Icc 0 (r₁ - r₀),
                ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
                  gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
              ∀ t ∈ Set.Icc 0 (r₁ - r₀),
                lam * ∫ τ in Set.Ioc 0 t,
                    ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
                  ‖initial‖ ^ 2 +
                    (2 * K + 1) * t *
                      gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2)
                        (r₁ - r₀) +
                    M ^ 2 * t := by
  exact reverseTimeGalerkin_uniform_energy_solution_aux r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos

end HypoellipticAleksandrov.Parabolic.Dirichlet

