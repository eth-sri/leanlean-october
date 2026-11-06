module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Global finite-coordinate linear ODEs on compact intervals

This file supplies the finite-dimensional nonautonomous linear ODE engine
needed by the Dirichlet Galerkin construction.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

noncomputable section

private def clip {n : ℕ} (R : NNReal) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (Set.projIcc (-(R : ℝ)) (R : ℝ) (neg_le_self R.2) (z i) : ℝ)

variable {n : ℕ} (R : NNReal) (z : Fin n → ℝ)

private theorem lipschitzWith_clip  :
    LipschitzWith 1 (clip (n := n) R) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) dist_nonneg)).mpr fun i => ?_
  change dist _ (clip R w i) ≤ (1) * dist z w
  calc
    dist _ _ ≤ (1) * dist _ _ := (LipschitzWith.projIcc _).dist_le_mul _ _
    _ ≤ (1) * dist z w := by
      gcongr
      simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (z - w) i

private theorem norm_clip_le_radius  :
    ‖clip R z‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg R.2).mpr fun i => ?_
  exact abs_le.2 (Set.projIcc _ _ _ _).property

private theorem norm_clip_le  :
    ‖clip R z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => ?_
  have hzero : (0) ∈ Set.Icc (-(R : ℝ)) R := ⟨neg_nonpos.mpr R.2, R.2⟩
  have h := (LipschitzWith.projIcc (neg_le_self R.2)).dist_le_mul (z i) 0
  have hprojzero :
      ((Set.projIcc _ _ (neg_le_self R.2) 0 :
        Set.Icc (-(R : ℝ)) _) : ℝ) = 0 := by
    simpa using congrArg Subtype.val (Set.projIcc_of_mem _ hzero)
  rw [← dist_zero_right]
  calc
    dist ((Set.projIcc _ _ _ _ :
      Set.Icc _ (R : ℝ)) : ℝ) 0 =
        dist ((Set.projIcc _ _ _ _ :
          Set.Icc (-(R : ℝ)) R) : ℝ)
          ((Set.projIcc _ _ _ 0 :
            Set.Icc (-(R : ℝ)) (R : ℝ))) := by
      simp_all
    _ ≤ (1) * dist _ 0 := h
    _ = ‖z i‖ := by simp
    _ ≤ ‖z‖ := norm_le_pi_norm z i

private theorem clip_eq_self_of_norm_lt  {R : NNReal} {z : Fin n → ℝ}
    (hz : ‖z‖ < R) : clip R z = z := by
  ext i
  have hzi : ‖z i‖ < R :=
    (norm_le_pi_norm z i).trans_lt hz
  have hz_mem : z i ∈ Set.Icc (-(R : ℝ)) _ :=
    ⟨(abs_lt.mp hzi).1.le, (abs_lt.mp hzi).2.le⟩
  change ((Set.projIcc _ _ (neg_le_self R.2) _ :
    Set.Icc (-(R : ℝ)) _)) = z i
  simpa using congrArg Subtype.val (Set.projIcc_of_mem _ hz_mem)

/-- A continuous affine linear field on a compact interval has a solution on that interval. -/
theorem exists_linear_ode_on_Icc
     {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : ℝ → Fin n → ℝ)
    (hA : ContinuousOn A (Set.Icc a b))
    (hf : ContinuousOn f (Set.Icc a b))
    (x0 : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ,
      x a = x0 ∧
      ContinuousOn x (Set.Icc a b) ∧
      ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt x (A t (x t) + f t) (Set.Icc a b) t := by
  let t0 : Set.Icc a b := ⟨a, le_rfl, hab⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg _).trans (hC a t0.2)
  have hD_nonneg : 0 ≤ D :=
    (norm_nonneg _).trans (hD a t0.2)
  let Cnn  := Real.toNNReal C
  let Dnn  := Real.toNNReal D
  have hCnn : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ Cnn := by
    aesop
  have hDnn : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ Dnn := by
    aesop
  let G  := gronwallBound ‖x0‖ C D (b - a)
  let R  := Real.toNNReal (|G| + 1)
  let L  := Cnn * R + Dnn
  let r  := ‖x0‖₊
  let T  := Real.toNNReal (b - a)
  let q  := r + L * T
  let g  :=
    fun t z => A t (clip R z) + f t
  have hT_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hT : T = b - a := by
    aesop
  have hG_lt_R : G < R := (lt_add_of_le_of_pos (le_abs_self G) zero_lt_one).trans_le (le_max_left _ _)
  have hPL : IsPicardLindelof g t0 0 q r L Cnn := {
    lipschitzOnWith := by
      intro t ht
      apply (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
      calc
        dist _ _ = dist _ _ := by
          aesop
        _ ≤ ‖A t‖ * dist (clip R z) (clip R w) := (A t).dist_le_opNorm _ _
        _ ≤ Cnn * dist _ _ := by
          gcongr
          simp_all
        _ ≤ Cnn * ((1) * dist z w) := by
          gcongr
          exact (lipschitzWith_clip R).dist_le_mul z w
        _ = Cnn * dist z w := by ring
    continuousOn := by
      fun_prop
    norm_le := by
      intro t ht z hz
      calc
        ‖g t z‖ ≤ ‖A t _‖ + ‖f t‖ := norm_add_le _ _
        _ ≤ Cnn * ‖clip R z‖ + Dnn := by
          gcongr
          · exact (A t).le_of_opNorm_le (hCnn t ht) _
          simp_all
        _ ≤ Cnn * R + Dnn := by
          gcongr
          exact norm_clip_le_radius R z
        _ = L := by aesop
    mul_max_le := by
      aesop }
  have hx0_ball : x0 ∈ Metric.closedBall (0) r := by
    aesop
  obtain ⟨x, hx0, hdx⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx0_ball
  have hx_cont : ContinuousOn x _ := fun t ht =>
    (hdx t ht).continuousWithinAt
  have hdx_right : ∀ t ∈ Set.Ico a b, HasDerivWithinAt x (g t (x t)) (Set.Ici t) t := by
    intro t ht
    exact (hdx t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hg_bound : ∀ t ∈ Set.Ico a b, ‖g t (x t)‖ ≤ C * ‖x t‖ + D := by
    intro t ht
    calc
      ‖g t _‖ ≤ ‖A t _‖ + ‖f t‖ := norm_add_le _ _
      _ ≤ ‖A t‖ * ‖clip R _‖ + D := by
        gcongr
        · exact (A t).le_of_opNorm_le le_rfl _
        grind
      _ ≤ C * ‖clip R _‖ + D := by
        gcongr
        grind
      _ ≤ C * ‖x t‖ + D := by
        gcongr
        exact norm_clip_le R _
  have hxG : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ G := by
    intro t ht
    have hxa : ‖x a‖ ≤ ‖x0‖ := by
      rw [hx0]
    refine (norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖x0‖)
      hx_cont hdx_right hxa hg_bound t ht).trans ?_
    · simpa only [G] using
        gronwallBound_mono (norm_nonneg x0) hD_nonneg hC_nonneg
          (sub_le_sub_right ht.2 a)
  have hclip : ∀ t ∈ Set.Icc a b, clip R (x t) = x t := by
    intro t ht
    apply clip_eq_self_of_norm_lt
    grind
  grind

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
