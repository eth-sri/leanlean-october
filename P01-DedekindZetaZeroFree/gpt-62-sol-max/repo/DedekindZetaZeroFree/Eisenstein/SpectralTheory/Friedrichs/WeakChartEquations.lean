module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.VariationalChartEquation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

attribute [-instance] DedekindZetaZeroFree.PGLComplex.AdelicSlices.instMeasurableSpaceActualCover

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFriedrichsWeakChart

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def inverseMetric (p : Space (KPCuspLogShape.dimension F * 3)) :
    Matrix (Fin (KPCuspLogShape.dimension F * 3))
      (Fin (KPCuspLogShape.dimension F * 3)) ℝ :=
  Matrix.diagonal (fun j =>
    let ik := finProdFinEquiv.symm j
    if ik.2 = 2 then 1 else
      Real.exp (2 * (coordinates F p ik.1).2))

structure ChartCoefficients (A : LocalBall (KPCuspLogShape.dimension F * 3)) where
  lowerDensity : ℝ
  upperDensity : ℝ
  lowerEllipticity : ℝ
  upperEllipticity : ℝ
  lowerDensity_pos : 0 < lowerDensity
  lowerEllipticity_pos : 0 < lowerEllipticity
  data : KPContLocalEnergy.Coefficients A lowerDensity upperDensity
    lowerEllipticity upperEllipticity
  density_exact : data.density = density F
private lemma coordinates_snd (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (KPCuspLogShape.dimension F)) :
    (coordinates F p i).2 = p (finProdFinEquiv (i, 2)) := rfl

 def diagFun (p : Space (KPCuspLogShape.dimension F * 3)) :
    Fin (KPCuspLogShape.dimension F * 3) → ℝ :=
  fun j => let ik := finProdFinEquiv.symm j
    if ik.2 = 2 then 1 else Real.exp (2 * p (finProdFinEquiv (ik.1, 2)))

 lemma inverseMetric_eq_diagonal (p : Space (KPCuspLogShape.dimension F * 3)) :
    inverseMetric F p = Matrix.diagonal (diagFun F p) := by
  funext i j
  rw [inverseMetric, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; simp only [diagFun, coordinates_snd]
  · rw [if_neg h, if_neg h]

private lemma contDiff_diagFun (j : Fin (KPCuspLogShape.dimension F * 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space (KPCuspLogShape.dimension F * 3) => diagFun F p j) := by
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [diagFun, h, if_true]; fun_prop
  · simp only [diagFun, h, if_false]; fun_prop

 lemma contDiff_inverseMetric_entry (i j : Fin (KPCuspLogShape.dimension F * 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space (KPCuspLogShape.dimension F * 3) => inverseMetric F p i j) := by
  by_cases h : i = j
  · have he : (fun p => inverseMetric F p i j) = (fun p => diagFun F p i) := by
      funext p; rw [inverseMetric_eq_diagonal, ← h, Matrix.diagonal_apply_eq]
    rw [he]; exact contDiff_diagFun F i
  · have he : (fun p => inverseMetric F p i j) = (fun _ => (0 : ℝ)) := by
      funext p; rw [inverseMetric_eq_diagonal, Matrix.diagonal_apply_ne _ h]
    rw [he]; exact contDiff_const

 def entryLo (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℝ :=
  let ik := finProdFinEquiv.symm j
  if ik.2 = 2 then 1
  else Real.exp (2 * (A.center (finProdFinEquiv (ik.1, 2)) - A.radius))

 def entryHi (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℝ :=
  let ik := finProdFinEquiv.symm j
  if ik.2 = 2 then 1
  else Real.exp (2 * (A.center (finProdFinEquiv (ik.1, 2)) + A.radius))

 lemma entryLo_pos (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : 0 < entryLo F A j := by
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [entryLo, h, if_true]; norm_num
  · simp only [entryLo, h, if_false]; exact Real.exp_pos _

 lemma entry_bounds (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3))
    {p : Space (KPCuspLogShape.dimension F * 3)} (hp : p ∈ KPContLocalCubeEmbedding.closedCarrier A) :
    entryLo F A j ≤ diagFun F p j ∧ diagFun F p j ≤ entryHi F A j := by
  have hd : dist p A.center ≤ A.radius := Metric.mem_closedBall.mp hp
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [entryLo, entryHi, diagFun, h, if_true]; exact ⟨le_rfl, le_rfl⟩
  · simp only [entryLo, entryHi, diagFun, h, if_false]
    have hk : |p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) -
        A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2))| ≤ A.radius := by
      have h1 := PiLp.norm_apply_le (p - A.center)
        (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2))
      rw [PiLp.sub_apply] at h1
      rw [dist_eq_norm] at hd
      simpa using h1.trans hd
    have hlo : A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) - A.radius ≤
        p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) := by
      have := (abs_le.mp hk).1; linarith
    have hhi : p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) ≤
        A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) + A.radius := by
      have := (abs_le.mp hk).2; linarith
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩


 lemma diag_quad (d : Fin (KPCuspLogShape.dimension F * 3) → ℝ)
    (v : Space (KPCuspLogShape.dimension F * 3)) :
    ∑ i, ∑ j, Matrix.diagonal d i j * v i * v j = ∑ i, d i * (v i) ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj; rw [Matrix.diagonal_apply_ne' _ hj]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

def chartCoefficients (A : LocalBall (KPCuspLogShape.dimension F * 3)) :
    ChartCoefficients F A := by
  classical
  let hbnd := density_bounds F A
  let a : ℝ := hbnd.choose
  let b : ℝ := hbnd.choose_spec.choose
  have ha : 0 < a := hbnd.choose_spec.choose_spec.1
  have hb : ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A, a ≤ density F p ∧ density F p ≤ b :=
    hbnd.choose_spec.choose_spec.2
  haveI : Nonempty (Fin (KPCuspLogShape.dimension F * 3)) :=
    ⟨⟨0, A.dimension_pos⟩⟩
  let κ : ℝ := Finset.univ.inf' Finset.univ_nonempty (entryLo F A)
  let Λ : ℝ := Finset.univ.sup' Finset.univ_nonempty (entryHi F A)
  have hκpos : 0 < κ :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => entryLo_pos F A j)
  refine
    { lowerDensity := a
      upperDensity := b
      lowerEllipticity := κ
      upperEllipticity := Λ
      lowerDensity_pos := ha
      lowerEllipticity_pos := hκpos
      data :=
        { density := density F
          matrix := inverseMetric F
          density_smooth := (density_smooth F).contDiffOn
          matrix_smooth := fun i j => (contDiff_inverseMetric_entry F i j).contDiffOn
          density_bounds := fun x hx => hb x (Metric.ball_subset_closedBall hx)
          symmetric := fun x _ i j => by
            rw [inverseMetric_eq_diagonal]
            by_cases hij : i = j
            · rw [hij]
            · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
          ellipticity := fun x hx ξ => by
            calc κ * ‖ξ‖ ^ 2 = κ * ∑ i, (ξ i) ^ 2 := by
                  rw [EuclideanSpace.real_norm_sq_eq]
              _ = ∑ i, κ * (ξ i) ^ 2 := by rw [Finset.mul_sum]
              _ ≤ ∑ i, diagFun F x i * (ξ i) ^ 2 :=
                  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                    ((Finset.inf'_le (entryLo F A) (Finset.mem_univ i)).trans
                      (entry_bounds F A i (Metric.ball_subset_closedBall hx)).1) (sq_nonneg _)
              _ = ∑ i, ∑ j, inverseMetric F x i j * ξ i * ξ j := by
                  rw [inverseMetric_eq_diagonal, diag_quad]
          upper_bound := fun x hx ξ => by
            calc ∑ i, ∑ j, inverseMetric F x i j * ξ i * ξ j
                = ∑ i, diagFun F x i * (ξ i) ^ 2 := by
                  rw [inverseMetric_eq_diagonal, diag_quad]
              _ ≤ ∑ i, Λ * (ξ i) ^ 2 :=
                  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                    ((entry_bounds F A i (Metric.ball_subset_closedBall hx)).2.trans
                      (Finset.le_sup' (entryHi F A) (Finset.mem_univ i))) (sq_nonneg _)
              _ = Λ * ∑ i, (ξ i) ^ 2 := by rw [Finset.mul_sum]
              _ = Λ * ‖ξ‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq] }
      density_exact := rfl }

end DedekindZetaZeroFree.KPContActualFriedrichsWeakChart

end
