module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSpan

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
set_option autoImplicit false
open scoped MatrixOrder Matrix

variable {n : ℕ}

/-- A coordinate projection of the derivative of a field is the derivative of the projected
field. -/
theorem coord_fderiv_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EvolutionVec n →L[ℝ] F) {W : EvolutionVec n → EvolutionVec n} {g : EvolutionVec n → F}
    {x : EvolutionVec n} (hW : DifferentiableAt ℝ W x)
    (h : ∀ y, L (W y) = g y) (w : EvolutionVec n) :
    L (fderiv ℝ W x w) = fderiv ℝ g x w := by
  have h1 := L.hasFDerivAt.comp x hW.hasFDerivAt
  have h2 : (L ∘ W) = g := funext h
  rw [h2] at h1
  rw [h1.fderiv]
  rfl

/-- A coordinate projection of the derivative of a field with constant coordinate vanishes. -/
theorem coord_fderiv_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EvolutionVec n →L[ℝ] F) {W : EvolutionVec n → EvolutionVec n} {x : EvolutionVec n}
    (hW : DifferentiableAt ℝ W x) (c : F) (h : ∀ y, L (W y) = c) (w : EvolutionVec n) :
    L (fderiv ℝ W x w) = 0 := by
  rw [coord_fderiv_comp L hW h w]
  simp

/-- A drift with `m ≤ ξ · Db(v) ξ` for unit `ξ`, `m > 0`, has surjective derivative. -/
theorem fderiv_surjective_of_coercive {m : ℝ} {b : PDE.Vec n → PDE.Vec n} (hm : 0 < m)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) (y : PDE.Vec n) :
    Function.Surjective (fderiv ℝ b y) := by
  suffices hinj : Function.Injective (fderiv ℝ b y).toLinearMap from
    LinearMap.injective_iff_surjective.1 hinj
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  change (fderiv ℝ b y) ξ = 0 at hξ
  by_contra hne
  have hpos :=
    lt_of_le_of_ne (PDE.vecNormSq_nonneg ξ) (fun h => hne (PDE.vecNormSq_eq_zero h.symm))
  set c := Real.sqrt (PDE.vecNormSq ξ) with hc
  have hcpos : 0 < c := Real.sqrt_pos.2 hpos
  have hcsq : c ^ 2 = PDE.vecNormSq ξ := Real.sq_sqrt hpos.le
  have hunit : PDE.vecEuclideanNorm (c⁻¹ • ξ) = 1 := by
    have : PDE.vecNormSq (c⁻¹ • ξ) = 1 := by
      have e : PDE.vecNormSq (c⁻¹ • ξ) = (c⁻¹) ^ 2 * PDE.vecNormSq ξ := by
        simp [PDE.vecNormSq, PDE.vecDot, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [e, ← hcsq]
      field_simp
    simp [PDE.vecEuclideanNorm, this]
  have h := hcoerc y (c⁻¹ • ξ) hunit
  have hz : (fderiv ℝ b y) (c⁻¹ • ξ) = 0 := by
    rw [map_smul, hξ, smul_zero]
  rw [hz] at h
  simp [PDE.vecDot] at h
  linarith

section Bracket

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

private theorem differentiableAt_diffusionField
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (i : Fin n)
    (x : EvolutionVec n) : DifferentiableAt ℝ (diffusionField B i) x :=
  ((contDiff_diffusionField hβ i).differentiable (by simp)) x

private theorem differentiableAt_driftField
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (x : EvolutionVec n) :
    DifferentiableAt ℝ (driftField B b) x :=
  ((contDiff_driftField hβ hb).differentiable (by simp)) x

/-- The transported component of the bracket `[X_i, X_0]` is `Db(v) β_i`, where `β_i` is the
`i`-th row of `β` (equal to its `i`-th column by symmetry). -/
theorem transportedCoord_lieBracket
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin n) (x : EvolutionVec n) :
    transportedCoord n
        (VectorField.lieBracket ℝ (diffusionField B i) (driftField B b) x) =
      fderiv ℝ b (diffusedCoord n x) (fun j => sqrtCoeffAt B x i j) := by
  unfold VectorField.lieBracket
  rw [map_sub]
  have h1 : transportedCoord n (fderiv ℝ (driftField B b) x (diffusionField B i x)) =
      fderiv ℝ b (diffusedCoord n x) (fun j => sqrtCoeffAt B x i j) := by
    rw [coord_fderiv_comp (transportedCoord n) (differentiableAt_driftField hβ hb x)
      (g := fun y => b (diffusedCoord n y)) (fun y => by simp [driftField])]
    have hd : HasFDerivAt (fun y => b (diffusedCoord n y))
        ((fderiv ℝ b (diffusedCoord n x)).comp (diffusedCoord n)) x :=
      (hb.differentiable (by simp) _).hasFDerivAt.comp x (diffusedCoord n).hasFDerivAt
    rw [hd.fderiv]
    simp [diffusionField]
  have h2 : transportedCoord n (fderiv ℝ (diffusionField B i) x (driftField B b x)) = 0 :=
    coord_fderiv_const (transportedCoord n) (differentiableAt_diffusionField hβ i x) 0
      (fun y => by simp [diffusionField]) _
  rw [h1, h2, sub_zero]

/-- The time component of the bracket `[X_i, X_0]` vanishes. -/
theorem timeCoord_lieBracket
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin n) (x : EvolutionVec n) :
    timeCoord n (VectorField.lieBracket ℝ (diffusionField B i) (driftField B b) x) = 0 := by
  unfold VectorField.lieBracket
  rw [map_sub]
  have h1 : timeCoord n (fderiv ℝ (driftField B b) x (diffusionField B i x)) = 0 :=
    coord_fderiv_const (timeCoord n) (differentiableAt_driftField hβ hb x) 1
      (fun y => by simp [driftField]) _
  have h2 : timeCoord n (fderiv ℝ (diffusionField B i) x (driftField B b x)) = 0 :=
    coord_fderiv_const (timeCoord n) (differentiableAt_diffusionField hβ i x) 0
      (fun y => by simp [diffusionField]) _
  rw [h1, h2, sub_zero]

/-- **Bracket (Lie-algebra spanning) condition for `Lop`.**  Under the standing hypotheses
(`B` smooth with `lam • 1 ≤ B`, `0 < lam`; `b` smooth with `ξ · Db(v) ξ ≥ m` for unit `ξ`,
`0 < m`), the Lie algebra generated by `X_0, X_1, …, X_d` spans `ℝ^{1+2d}` at every point.
Valid also when `B` depends on `z`. -/
theorem lieAlgebraSpansOn_transportedFields {lam Lam m : ℝ} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) (hm : 0 < m) (hcoerc : HasUnitDirectionDriftCoercivity m b) :
    LieAlgebraSpansOn (Set.univ : Set (EvolutionVec n)) (transportedFields B b) := by
  intro x _
  have hβ := contDiff_sqrtCoeffAt_entry hlam hB hell
  set W := Submodule.span ℝ
    (Set.range (fun w => LieWord.eval (transportedFields B b) w x)) with hW
  have hX : ∀ i, diffusionField B i x ∈ W := fun i =>
    Submodule.subset_span ⟨LieWord.generator i.succ, by simp [LieWord.eval, transportedFields]⟩
  have h0 : driftField B b x ∈ W :=
    Submodule.subset_span ⟨LieWord.generator 0, by simp [LieWord.eval, transportedFields]⟩
  have hBr : ∀ i, VectorField.lieBracket ℝ (diffusionField B i) (driftField B b) x ∈ W :=
    fun i => Submodule.subset_span
      ⟨LieWord.bracket (LieWord.generator i.succ) (LieWord.generator 0),
        by simp [LieWord.eval, transportedFields]⟩
  have hv := packPoint_diffused_mem (posDef_sqrtCoeffAt hlam hell x) hX
  have hz : ∀ w, packPoint 0 0 w ∈ W := by
    intro w
    obtain ⟨ξ, hξ⟩ := fderiv_surjective_of_coercive hm hcoerc (diffusedCoord n x) w
    obtain ⟨a, ha⟩ := exists_row_combination (posDef_sqrtCoeffAt hlam hell x) ξ
    set S := ∑ i, a i • VectorField.lieBracket ℝ (diffusionField B i) (driftField B b) x
      with hS
    have hSW : S ∈ W := W.sum_mem fun i _ => W.smul_mem _ (hBr i)
    have e : packPoint 0 0 w = S - packPoint 0 (diffusedCoord n S) 0 := by
      refine ext_coords ?_ ?_ ?_
      · simp [hS, map_sub, map_sum, map_smul, timeCoord_lieBracket hβ hb, timeCoord_packPoint]
      · simp
      · simp [hS, map_sub, map_sum, map_smul, transportedCoord_lieBracket hβ hb, transportedCoord_packPoint, transportedCoord_packPoint]
        rw [← hξ]
        have hξ' : ξ = ∑ i, a i • (fun j => sqrtCoeffAt B x i j) := by
          funext j
          simp [Finset.sum_apply, ha j]
        rw [hξ', map_sum]
        simp [map_smul]
    rw [e]
    exact W.sub_mem hSW (hv _)
  refine eq_top_of_blocks ?_ hv hz
  have e : packPoint 1 0 0 = driftField B b x -
      packPoint 0 (fun k => - driftCorrection B k x) 0 - packPoint 0 0 (b (diffusedCoord n x)) := by
    refine ext_coords ?_ ?_ ?_ <;> simp [driftField]
  rw [e]
  exact W.sub_mem (W.sub_mem h0 (hv _)) (hz _)

end Bracket

set_option autoImplicit false

variable {n : ℕ}

/-- The unit time direction `∂_σ`. -/
def basisT : EvolutionVec n := packPoint 1 0 0

/-- The unit diffused direction `∂_{v_j}`. -/
def basisV (j : Fin n) : EvolutionVec n := packPoint 0 (Pi.single j 1) 0

/-- The unit transported direction `∂_{z_l}`. -/
def basisZ (l : Fin n) : EvolutionVec n := packPoint 0 0 (Pi.single l 1)

section Algebra

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- `∑_i β_ij β_ik = B_jk`: the square-root factorisation (uses symmetry of `β`). -/
theorem sum_sqrtCoeffAt_mul {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (x : EvolutionVec n) (j k : Fin n) :
    ∑ i, sqrtCoeffAt B x i j * sqrtCoeffAt B x i k =
      B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) j k := by
  set A := B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) with hA
  have hApd : A.PosDef := posDef_of_smul_one_le hlam (hell _ _ _).1
  have hsymm' : ∀ i j, CFC.sqrt A i j = CFC.sqrt A j i := fun i j => by
    have := congrFun (congrFun ((CFC.sqrt_nonneg A).isSelfAdjoint.star_eq) j) i
    simpa [Matrix.conjTranspose_apply] using this
  have := congrFun (congrFun (CFC.sqrt_mul_sqrt_self A hApd.posSemidef.nonneg) j) k
  rw [Matrix.mul_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sqrtCoeffAt, ← hA]
  rw [hsymm' i j]

/-- The transported operator `Lop = ∂_σ + B(σ,v,z) : D_v² + b(v) · ∇_z` in packed
coordinates (`B_ij ∂_{v_i} ∂_{v_j} u`, with the same index convention as
`transportedForwardOperator`). -/
def transportedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  fderiv ℝ u x basisT +
    ∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j *
      fderiv ℝ (fun y => fderiv ℝ u y (basisV j)) x (basisV i) +
    ∑ l, b (diffusedCoord n x) l * fderiv ℝ u x (basisZ l)

/-- The regularised operator `L_ε = Lop + ε Δ_z` in packed coordinates. -/
def regularizedOperator (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (u : EvolutionVec n → ℝ) (x : EvolutionVec n) : ℝ :=
  transportedOperator B b u x +
    ε * ∑ l, fderiv ℝ (fun y => fderiv ℝ u y (basisZ l)) x (basisZ l)

end Algebra

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

