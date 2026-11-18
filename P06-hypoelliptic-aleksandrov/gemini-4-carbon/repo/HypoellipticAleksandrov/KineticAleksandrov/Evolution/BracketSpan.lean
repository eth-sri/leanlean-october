module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketCoord
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSqrt
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
set_option autoImplicit false
open scoped MatrixOrder

variable {n : ℕ}

/-- The matrix `β(x) = B(σ,v,z)^{1/2}` at the point `x = (σ, v, z)` (positive square root
of the coefficient matrix). -/
def sqrtCoeffAt (B : FullKineticCoefficient n) (x : EvolutionVec n) : PDE.Mat n :=
  CFC.sqrt (B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x))

/-- The diffusion field `X_i = ∑_j β_ij ∂_{v_j}`. -/
def diffusionField (B : FullKineticCoefficient n) (i : Fin n) (x : EvolutionVec n) :
    EvolutionVec n :=
  packPoint 0 (fun j => sqrtCoeffAt B x i j) 0

/-- The drift correction `c_k = ∑_{i,j} β_ij ∂_{v_j} β_ik`. -/
def driftCorrection (B : FullKineticCoefficient n) (k : Fin n) (x : EvolutionVec n) : ℝ :=
  ∑ i, ∑ j, sqrtCoeffAt B x i j *
    fderiv ℝ (fun y => sqrtCoeffAt B y i k) x (packPoint 0 (Pi.single j 1) 0)

/-- The drift field `X_0 = ∂_σ + b(v) · ∇_z - ∑_k c_k ∂_{v_k}`. -/
def driftField (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (x : EvolutionVec n) : EvolutionVec n :=
  packPoint 1 (fun k => - driftCorrection B k x) (b (diffusedCoord n x))

/-- The constant regularising field `Y_l = √ε ∂_{z_l}` of `L_ε = Lop + ε Δ_z`. -/
def regularizingField (ε : ℝ) (l : Fin n) (_x : EvolutionVec n) : EvolutionVec n :=
  packPoint 0 0 (Pi.single l (Real.sqrt ε))

/-- The Hörmander generators of `Lop = X_0 + ∑ X_i²`: `X 0` is the drift `X_0` and
`X i.succ = X_i`.  (`k = d`, so this is a `Fin (d + 1)`-indexed family.) -/
def transportedFields (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) :
    Fin (n + 1) → EvolutionVec n → EvolutionVec n :=
  Fin.cons (driftField B b) (diffusionField B)

/-- The Hörmander generators of `L_ε = Lop + ε Δ_z = X_0 + ∑ X_i² + ∑ Y_l²`: `X 0` is the
drift `X_0`, then the `d` fields `X_i`, then the `d` fields `Y_l = √ε ∂_{z_l}`. -/
def regularizedFields (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ) :
    Fin (n + n + 1) → EvolutionVec n → EvolutionVec n :=
  Fin.cons (driftField B b) (Fin.append (diffusionField B) (regularizingField ε))

/-! ## Smoothness -/

theorem contDiff_packPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : WithTop ℕ∞} {f : E → ℝ} {g h : E → PDE.Vec n}
    (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) (hh : ContDiff ℝ m h) :
    ContDiff ℝ m (fun x => packPoint (f x) (g x) (h x)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa using contDiff_pi.1 hg a
    · simpa only [packPoint_transported_apply] using contDiff_pi.1 hh b

/-- The coefficient matrix, read in packed coordinates, is entrywise smooth. -/
theorem contDiff_coeffAt_entry {B : FullKineticCoefficient n}
    (hB : IsSmoothFullKineticCoefficient B) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EvolutionVec n =>
        B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      (timeCoord n x, (diffusedCoord n x, transportedCoord n x))) :=
    (timeCoord n).contDiff.prodMk
      ((diffusedCoord n).contDiff.prodMk (transportedCoord n).contDiff)
  exact (hB i j).comp hlin

/-- The positive square root `β` of the coefficient is entrywise smooth in packed
coordinates, under the standing ellipticity hypotheses. -/
theorem contDiff_sqrtCoeffAt_entry {lam Lam : ℝ} {B : FullKineticCoefficient n}
    (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j) :=
  contDiff_sqrt_entry
    (fun x => B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x))
    (fun i j => contDiff_coeffAt_entry hB i j)
    (fun _ => posDef_of_smul_one_le hlam (hell _ _ _).1) i j

/-- The drift corrections `c_k` are smooth, as soon as `β` is entrywise smooth. -/
theorem contDiff_driftCorrection {B : FullKineticCoefficient n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (k : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => driftCorrection B k x) := by
  unfold driftCorrection
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y => sqrtCoeffAt B y i k)) :=
    (hβ i k).fderiv_right (by simp)
  exact (hβ i j).mul (h1.clm_apply contDiff_const)

theorem contDiff_diffusionField {B : FullKineticCoefficient n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (diffusionField B i) :=
  contDiff_packPoint contDiff_const (contDiff_pi.2 fun j => hβ i j) contDiff_const

theorem contDiff_driftField {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (driftField B b) :=
  contDiff_packPoint contDiff_const
    (contDiff_pi.2 fun k => (contDiff_driftCorrection hβ k).neg)
    (hb.comp (diffusedCoord n).contDiff)

theorem contDiff_regularizingField (ε : ℝ) (l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizingField ε l) :=
  contDiff_const

/-- The generators of `Lop` are smooth. -/
theorem contDiff_transportedFields {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedFields B b i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [transportedFields] using contDiff_driftField hβ hb
  · simpa [transportedFields] using contDiff_diffusionField hβ j

/-- The generators of `L_ε` are smooth. -/
theorem contDiff_regularizedFields {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (ε : ℝ) (i : Fin (n + n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedFields B b ε i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [regularizedFields] using contDiff_driftField hβ hb
  · refine Fin.addCases (fun a => ?_) (fun c => ?_) j
    · simpa [regularizedFields, Fin.append_left] using
        contDiff_diffusionField hβ a
    · simpa only [regularizedFields, Fin.cons_succ, Fin.append_right] using
        contDiff_regularizingField ε c

set_option autoImplicit false

variable {n : ℕ}

/-- A subspace containing the three coordinate blocks of `ℝ^{1+2d}` is everything. -/
theorem eq_top_of_blocks {W : Submodule ℝ (EvolutionVec n)}
    (ht : packPoint 1 0 0 ∈ W) (hv : ∀ u, packPoint 0 u 0 ∈ W)
    (hz : ∀ w, packPoint 0 0 w ∈ W) : W = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have h : y = packPoint (timeCoord n y) 0 0 + packPoint 0 (diffusedCoord n y) 0 +
      packPoint 0 0 (transportedCoord n y) := by
    conv_lhs => rw [← packPoint_coords y]
    exact packPoint_eq_add _ _ _
  have hs : packPoint (timeCoord n y) 0 0 ∈ W := by
    have := W.smul_mem (timeCoord n y) ht
    have e : (timeCoord n y) • packPoint 1 0 (0 : PDE.Vec n) =
        packPoint (timeCoord n y) 0 0 := by
      rw [← packPoint_smul]
      simp
    rwa [e] at this
  rw [h]
  exact W.add_mem (W.add_mem hs (hv _)) (hz _)

/-- The positive square root `β(x)` of the coefficient matrix is positive definite. -/
theorem posDef_sqrtCoeffAt {lam Lam : ℝ} {B : FullKineticCoefficient n}
    (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B) (x : EvolutionVec n) :
    (sqrtCoeffAt B x).PosDef :=
  posDef_sqrt (posDef_of_smul_one_le hlam (hell _ _ _).1)

/-- The rows of an invertible (positive-definite) matrix span `ℝ^d`. -/
theorem exists_row_combination {β : PDE.Mat n} (hβ : β.PosDef) (u : PDE.Vec n) :
    ∃ a : PDE.Vec n, ∀ j, ∑ i, a i * β i j = u j := by
  refine ⟨Matrix.vecMul u β⁻¹, fun j => ?_⟩
  have h : Matrix.vecMul (Matrix.vecMul u β⁻¹) β = u := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul β ((Matrix.isUnit_iff_isUnit_det β).1 hβ.isUnit), Matrix.vecMul_one]
  have := congrFun h j
  simpa [Matrix.vecMul, dotProduct] using this

/-- If all `X_i(x)` lie in `W` and `β(x)` is invertible, the whole velocity block lies in `W`. -/
theorem packPoint_diffused_mem {B : FullKineticCoefficient n} {x : EvolutionVec n}
    (hβ : (sqrtCoeffAt B x).PosDef) {W : Submodule ℝ (EvolutionVec n)}
    (hX : ∀ i, diffusionField B i x ∈ W) (u : PDE.Vec n) : packPoint 0 u 0 ∈ W := by
  obtain ⟨a, ha⟩ := exists_row_combination hβ u
  have e : packPoint 0 u 0 = ∑ i, a i • diffusionField B i x := by
    refine ext_coords ?_ ?_ ?_
    · simp [diffusionField, map_sum]
    · simp only [diffusionField, map_sum, map_smul, diffusedCoord_packPoint]
      ext j
      simp [Finset.sum_apply, ha j]
    · simp [diffusionField, map_sum]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (hX i)

/-- The `ε > 0` regularising fields fill the transported block. -/
theorem packPoint_transported_mem_of_regularizing {ε : ℝ} (hε : 0 < ε) {x : EvolutionVec n}
    {W : Submodule ℝ (EvolutionVec n)} (hY : ∀ l, regularizingField ε l x ∈ W)
    (w : PDE.Vec n) : packPoint 0 0 w ∈ W := by
  have e : packPoint 0 0 w = ∑ l, (w l / Real.sqrt ε) • regularizingField ε l x := by
    refine ext_coords ?_ ?_ ?_
    · simp [regularizingField, map_sum]
    · simp [regularizingField, map_sum]
    · simp only [regularizingField, map_sum, map_smul, transportedCoord_packPoint]
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
      field_simp
  rw [e]
  exact W.sum_mem fun l _ => W.smul_mem _ (hY l)

/-- **Bracket (spanning) condition for `L_ε`, `ε > 0`.**  The Lie algebra generated by
`X_0, X_i, Y_l` spans `ℝ^{1+2d}` at every point; in fact the generators themselves span. -/
theorem lieAlgebraSpansOn_regularizedFields {lam Lam ε : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hε : 0 < ε) :
    LieAlgebraSpansOn (Set.univ : Set (EvolutionVec n)) (regularizedFields B b ε) := by
  intro x _
  set W := Submodule.span ℝ
    (Set.range (fun w => LieWord.eval (regularizedFields B b ε) w x)) with hW
  have hgen : ∀ i, regularizedFields B b ε i x ∈ W := fun i =>
    Submodule.subset_span ⟨LieWord.generator i, rfl⟩
  have hX : ∀ i, diffusionField B i x ∈ W := fun i => by
    have := hgen (Fin.succ (Fin.castAdd n i))
    simpa [regularizedFields, Fin.append_left] using this
  have hY : ∀ l, regularizingField ε l x ∈ W := fun l => by
    have := hgen (Fin.succ (Fin.natAdd n l))
    simpa only [regularizedFields, Fin.cons_succ, Fin.append_right] using this
  have h0 : driftField B b x ∈ W := by
    simpa [regularizedFields] using hgen 0
  have hv := packPoint_diffused_mem (posDef_sqrtCoeffAt hlam hell x) hX
  have hz := packPoint_transported_mem_of_regularizing hε hY
  refine eq_top_of_blocks ?_ hv hz
  have e : packPoint 1 0 0 = driftField B b x -
      packPoint 0 (fun k => - driftCorrection B k x) 0 - packPoint 0 0 (b (diffusedCoord n x)) := by
    refine ext_coords ?_ ?_ ?_ <;> simp [driftField]
  rw [e]
  exact W.sub_mem (W.sub_mem h0 (hv _)) (hz _)

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

