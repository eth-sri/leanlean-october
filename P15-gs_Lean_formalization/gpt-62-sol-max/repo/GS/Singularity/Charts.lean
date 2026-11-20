module

public import GS.Singularity.Anchors
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import GS.NonmanifoldFinal.EuclideanTransport
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Set Matrix
open scoped ComplexOrder
namespace GS.Shared.Singularity
variable {𝕜 : Type*} [RCLike 𝕜] {q n : ℕ}

@[simp] theorem factorPartialChart_base (Q : FullU 𝕜 n) : factorPartialChart Q Q = 0 := by
  change factorCoordinates Q (Factor.matrix Q) = 0
  simpa only [reconstruct_zero] using factorCoordinates_reconstruct Q 0

/-- Two independent upper entries suffice for the real cone obstruction. -/
theorem realSkew_finrank_ge_two (hq : 3 ≤ q) : 2 ≤ Module.finrank ℝ (FullModel ℝ q) := by
  let i : Fin q := ⟨0,by omega⟩
  let j : Fin q := ⟨1,by omega⟩
  let k : Fin q := ⟨2,by omega⟩
  let E := sharedSkewSpace (𝕜 := ℝ) (n := q) (fullPattern ℝ q).size (fullPattern ℝ q).label
  let f : E →ₗ[ℝ] ℝ × ℝ := ((entryLinearMap ℝ ℝ i j).prod (entryLinearMap ℝ ℝ i k)).comp E.subtype
  have hf : Function.Surjective f := by
    rintro ⟨a,b⟩
    let T : M ℝ q := single i j a + single i k b
    have ht : IsSkewHermitian (T - Tᵀ) := by
      change (T-Tᵀ)ᵀ = -(T-Tᵀ)
      simp [neg_sub]
    refine ⟨asModel _ ht, ?_⟩
    change ((T-Tᵀ) i j, (T-Tᵀ) i k) = (a,b)
    simp [T, i, j, k, Fin.ext_iff]
  simpa [E] using LinearMap.finrank_le_finrank_of_surjective hf

/-- Over the reals positivity is an open restriction of the full Cayley chart. -/
def realSliceChart (Q : FullU ℝ q) (o : Fin q) (hQ : AnchorsNonzero (Factor.matrix Q) o) :
    SliceChart Q o (Module.finrank ℝ (FullModel ℝ q)) := by
  let c : FullModel ℝ q ≃L[ℝ] Coordinate (Module.finrank ℝ (FullModel ℝ q)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let S := {A : FullU ℝ q | PositiveAnchors (Factor.matrix Q) o (Factor.matrix A)}
  have hS : IsOpen S := isOpen_onAnchors o fun i j =>
    isOpen_lt continuous_const ((Factor.continuous_matrix.matrix_elem i j).div_const _)
  let e := ((factorPartialChart Q).restrOpen S hS).transHomeomorph
    (c.toHomeomorph.trans (Homeomorph.uniqueProd Unit (Coordinate _)).symm)
  refine SliceChart.ofProduct e () hQ ⟨base_mem_factorSource Q,positiveAnchors_self hQ⟩ ?_ ?_
  · change ((),c (factorPartialChart Q Q)) = _
    simp
  · exact fun _ hx => ⟨fun _ => rfl,fun _ => hx.2⟩


/-- Multiplication by `I` interchanges the self- and skew-adjoint summands. -/
theorem complexSkew_finrank : Module.finrank ℝ (FullModel ℂ q) = q*q := by
  let A := M ℂ q
  let e := (LinearEquiv.smulOfNeZero ℂ A Complex.I Complex.I_ne_zero).restrictScalars ℝ
  let S := skewAdjoint.submodule ℝ A
  let H := selfAdjoint.submodule ℝ A
  have heq : S.comap e.toLinearMap = H := by
    ext x
    exact Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint
  have h : Module.finrank ℝ A = Module.finrank ℝ (H × S) :=
    (StarModule.decomposeProdAdjoint ℝ A).finrank_eq
  rw [finrank_real_of_complex, Module.finrank_matrix, Module.finrank_prod, ← heq,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  have he : sharedSkewSpace (𝕜 := ℂ) (n := q) (fullPattern ℂ q).size (fullPattern ℂ q).label =
      skewAdjoint.submodule ℝ A := by
    ext T
    exact ⟨fun ht => ht.2.1, fun ht => ⟨full_supported T,ht,full_tied T⟩⟩
  change Module.finrank ℝ (sharedSkewSpace (𝕜 := ℂ) (n := q) _ _) = _
  rw [he]
  change Module.finrank ℝ S = _
  omega

abbrev Phases (o : Fin q) := Anchor o → ℝ

def imagAnchors (A : M ℂ q) (o : Fin q) : M ℂ q →L[ℝ] Phases o :=
  ({ toFun B k := (B (anchorCell k).1 (anchorCell k).2 / A (anchorCell k).1 (anchorCell k).2).im
     map_add' B C := by funext k; simp [add_div]
     map_smul' t B := by ext <;> simp [mul_div_assoc]
   } : M ℂ q →ₗ[ℝ] Phases o).toContinuousLinearMap

def phaseGen (a : Fin q → ℝ) : M ℂ q := diagonal fun i => (a i : ℂ) * Complex.I

theorem phaseGen_skew (a : Fin q → ℝ) : IsSkewHermitian (phaseGen a) := by
  change (phaseGen a)ᴴ = -phaseGen a
  simp [phaseGen]

variable (Q : FullU ℂ q) (o : Fin q)
local notation "A" => Factor.matrix Q
def phaseDerivative := (imagAnchors A o).comp (fderiv ℝ (matrixReconstruct Q) 0)

theorem phaseDerivative_surjective (hQ : AnchorsNonzero A o) :
    Function.Surjective (phaseDerivative Q o) := by
  classical
  intro y
  let a (i : Fin q) := y (.inl i)
  let b (j : Fin q) := if h : j ≠ o then y (.inr ⟨j,h⟩) - a o else 0
  let X := Aᴴ * phaseGen a * A + phaseGen b
  have hX : IsSkewHermitian X := skewHermitian_add
    (by simpa only [conjTranspose_conjTranspose] using (phaseGen_skew a).conjugate Aᴴ)
    (phaseGen_skew b)
  let x := asModel ((-1/2 : ℝ) • X) (skewHermitian_real_smul _ hX)
  have hx : fderiv ℝ (matrixReconstruct Q) 0 x = phaseGen a * A + A * phaseGen b := by
    rw [matrixReconstruct_fderiv_zero]
    change (-2 : ℝ) • (A * ((-1/2 : ℝ) • X)) = _
    rw [Matrix.mul_smul, smul_smul]
    norm_num
    simp only [X, Matrix.mul_add, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]
  have hj (i j : Fin q) (h : A i j ≠ 0) :
      (((phaseGen a * A + A * phaseGen b) i j) / A i j).im = a i + b j := by
    simp [phaseGen, add_div, mul_comm (A i j), h, Complex.mul_im]
  refine ⟨x,?_⟩
  change imagAnchors A o (fderiv ℝ (matrixReconstruct Q) 0 x) = y
  rw [hx]
  funext k
  change (((phaseGen a * A + A * phaseGen b) _ _) / A _ _).im = y k
  grind [anchorCell]

def anchorsRePositive (B : FullU ℂ q) : Prop := OnAnchors o (fun i j => 0 < (Factor.matrix B i j / A i j).re)

theorem anchorsRePositive_open : IsOpen {B | anchorsRePositive Q o B} :=
  isOpen_onAnchors o fun i j => isOpen_lt continuous_const
    (Complex.continuous_re.comp ((Factor.continuous_matrix.matrix_elem i j).div_const _))

theorem positive_iff_levels (B : FullU ℂ q) (hB : anchorsRePositive Q o B) :
    PositiveAnchors A o (Factor.matrix B) ↔ imagAnchors A o (Factor.matrix B) = 0 := by
  unfold PositiveAnchors
  rw [funext_iff]
  exact forall_congr' fun k => (RCLike.pos_iff (K := ℂ)).trans (and_iff_right (hB k))

/-- The positive-anchor slice is the regular zero set of its phase coordinates
inside the shared Cayley chart. -/
def complexSliceChart (hQ : AnchorsNonzero A o) : SliceChart Q o ((q-1)^2) := by
  classical
  let f := (imagAnchors A o) ∘ matrixReconstruct Q
  let D := phaseDerivative Q o
  have hs : HasStrictFDerivAt f D 0 :=
    ((imagAnchors A o).contDiff.comp (matrixReconstruct_smooth Q)).contDiffAt.hasStrictFDerivAt'
      ((imagAnchors A o).hasFDerivAt.comp 0
        ((matrixReconstruct_smooth Q).differentiable (by simp) 0).hasFDerivAt) (by simp)
  have hr : D.range = ⊤ := LinearMap.range_eq_top.mpr (phaseDerivative_surjective Q o hQ)
  have hdim : Module.finrank ℝ D.ker = (q-1)^2 := by
    have h := LinearMap.finrank_range_add_finrank_ker D.toLinearMap
    have hf : Module.finrank ℝ (Phases o) = q + (q-1) := by
      simp [Phases, Fintype.card_subtype_compl]
    have hq : q - 1 + 1 = q := by have := o.isLt; omega
    rw [hr, finrank_top, hf, complexSkew_finrank] at h
    nlinarith
  let c : D.ker ≃L[ℝ] Coordinate ((q-1)^2) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ↥D.ker) (F := Coordinate _) (by simp [hdim])
  let g := hs.implicitToOpenPartialHomeomorph f D hr
  let e := (((factorPartialChart Q).trans g).restrOpen {B | anchorsRePositive Q o B}
    (anchorsRePositive_open Q o)).transHomeomorph ((Homeomorph.refl _).prodCongr c.toHomeomorph)
  have hb : Q ∈ e.source := by
    refine ⟨⟨base_mem_factorSource _,?_⟩,fun k => by simp [hQ k]⟩
    simpa using hs.mem_implicitToOpenPartialHomeomorph_source hr
  have hz : e Q = (0,0) := by
    change ((g (factorPartialChart Q Q)).1, c (g (factorPartialChart Q Q)).2) = _
    simp only [factorPartialChart_base, g, hs.implicitToOpenPartialHomeomorph_self hr, map_zero,
      Prod.mk.injEq, and_true]
    funext k
    simp [f, imagAnchors, hQ k]
  have hlevel (B : FullU ℂ q) (hB : B ∈ e.source) :
      PositiveAnchors A o (Factor.matrix B) ↔ (e B).1 = 0 := by
    change _ ↔ (g (factorPartialChart Q B)).1 = _
    rw [hs.implicitToOpenPartialHomeomorph_fst hr]
    change _ ↔ imagAnchors A o (Factor.matrix (reconstruct Q (factorCoordinates Q (Factor.matrix B)))) = _
    rw [reconstruct_factorCoordinates Q B hB.1.1]
    exact positive_iff_levels Q o B hB.2
  exact SliceChart.ofProduct e 0 hQ hb hz hlevel

end GS.Shared.Singularity
