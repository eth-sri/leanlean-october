module

public import GS.Topology.RankOne
public import GS.NonmanifoldFinal.EuclideanTransport
public import Mathlib.Topology.Instances.Matrix
public import GS.Topology.LocalDimension
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import GS.Core
public import GS.OriginalLocalModel

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Matrix GS GS.NonmanifoldFinal GS.NonmanifoldObstruction
open scoped Topology BigOperators
namespace GS.NonmanifoldClosure

abbrev RankProduct (ι κ : Type*) [Fintype κ] (r : ℕ) := (ι → ℝ) × RankOne r κ

variable {ι κ : Type*} [Fintype κ] {r : ℕ}

def pivotSource (j : κ) : Set (RankProduct ι κ r) := {p | p.2.val 0 j ≠ 0}
def pivotTarget (j : κ) : Set ((ι → ℝ) × (κ → ℝ) × (Fin r → ℝ)) :=
  {p | p.2.1 j ≠ 0}

/-- At a nonzero pivot, the first row and the remaining row ratios are free. -/
def pivotCoordinates (j : κ) : OpenPartialHomeomorph (RankProduct ι κ r)
    ((ι → ℝ) × (κ → ℝ) × (Fin r → ℝ)) where
  toFun p := (p.1, p.2.val 0, fun k => p.2.val k.succ j / p.2.val 0 j)
  invFun p := (p.1, ⟨vecMulVec (Fin.cons 1 p.2.2) p.2.1, rank_vecMulVec_le _ _⟩)
  source := pivotSource j
  target := pivotTarget j
  map_source' _ hp := hp
  map_target' p hp := by
    change vecMulVec (Fin.cons 1 p.2.2) p.2.1 0 j ≠ 0
    simpa [pivotTarget, vecMulVec_apply] using hp
  left_inv' p hp := by
    refine Prod.ext rfl (Subtype.ext (Matrix.ext fun i k => ?_))
    refine Fin.cases ?_ (fun a => ?_) i
    · simp [vecMulVec_apply]
    · exact GS.rank_one_pivot _ p.2.property hp _ _
  right_inv' p hp := by
    have hj : p.2.1 j ≠ 0 := hp
    exact Prod.ext rfl (Prod.ext (by ext k; simp [vecMulVec_apply]) (by ext k; simp [vecMulVec_apply, hj]))
  open_source := isOpen_ne_fun
    (Continuous.matrix_elem (by fun_prop : Continuous fun p : RankProduct ι κ r => p.2.val) 0 j) continuous_const
  open_target := isOpen_ne_fun (by fun_prop) continuous_const
  continuousOn_toFun := by
    have hW : Continuous (fun p : RankProduct ι κ r => p.2.val) := by fun_prop
    exact continuous_fst.continuousOn.prodMk (((continuous_apply 0).comp hW).continuousOn.prodMk
      (continuousOn_pi.mpr fun k => (hW.matrix_elem k.succ j).continuousOn.div
        (hW.matrix_elem 0 j).continuousOn fun _ h => h))
  continuousOn_invFun := Continuous.continuousOn (by fun_prop)

def pivotChart [Fintype ι] (j : κ) : OpenPartialHomeomorph (RankProduct ι κ r)
    (Eucl (Fintype.card ι + Fintype.card κ + r)) :=
  (pivotCoordinates j).transHomeomorph <|
    (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by simp [Nat.add_assoc])).toHomeomorph

@[simp] theorem pivotChart_source [Fintype ι] (j : κ) :
    (pivotChart (ι := ι) (r := r) j).source = pivotSource j := by simp [pivotChart, pivotCoordinates]

variable [Fintype ι] [DecidableEq κ]

theorem exists_regular (j : κ) (U : Set (RankProduct ι κ r))
    (hU : IsOpen U) (hz : (0, rankZero) ∈ U) :
    ∃ p ∈ U, p ∈ (pivotChart j).source := by
  let ray (t : ℝ) : RankProduct ι κ r :=
    (0, ⟨vecMulVec (Pi.single 0 t) (Pi.single j 1), rank_vecMulVec_le _ _⟩)
  have hc : Continuous ray := by
    unfold ray
    exact continuous_const.prodMk ((continuous_matrix fun i k => by
      simp only [vecMulVec_apply, Pi.single_apply]
      split_ifs <;> fun_prop).subtype_mk _)
  obtain ⟨t,h0,ht⟩ := (dense_compl_singleton (0 : ℝ)).exists_mem_open (hU.preimage hc)
    ⟨0, by simpa [ray, rankZero] using hz⟩
  refine ⟨ray t, ht, ?_⟩
  rw [pivotChart_source]
  simpa [pivotSource, ray, vecMulVec_apply] using h0

end GS.NonmanifoldClosure


/-!
# Isolated-zero Euclidean retracts and punctured neighbourhoods

A continuous Euclidean retract whose projection vanishes only at the marked
point produces a sphere retract in every punctured open neighbourhood. This
criterion is applicable to Clifford contractions of rank-one matrix cones.
-/
open GS.NonmanifoldClosure
open ContinuousMap
namespace GS.UnitaryTopology

variable {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ}

/-- Adjoin freely varying Euclidean coordinates to an isolated-zero retract. -/
def IsolatedEuclideanRetract.product {ι V X : Type*} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace X] {z : X} {d : ℕ} (h : Module.finrank ℝ V = d)
    (p : ContinuousSectionPair V X)
    (hs : p.sectionMap 0 = z) (hr : ∀ x, p.retractionMap x = 0 ↔ x = z) :
    IsolatedEuclideanRetract ((ι → ℝ) × X) (0,z) (Fintype.card ι + d) := by
  classical
  let e : ((ι → ℝ) × V) ≃L[ℝ] Eucl (Fintype.card ι + d) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, h])
  refine ⟨⟨(ContinuousMap.fst.prodMk (p.sectionMap.comp ContinuousMap.snd)).comp e.toHomeomorph.symm,
    (e.toHomeomorph : C(_,_)).comp (ContinuousMap.fst.prodMk (p.retractionMap.comp ContinuousMap.snd)), ?_⟩, ?_, ?_⟩
  · intro x
    simp [p.retraction_section]
  · simp [hs]
  · rintro ⟨x,y⟩
    change e (x, p.retractionMap y) = 0 ↔ _
    rw [← e.map_zero, e.injective.eq_iff]
    change (x,p.retractionMap y) = (0,0) ↔ (x,y) = (0,z)
    simp only [Prod.mk.injEq, hr]

/-- At the vertex the retract and the neighbouring pivot chart must give the same dimension. -/
theorem rankProduct_not_euclidean {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {r : ℕ}
    (p : IsolatedEuclideanRetract (RankProduct ι κ r) (0,rankZero) m)
    (j : κ) (h : m ≠ Fintype.card ι + Fintype.card κ + r) :
    ¬ EuclideanAt ((0,rankZero) : RankProduct ι κ r) := by
  rintro ⟨n,c,hc⟩
  obtain ⟨x,hx,hj⟩ := exists_regular j c.source c.open_source hc
  apply h
  refine (GS.Topology.local_dimension c _ hc (fun U hU h0 _ => p.punctured_sphere U hU h0)).symm.trans ?_
  exact GS.Topology.local_dimension (c.restrOpen _ (pivotChart j).open_source) x ⟨hx,hj⟩
    (fun U hU hu hs => GS.Topology.openChart_sphereGerm (pivotChart j) x U hU hu (fun _ hy => (hs hy).2))

end GS.UnitaryTopology


open scoped Topology
namespace GS.NonmanifoldClosure

/-- In complex coordinates the traceless Gram projection is the sum of the
squares of the columns. On rank one all summands have the same phase. -/
def gramComplex {κ : Type*} [Fintype κ] (W : Matrix (Fin 2) κ ℝ) : ℂ :=
  ∑ j, (Complex.equivRealProdCLM.symm (W 0 j, W 1 j))^2

@[fun_prop] theorem gramComplex_continuous {κ : Type*} [Fintype κ] :
    Continuous (gramComplex : Matrix (Fin 2) κ ℝ → ℂ) := by
  unfold gramComplex
  fun_prop

theorem gramComplex_zero {κ : Type*} [Fintype κ] (W : RankOne 1 κ) :
    gramComplex W.val = 0 ↔ W = rankZero := by
  constructor
  · intro hz
    obtain ⟨u,hu,z,he⟩ := rank_one_normalized W.val W.property
    let a : ℂ := ⟨u 0,u 1⟩
    have ha : Complex.normSq a = 1 := by
      simpa [a, Complex.normSq_apply, Fin.sum_univ_two, pow_two] using hu
    have ha' : a ≠ 0 := by intro h; simp [h] at ha
    have h (j : κ) : Complex.equivRealProdCLM.symm
        (vecMulVec u z 0 j, vecMulVec u z 1 j) = a * z j := by
      apply Complex.ext <;> simp [a, vecMulVec_apply, Complex.mul_re, Complex.mul_im]
    simp only [← he, gramComplex, h, mul_pow, ← Finset.mul_sum, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, mul_eq_zero, pow_ne_zero _ ha', false_or, Complex.ofReal_eq_zero,
      Finset.sum_sq_eq_zero_iff, Finset.mem_univ, true_implies] at hz
    exact Subtype.ext (by ext; simp [← he, show z = 0 from funext hz, rankZero, vecMulVec_apply])
  · rintro rfl
    simp [rankZero, gramComplex]

/-- Undo quadratic radial growth, continuously even at the origin. -/
def rootRadial (z : ℂ) : ℂ := (Real.sqrt ‖z‖)⁻¹ • z

@[simp] theorem norm_rootRadial (z : ℂ) : ‖rootRadial z‖ = Real.sqrt ‖z‖ := by
  rw [rootRadial, norm_smul, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← div_eq_inv_mul,
    Real.div_sqrt]

@[fun_prop] theorem rootRadial_continuous : Continuous rootRadial := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [ContinuousAt, show rootRadial 0 = 0 by simp [rootRadial], tendsto_zero_iff_norm_tendsto_zero]
    simpa [ContinuousAt, Function.comp_def] using (Real.continuous_sqrt.comp (continuous_norm (E := ℂ))).continuousAt (x := 0)
  · exact ((Real.continuous_sqrt.comp continuous_norm).continuousAt.inv₀
      (Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hz))).smul continuousAt_id

def planeMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(‖z‖ + z.re)/2, z.im/2; z.im/2, (‖z‖ - z.re)/2]

def planeSection (d : ℕ) (z : ℂ) : RankOne 1 (Fin (2+d)) :=
  ⟨fun i => Fin.append (planeMatrix z i) 0, by
    obtain ⟨w,rfl⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
    let u : Fin 2 → ℝ := ![w.re,w.im]
    have h : planeMatrix (w^2) = vecMulVec u u := by
      ext i j
      have hn := Complex.sq_norm w
      rw [Complex.normSq_apply] at hn
      fin_cases i, j <;>
        simp [planeMatrix,u,vecMulVec_apply,pow_two,Complex.mul_re,Complex.mul_im] <;> nlinarith
    rw [h, show (fun i => Fin.append (vecMulVec u u i) (0 : Fin d → ℝ)) =
        vecMulVec u (Fin.append u 0) from Matrix.ext fun i => Fin.addCases
          (fun j => by simp [vecMulVec_apply]) (fun j => by simp [vecMulVec_apply])]
    exact rank_vecMulVec_le _ _⟩

@[fun_prop] theorem planeSection_continuous (d : ℕ) : Continuous (planeSection d) := by
  have h (i : Fin 2) : Continuous (fun z => planeMatrix z i) := continuous_pi fun j => by
    fin_cases i, j <;> simp [planeMatrix] <;> fun_prop
  exact (continuous_matrix fun i j => (continuous_apply j).comp
    ((Fin.continuous_append 2 d).comp ((h i).prodMk continuous_const))).subtype_mk _

theorem gramComplex_planeSection (d : ℕ) (z : ℂ) :
    gramComplex (planeSection d z).val = ‖z‖ • z := by
  apply Complex.ext <;>
    simp [gramComplex, planeSection, planeMatrix, Fin.sum_univ_add, Fin.sum_univ_two,
      pow_two, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem planeSection_zero (d : ℕ) : planeSection d 0 = rankZero :=
  (gramComplex_zero _).mp (by simp [gramComplex_planeSection])

theorem rootRadial_section (z : ℂ) : rootRadial (‖z‖ • z) = z := by
  by_cases hz : z = 0
  · simp [hz, rootRadial]
  simp [rootRadial, ← sq, Real.sqrt_sq (norm_nonneg z), norm_ne_zero_iff.mpr hz]

/-- The Gram plane retract, with no zero except the cone vertex. -/
def planeProductRetract {ι : Type*} [Fintype ι] (d : ℕ) :
    GS.UnitaryTopology.IsolatedEuclideanRetract ((ι → ℝ) × RankOne 1 (Fin (2+d)))
      (0,rankZero) (Fintype.card ι + 2) :=
  GS.UnitaryTopology.IsolatedEuclideanRetract.product Complex.finrank_real_complex
    ⟨⟨planeSection d, planeSection_continuous d⟩, ⟨fun W => rootRadial (gramComplex W.val), by fun_prop⟩,
      fun z => by change rootRadial (gramComplex (planeSection d z).val) = z; rw [gramComplex_planeSection, rootRadial_section]⟩
    (planeSection_zero d) fun W => by
      change rootRadial (gramComplex W.val) = 0 ↔ _
      rw [← norm_eq_zero, norm_rootRadial, Real.sqrt_eq_zero (norm_nonneg _),
        norm_eq_zero, gramComplex_zero]

end GS.NonmanifoldClosure


/-!
# A Clifford contraction of the real three-row rank-one cone

For a width divisible by four, two orthogonal anticommuting complex structures
give a linear contraction onto the column space. Its squared Euclidean norm
equals the Frobenius square on rank-one matrices. The first-row section is an
exact right inverse. In particular the contraction has no additional zeros.
-/
open scoped BigOperators
namespace GS.UnitaryTopology

def quaternionContraction {r : ℕ} (W : Matrix (Fin 3) (Fin r × Fin 4) ℝ) :
    Fin r × Fin 4 → ℝ := fun j =>
  ![W 0 (j.1,0)-W 1 (j.1,1)-W 2 (j.1,2),
    W 0 (j.1,1)+W 1 (j.1,0)+W 2 (j.1,3),
    W 0 (j.1,2)-W 1 (j.1,3)+W 2 (j.1,0),
    W 0 (j.1,3)+W 1 (j.1,2)-W 2 (j.1,1)] j.2

theorem continuous_quaternionContraction (r : ℕ) :
    Continuous (@quaternionContraction r) := by
  apply continuous_pi
  intro j
  rcases j with ⟨j,a⟩
  fin_cases a <;> simp [quaternionContraction] <;> fun_prop

theorem quaternionContraction_outer_square {r : ℕ}
    (u : Fin 3 → ℝ) (z : Fin r × Fin 4 → ℝ) (j : Fin r) :
    (∑ a : Fin 4, quaternionContraction (vecMulVec u z) (j,a)^2) =
      (∑ i, u i^2) * (∑ a : Fin 4, z (j,a)^2) := by
  simp [quaternionContraction, vecMulVec_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

def firstRowSection {κ : Type*} [Fintype κ] (z : κ → ℝ) : RankOne 2 κ :=
  ⟨vecMulVec ![1,0,0] z, rank_vecMulVec_le _ _⟩

theorem quaternionContraction_zero_iff {r : ℕ} (W : RankOne 2 (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankZero := by
  constructor
  · intro he
    obtain ⟨u,hu,z,hz⟩ := rank_one_normalized W.val W.property
    have h (j : Fin r) : ∑ a, z (j,a)^2 = 0 := by
      simpa [hz, he, hu] using (quaternionContraction_outer_square u z j).symm
    have hz0 : z = 0 := funext fun ⟨j,a⟩ => (Finset.sum_sq_eq_zero_iff _ _).mp (h j) a (Finset.mem_univ _)
    exact Subtype.ext (by ext; simp [← hz, hz0, rankZero, vecMulVec_apply])
  · rintro rfl
    funext ⟨j,a⟩
    fin_cases a <;> simp [quaternionContraction,rankZero]

/-- Two anticommuting orthogonal complex structures give the three-row retract. -/
def quaternionProductRetract (e r : ℕ) :
    IsolatedEuclideanRetract ((Fin e → ℝ) × RankOne 2 (Fin r × Fin 4))
      (0,rankZero) (Fintype.card (Fin e) + Fintype.card (Fin r × Fin 4)) := by
  refine IsolatedEuclideanRetract.product (V := Fin r × Fin 4 → ℝ) (by simp)
    ⟨⟨firstRowSection, (continuous_matrix fun i j => continuous_const.mul (continuous_apply j)).subtype_mk _⟩,
      ⟨fun W => quaternionContraction W.val, (continuous_quaternionContraction r).comp continuous_subtype_val⟩, ?_⟩ ?_ quaternionContraction_zero_iff
  · intro z
    funext ⟨j,a⟩
    fin_cases a <;> simp [quaternionContraction, firstRowSection]
  · exact Subtype.ext (Matrix.ext fun i j => mul_zero _)

end GS.UnitaryTopology


/-!
# Unconditional topological obstruction at widths divisible by four

This is a topological, not differentiable, conclusion. A hypothetical vertex
chart would have dimension e+4r from an explicit Clifford sphere retract, but
its overlapping regular chart has dimension e+4r+2. The contradiction uses
the already proved sphere-dimension theorem. No homology profile, manifold
obstruction, or local GS-family model is assumed.

The present mechanism covers positive widths divisible by four. Its transfer
to the unitary GS matrix family requires the separate local-model theorem.
-/
namespace GS.UnitaryTopology

theorem rankThreeProduct_not_euclidean_of_four_dvd (e d : ℕ)
    (hd : 0<d) (hdiv : 4∣d) :
    ¬ EuclideanAt ((0,rankZero) : (Fin e → ℝ) × RankOne 2 (Fin d)) := by
  obtain ⟨r,rfl⟩ := hdiv
  rw [Nat.mul_comm]
  let h := (Homeomorph.refl (Fin e → ℝ)).prodCongr <| rankReindex (r := 2) (finProdFinEquiv : Fin r × Fin 4 ≃ Fin (r*4))
  intro he
  exact rankProduct_not_euclidean (quaternionProductRetract e r) (⟨0,by omega⟩,0) (by simp)
    ((euclideanAt_homeomorph h (0,rankZero)).mpr he)

end GS.UnitaryTopology


set_option autoImplicit false

/-!
# Unconditional topological nonmanifoldness of the cone and the GS family

The geometric retractions and charts are combined with the proved Brouwer
theorem and the proved nullhomotopy theorem for maps into larger spheres.
Neither a sphere-homology profile nor a cone-obstruction premise occurs in
the final statements. The original family and its induced topology are used.
-/

open GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology

/-- The plane retract and the regular pivot chart have different dimensions. -/
theorem cone_not_euclidean (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt ((0,rankZero) : (Fin e → ℝ) × RankOne 1 (Fin d)) := by
  obtain ⟨k,rfl⟩ : ∃ k, d = 2+k := ⟨d-2, by omega⟩
  exact GS.UnitaryTopology.rankProduct_not_euclidean (planeProductRetract (ι := Fin e) k) 0 (by simp; omega)

end GS.NonmanifoldTopology
