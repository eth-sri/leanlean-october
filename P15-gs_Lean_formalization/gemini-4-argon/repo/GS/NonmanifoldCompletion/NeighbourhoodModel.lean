module

public import GS.NonmanifoldCompletion.BlockRealization
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix Filter GS GS.Extensions GS.Continuation
open scoped BigOperators Topology

namespace GS.GlobalGeometry
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_le_one_two_column_minor (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) (j k : κ) : W 0 j * W 1 k = W 0 k * W 1 j := by
  let D : Mat 2 := W.submatrix id ![j, k]
  have hDW : D.rank ≤ W.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono (Submodule.span_mono _)
    rintro x ⟨i, rfl⟩; exact ⟨![j, k] i, rfl⟩
  have hr : D.rank ≤ 1 := hDW.trans hW
  have hd : D.det = 0 := by
    by_contra hn
    have he : D.rank = 2 := by
      simpa using Matrix.rank_of_isUnit D
        ((Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hn))
    omega
  simpa only [D, Matrix.det_fin_two, Matrix.submatrix_apply, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_eq_zero] using hd

theorem rank_le_one_minorN {r : ℕ} (W : Matrix (Fin (r + 1)) κ ℝ) (hW : W.rank ≤ 1)
    (i k : Fin (r + 1)) (j l : κ) : W i j * W k l = W i l * W k j := by
  let R : Matrix (Fin 2) (Fin (r + 1)) ℝ := fun a b => if ![i, k] a = b then 1 else 0
  have he : R * W = W.submatrix ![i, k] id := by ext a b; simp [R, Matrix.mul_apply]
  have hr : (W.submatrix ![i, k] id).rank ≤ 1 := by
    rw [← he]; exact (Matrix.rank_mul_le_right R W).trans hW
  simpa using rank_le_one_two_column_minor (W.submatrix ![i, k] id) hr j l

theorem exists_unitSq_outer_of_rank_le_one {r : ℕ} (W : Matrix (Fin (r + 1)) κ ℝ)
    (hW : W.rank ≤ 1) :
    ∃ u : Fin (r + 1) → ℝ, UnitSq u ∧ ∃ z : κ → ℝ, outer u z = W := by
  classical
  by_cases hzero : W = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, 0, by rw [hzero]; ext i j; simp [outer]⟩
    change (∑ i : Fin (r + 1), (if i = 0 then (1 : ℝ) else 0) ^ 2) = 1
    rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (by simp)]
    norm_num
  have hex : ∃ i j, W i j ≠ 0 := by
    by_contra! hn; exact hzero (Matrix.ext hn)
  obtain ⟨i₀, j₀, hij⟩ := hex
  let v : Fin (r + 1) → ℝ := fun i => W i j₀
  let s : ℝ := ∑ i, v i ^ 2
  have hv : 0 < s := lt_of_lt_of_le (sq_pos_of_ne_zero hij)
    (Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ i₀))
  let norm := Real.sqrt s
  have hr : 0 < norm := Real.sqrt_pos.mpr hv
  have hr0 : norm ≠ 0 := ne_of_gt hr
  have hrs : norm ^ 2 = s := Real.sq_sqrt hv.le
  refine ⟨fun i => v i / norm, ?_, fun j => norm * W i₀ j / W i₀ j₀, ?_⟩
  · change (∑ i, (v i / norm) ^ 2) = 1
    simp_rw [div_pow, ← Finset.sum_div]
    change s / norm ^ 2 = 1
    rw [← hrs, div_self (pow_ne_zero 2 hr0)]
  · ext i j
    have hm := rank_le_one_minorN W hW i i₀ j j₀
    change (W i j₀ / norm) * (norm * W i₀ j / W i₀ j₀) = W i j
    field_simp [hr0, hij]; nlinarith [hm]

theorem exists_unit_outer_of_rank_le_one (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) : ∃ u : CircleVector, OnCircle u ∧ ∃ z : κ → ℝ, outer u z = W := by
  obtain ⟨u, hu, z, hz⟩ := exists_unitSq_outer_of_rank_le_one W hW
  exact ⟨u, by simpa [OnCircle, UnitSq, Fin.sum_univ_two] using hu, z, hz⟩

theorem outer_skew_factor {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (u : CircleVector) (hu : OnCircle u) (z : Fin q × Fin q → ℝ)
    (he : outer u z = W) (hrows : ∀ r, IsSkew (fun i j => W r (i, j))) :
    IsSkew (fun i j => z (i, j)) := by
  have hrecover (i j : Fin q) : z (i, j) = u 0 * W 0 (i, j) + u 1 * W 1 (i, j) := by
    rw [← he]; dsimp [outer]; nlinarith [congrArg (fun x : ℝ => x * z (i, j)) hu]
  change (fun i j => z (j, i)) = -(fun i j => z (i, j))
  ext i j
  have h₀ : W 0 (j, i) = -W 0 (i, j) := congrFun (congrFun (hrows 0) i) j
  have h₁ : W 1 (j, i) = -W 1 (i, j) := congrFun (congrFun (hrows 1) i) j
  simp only [Pi.neg_apply]; rw [hrecover j i, hrecover i j, h₀, h₁]; ring

abbrev OriginalImageCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ

def originalGImageSet (q : ℕ) (η : ℝ) : Set (OriginalImageCoordinates q) :=
  {p | (∀ i, |p.1 i| ≤ η) ∧ (∀ j, |p.2.1 j| ≤ η) ∧
    (∀ j : Fin q, j.val = 0 → p.2.1 j = 0) ∧ IsSkew p.2.2.1 ∧
    frobSq p.2.2.1 ≤ η ^ 2 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i, j))) ∧
    p.2.2.2.rank ≤ 1 ∧ frobSq p.2.2.2 ≤ η ^ 2}

theorem originalG_image_eq (q : ℕ) (η : ℝ) :
    originalG '' originalK q η = originalGImageSet q η := by
  ext p
  constructor
  · rintro ⟨⟨ell, r, c, z, u⟩, ⟨hell, hr, hr0, hc, hz, hcn, hzn, hu⟩, rfl⟩
    refine ⟨hell, hr, hr0, hc, hcn, ?_, rank_outer_le_one _ _, ?_⟩
    · intro k; change IsSkew ((u k) • z); change zᵀ = -z at hz
      simp only [IsSkew, Matrix.transpose_smul, hz, smul_neg]
    · change frobSq (outer u (fun ij : Fin q × Fin q => z ij.1 ij.2)) ≤ η ^ 2
      rw [frobSq_outer hu]
      simpa only [frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hzn
  · rcases p with ⟨ell, r, c, W⟩
    rintro ⟨hell, hr, hr0, hc, hcn, hrows, hRank, hWn⟩
    obtain ⟨u, hu, z, he⟩ := exists_unit_outer_of_rank_le_one W hRank
    let Z : Mat q := fun i j => z (i, j)
    have hz : IsSkew Z := outer_skew_factor W u hu z he hrows
    have hn : frobSq Z ≤ η ^ 2 := by
      rw [← he, frobSq_outer hu] at hWn
      simpa only [Z, frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hWn
    refine ⟨(ell, r, c, Z, u), ⟨hell, hr, hr0, hc, hz, hcn, hn, hu⟩, ?_⟩
    change (ell, r, c, outer u (fun ij => Z ij.1 ij.2)) = (ell, r, c, W)
    simpa only [Z] using congrArg (fun A => (ell, r, c, A)) he

end GS.GlobalGeometry

open GS.GlobalGeometry
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_le_one_of_two_column_minors (W : Matrix (Fin 2) κ ℝ)
    (h : ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j) : W.rank ≤ 1 := by
  by_cases hz : ∀ j, W 0 j = 0
  · rw [show W = outer ![0, 1] (W 1) by ext i j; fin_cases i <;> simp [outer, hz]]
    exact rank_outer_le_one _ _
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    let a : ℝ := W 1 j / W 0 j
    have hrow (k : κ) : W 1 k = a * W 0 k := by
      have hm := h j k; dsimp [a]; field_simp [hj]; nlinarith [hm]
    rw [show W = outer ![1, a] (W 0) by ext i k; fin_cases i <;> simp [outer, hrow]]
    exact rank_outer_le_one _ _

theorem rank_le_one_iff_minors (W : Matrix (Fin 2) κ ℝ) :
    W.rank ≤ 1 ↔ ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j :=
  ⟨fun h => rank_le_one_two_column_minor W h, rank_le_one_of_two_column_minors W⟩

theorem frobSq_pos_of_ne_zero {ι : Type*} [Fintype ι]
    {W : Matrix ι κ ℝ} (hW : W ≠ 0) : 0 < frobSq W :=
  lt_of_le_of_ne (frobSq_nonneg W) (Ne.symm fun h => hW ((frobSq_eq_zero_iff W).mp h))

def rowGram (W : Matrix (Fin 2) κ ℝ) : Mat 2 :=
  fun i j => ∑ k, W i k * W j k

theorem rowGram_outer (u : CircleVector) (z : κ → ℝ) (i j : Fin 2) :
    rowGram (outer u z) i j = (u i * u j) * ∑ k, z k ^ 2 := by
  simp only [rowGram, outer, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

def circleCoordinate (W : Matrix (Fin 2) κ ℝ) : CircleVector :=
  ![rowGram W 0 0 - rowGram W 1 1, 2 * rowGram W 0 1]

theorem continuous_circleCoordinate :
    Continuous (circleCoordinate : Matrix (Fin 2) κ ℝ → CircleVector) := by
  apply continuous_pi; intro i; fin_cases i <;> simp [circleCoordinate, rowGram] <;> fun_prop

def padTwo (d : ℕ) (A : Mat 2) : Matrix (Fin 2) (Fin (d + 2)) ℝ :=
  fun i => Fin.cases (A i 0) (Fin.cases (A i 1) (fun _ : Fin d => 0))

theorem padTwo_frobSq (d : ℕ) (A : Mat 2) :
    frobSq (padTwo d A) = frobSq A := by
  simp [frobSq, frobInner, padTwo, Fin.sum_univ_succ, Fin.sum_univ_two]

theorem padTwo_rowGram (d : ℕ) (A : Mat 2) :
    rowGram (padTwo d A) = A * Aᵀ := by
  ext i j; simp [rowGram, padTwo, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_two, Matrix.transpose_apply]

theorem padTwo_rank_le_one (d : ℕ) {A : Mat 2} (hA : A.rank ≤ 1) :
    (padTwo d A).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => by simp [padTwo]) j) j
  · refine Fin.cases (by simp [padTwo]) (fun k => Fin.cases ?_ (fun _ => by simp [padTwo]) k) k
    exact rank_le_one_two_column_minor A hA 0 1
  · refine Fin.cases ?_ (fun k => Fin.cases (by simp [padTwo]) (fun _ => by simp [padTwo]) k) k
    exact rank_le_one_two_column_minor A hA 1 0

def frobeniusRadius (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (frobSq W)

theorem continuous_frobeniusRadius : Continuous (frobeniusRadius : Matrix (Fin 2) κ ℝ → ℝ) :=
  Real.continuous_sqrt.comp continuous_frobSq

theorem frobeniusRadius_nonneg (W : Matrix (Fin 2) κ ℝ) : 0 ≤ frobeniusRadius W := Real.sqrt_nonneg _

theorem frobeniusRadius_sq (W : Matrix (Fin 2) κ ℝ) : frobeniusRadius W ^ 2 = frobSq W :=
  Real.sq_sqrt (frobSq_nonneg W)

theorem frobeniusRadius_ne_zero {W : Matrix (Fin 2) κ ℝ} (hW : W ≠ 0) :
    frobeniusRadius W ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hW))

end GS.Nonmanifold

namespace GS.NonmanifoldObstruction
open GS.Nonmanifold

abbrev RankCone (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coneZero : RankCone κ := ⟨0, by simp⟩

def planeSq (v : CircleVector) : ℝ := v 0 ^ 2 + v 1 ^ 2

def planeRadius (v : CircleVector) : ℝ := Real.sqrt (planeSq v)

theorem planeSq_nonneg (v : CircleVector) : 0 ≤ planeSq v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeSq_eq_zero_iff (v : CircleVector) : planeSq v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, planeSq]⟩
  have h0 : v 0 = 0 := by dsimp [planeSq] at h; nlinarith [sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by dsimp [planeSq] at h; nlinarith [sq_nonneg (v 0)]
  ext i; fin_cases i <;> simp [h0, h1]

theorem planeRadius_sq (v : CircleVector) : planeRadius v ^ 2 = planeSq v :=
  Real.sq_sqrt (planeSq_nonneg v)

theorem planeRadius_eq_zero_iff (v : CircleVector) : planeRadius v = 0 ↔ v = 0 :=
  ⟨fun h => (planeSq_eq_zero_iff v).mp (by rw [← planeRadius_sq, h]; norm_num),
   fun h => by simp [h, planeRadius, planeSq]⟩

theorem continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius planeSq; fun_prop

theorem circleCoordinate_sq (W : Matrix (Fin 2) κ ℝ) (hW : W.rank ≤ 1) :
    planeSq (circleCoordinate W) = frobSq W ^ 2 := by
  obtain ⟨u, hu, z, hz⟩ := exists_unit_outer_of_rank_le_one W hW
  rw [← hz, frobSq_outer hu z]
  change (rowGram (outer u z) 0 0 - rowGram (outer u z) 1 1) ^ 2 +
    (2 * rowGram (outer u z) 0 1) ^ 2 = (∑ j, z j ^ 2) ^ 2
  simp only [rowGram_outer]
  calc _ = (u 0 ^ 2 + u 1 ^ 2) ^ 2 * (∑ j, z j ^ 2) ^ 2 := by ring
    _ = _ := by rw [show u 0 ^ 2 + u 1 ^ 2 = 1 from hu]; ring

def coneToPlane (W : RankCone κ) : CircleVector :=
  fun i => circleCoordinate W.val i / frobeniusRadius W.val

@[simp] theorem coneToPlane_zero : coneToPlane (coneZero : RankCone κ) = 0 := by
  ext i; simp [coneToPlane, coneZero, circleCoordinate, rowGram, frobeniusRadius, frobSq, frobInner]

theorem coneToPlane_sq (W : RankCone κ) : planeSq (coneToPlane W) = frobSq W.val := by
  by_cases hz : W.val = 0
  · rw [show W = coneZero from Subtype.ext hz, coneToPlane_zero]
    simp [planeSq, coneZero, frobSq, frobInner]
  · have hr := frobeniusRadius_ne_zero hz
    have hg := circleCoordinate_sq W.val W.property
    have hn := frobeniusRadius_sq W.val
    dsimp [planeSq, coneToPlane] at hg ⊢
    field_simp [hr]
    nlinarith [congrArg (frobSq W.val * ·) hn]

theorem abs_coneToPlane_le (W : RankCone κ) (i : Fin 2) :
    |coneToPlane W i| ≤ frobeniusRadius W.val := by
  have hn := coneToPlane_sq W
  have hr := frobeniusRadius_sq W.val
  have hp := frobeniusRadius_nonneg W.val
  have hs : (coneToPlane W i) ^ 2 ≤ frobSq W.val := by
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, id_eq] <;>
      dsimp [planeSq] at hn <;> nlinarith [sq_nonneg (coneToPlane W 0), sq_nonneg (coneToPlane W 1)]
  nlinarith [sq_abs (coneToPlane W i), abs_nonneg (coneToPlane W i)]

theorem continuous_coneToPlane : Continuous (coneToPlane : RankCone κ → CircleVector) := by
  refine continuous_iff_continuousAt.mpr fun W => continuousAt_pi.mpr fun i => ?_
  by_cases hz : W.val = 0
  · obtain rfl : W = coneZero := Subtype.ext hz
    have hr : Tendsto (fun Z : RankCone κ => frobeniusRadius Z.val) (𝓝 coneZero) (𝓝 0) := by
      have hc : Continuous (fun Z : RankCone κ => frobeniusRadius Z.val) :=
        continuous_frobeniusRadius.comp continuous_subtype_val
      have he : frobeniusRadius (coneZero : RankCone κ).val = 0 := by
        simp [coneZero, frobeniusRadius, frobSq, frobInner]
      simpa only [ContinuousAt, he] using hc.continuousAt (x := coneZero)
    change Tendsto (fun Z : RankCone κ => coneToPlane Z i) (𝓝 coneZero) (𝓝 (coneToPlane coneZero i))
    rw [coneToPlane_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hr.neg) hr
      (fun Z => (abs_le.mp (abs_coneToPlane_le Z i)).1)
      (fun Z => (abs_le.mp (abs_coneToPlane_le Z i)).2)
  · exact ((continuous_apply i).comp
      (continuous_circleCoordinate.comp continuous_subtype_val)).continuousAt.div
      (continuous_frobeniusRadius.comp continuous_subtype_val).continuousAt
      (frobeniusRadius_ne_zero hz)

def planeMatrix (v : CircleVector) : Mat 2 :=
  !![(planeRadius v + v 0) / 2, v 1 / 2;
     v 1 / 2, (planeRadius v - v 0) / 2]

theorem planeMatrix_rank (v : CircleVector) : (planeMatrix v).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  have h := planeRadius_sq v; dsimp [planeSq] at h
  intro j k; fin_cases j <;> fin_cases k <;> simp [planeMatrix] <;> nlinarith [h]

def planeToCone (d : ℕ) (v : CircleVector) : RankCone (Fin (d + 2)) :=
  ⟨padTwo d (planeMatrix v), padTwo_rank_le_one d (planeMatrix_rank v)⟩

theorem continuous_planeToCone (d : ℕ) : Continuous (planeToCone d) := by
  apply Continuous.subtype_mk; apply continuous_pi; intro i; apply continuous_pi; intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => continuous_const) j) j
  · fin_cases i
    · exact (continuous_planeRadius.add (continuous_apply 0)).div_const 2
    · exact (continuous_apply 1).div_const 2
  · fin_cases i
    · exact (continuous_apply 1).div_const 2
    · exact (continuous_planeRadius.sub (continuous_apply 0)).div_const 2

@[simp] theorem planeToCone_zero (d : ℕ) : planeToCone d 0 = coneZero := by
  ext i j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j <;>
    fin_cases i <;> simp [planeToCone, planeMatrix, planeRadius, planeSq, padTwo, coneZero] <;> rfl

theorem coneToPlane_planeToCone (d : ℕ) (v : CircleVector) :
    coneToPlane (planeToCone d v) = v := by
  by_cases hv : v = 0
  · subst v; simp
  · have hr : planeRadius v ≠ 0 := fun h => hv ((planeRadius_eq_zero_iff v).mp h)
    have h_symm : (planeMatrix v)ᵀ = planeMatrix v := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [planeMatrix]
    have h_sq : planeMatrix v * planeMatrix v = planeRadius v • planeMatrix v := by
      have h := planeRadius_sq v; dsimp [planeSq] at h
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [planeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
    have h_frob : frobSq (planeToCone d v).val = planeSq v := by
      change frobSq (padTwo d (planeMatrix v)) = planeSq v
      rw [padTwo_frobSq]
      have h := planeRadius_sq v; dsimp [planeSq] at h ⊢
      simp [frobSq, frobInner, planeMatrix, Fin.sum_univ_two]; nlinarith [h]
    have h_rad : frobeniusRadius (planeToCone d v).val = planeRadius v := by
      simp [frobeniusRadius, h_frob, planeRadius]
    have hg : rowGram (planeToCone d v).val = planeRadius v • planeMatrix v := by
      change rowGram (padTwo d (planeMatrix v)) = _
      rw [padTwo_rowGram, h_symm, h_sq]
    have h_coord : circleCoordinate (planeToCone d v).val = planeRadius v • v := by
      ext i; fin_cases i <;> simp [circleCoordinate, hg, planeMatrix] <;> ring
    ext i
    change circleCoordinate (planeToCone d v).val i / frobeniusRadius (planeToCone d v).val = v i
    rw [h_coord, h_rad]
    change planeRadius v * v i / planeRadius v = v i
    field_simp [hr]

theorem coneToPlane_eq_zero_iff (W : RankCone κ) :
    coneToPlane W = 0 ↔ W = coneZero := by
  rw [← planeSq_eq_zero_iff, coneToPlane_sq, frobSq_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

def vectorSq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2
abbrev ConeSpace (ι κ : Type*) [Fintype κ] [DecidableEq κ] := (ι → ℝ) × RankCone κ
def productZero {ι : Type*} : ConeSpace ι κ := (0, coneZero)

end GS.NonmanifoldObstruction

section
namespace GS.Extensions

theorem middleFamily_fibres {q : ℕ} (A B A' B' : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : ∀ i j, middleBlock (A i j) (B i j) u = middleBlock (A' i j) (B' i j) v) :
    (A = B ∧ A' = B' ∧ A = A') ∨
      (u = v ∧ A = A' ∧ B = B') ∨ (u = -v ∧ A = B' ∧ B = A') := by
  have hs (i j) : A i j + B i j = A' i j + B' i j :=
    (middleBlock_eq_sum_and_difference _ _ _ _ u v (h i j)).1
  have hout : outer u (fun ij : Fin q × Fin q => A ij.1 ij.2 - B ij.1 ij.2) =
      outer v (fun ij : Fin q × Fin q => A' ij.1 ij.2 - B' ij.1 ij.2) := by
    ext r ij
    have he := (middleBlock_eq_sum_and_difference _ _ _ _ u v (h ij.1 ij.2)).2
    fin_cases r <;> [simpa [outer, T, mul_comm] using congrFun (congrFun he 0) 0;
      simpa [outer, T, mul_comm] using congrFun (congrFun he 0) 1]
  rcases (outer_fibres hu hv).mp hout with ⟨h₀, h₀'⟩ | ⟨huv, hd⟩ | ⟨huv, hd⟩
  · have hab : A = B := by ext i j; have hh := congrFun h₀ (i, j); dsimp at hh; linarith
    have hab' : A' = B' := by ext i j; have hh := congrFun h₀' (i, j); dsimp at hh; linarith
    refine Or.inl ⟨hab, hab', ?_⟩
    ext i j; have hh := hs i j; rw [hab, hab'] at hh ⊢; linarith
  · refine Or.inr (Or.inl ⟨huv, ?_, ?_⟩) <;> ext i j <;>
      { have hh := congrFun hd (i, j); dsimp at hh; linarith [hs i j] }
  · refine Or.inr (Or.inr ⟨huv, ?_, ?_⟩) <;> ext i j <;>
      { have hh := congrFun hd (i, j); dsimp at hh; linarith [hs i j] }

theorem sandwich_angle_unique (a b a' b' l r l' r' q₀ : ℝ) (u v : CircleVector)
    (h : rotation l * middleBlock a b u * rotation r =
      rotation l' * middleBlock a' b' v * rotation r')
    (hp : 0 < (a + b) * q₀) (hp' : 0 < (a' + b') * q₀)
    (ht : l + r ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (ht' : l' + r' ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) : l + r = l' + r' := by
  let s := a + b; let s' := a' + b'; let θ := l + r; let θ' := l' + r'
  have hprod : 0 < s * s' := by
    rcases mul_pos_iff.mp hp with ⟨hs, _⟩ | ⟨hs, _⟩ <;>
      rcases mul_pos_iff.mp hp' with ⟨hs', _⟩ | ⟨hs', _⟩
    · exact mul_pos hs hs'
    · linarith
    · linarith
    · exact mul_pos_of_neg_of_neg hs hs'
  have hc : s * Real.cos θ = s' * Real.cos θ' := by
    have h_tr (x y α β : ℝ) (w : CircleVector) :
        (rotation α * middleBlock x y w * rotation β) 0 0 +
          (rotation α * middleBlock x y w * rotation β) 1 1 = (x + y) * Real.cos (α + β) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [rotation, middleBlock, T, Matrix.one_apply, Real.cos_add]; ring
    simpa only [h_tr] using congrArg (fun X : Mat 2 => X 0 0 + X 1 1) h
  have hs_eq : s * Real.sin θ = s' * Real.sin θ' := by
    have h_sk (x y α β : ℝ) (w : CircleVector) :
        (rotation α * middleBlock x y w * rotation β) 1 0 -
          (rotation α * middleBlock x y w * rotation β) 0 1 = (x + y) * Real.sin (α + β) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [rotation, middleBlock, T, Matrix.one_apply, Real.sin_add]; ring
    simpa only [h_sk] using congrArg (fun X : Mat 2 => X 1 0 - X 0 1) h
  have hnorm (x t : ℝ) : (x * Real.cos t) ^ 2 + (x * Real.sin t) ^ 2 = x ^ 2 := by
    calc _ = x ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = x ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have he : s ^ 2 = s' ^ 2 := by rw [← hnorm s θ, hc, hs_eq, hnorm s' θ']
  have heq : s = s' := by
    rcases mul_eq_zero.mp (by nlinarith [he] : (s - s') * (s + s') = 0) with h0 | h0
    · linarith
    · exfalso; rw [show s' = -s by linarith] at hprod; nlinarith [sq_nonneg s]
  have hne : s ≠ 0 := fun h0 => by simp [h0] at hprod
  exact Real.injOn_sin ht ht' (mul_left_cancel₀ hne (heq ▸ hs_eq))

def NormalizedOriginal {q : ℕ} (Q₀ : Mat q) (V : Set (Mat q))
    (p : OriginalParameters q) : Prop :=
  let (ell, r, c, z, u) := p
  OnCircle u ∧
    (∀ j : Fin q, j.val = 0 → r j = 0) ∧
    (∀ i j, ell i + r j ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (∀ i j, 0 < (originalPsi Q₀ (c + z) i j + originalPsi Q₀ (c - z) i j) * Q₀ i j) ∧
    c + z ∈ V ∧ c - z ∈ V

theorem original_same_fibres_normalized {q : ℕ} (hq : 0 < q) (Q₀ : Mat q)
    (V : Set (Mat q)) (hinj : Set.InjOn (originalPsi Q₀) V)
    (p p' : OriginalParameters q)
    (hp : NormalizedOriginal Q₀ V p) (hp' : NormalizedOriginal Q₀ V p') :
    originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p' := by
  have symm_inj (c z c' w : Mat q) (hplus : c + z = c' + w) (hminus : c - z = c' - w) : c = c' ∧ z = w := by
    constructor <;> ext i j <;>
      { have hp := congrFun (congrFun hplus i) j; have hm := congrFun (congrFun hminus i) j
        dsimp at hp hm; linarith }
  rcases p with ⟨ell, r, c, z, u⟩
  rcases p' with ⟨ell', r', c', w, v⟩
  rcases hp with ⟨hu, hr₀, ht, hpos, hplus, hminus⟩
  rcases hp' with ⟨hv, hr₀', ht', hpos', hplus', hminus'⟩
  refine ⟨fun hF => ?_, originalF_eq_of_originalG_eq Q₀ ell r ell' r' c z c' w u v hu hv⟩
  have hblocks (i j : Fin q) :
      rotation (ell i) * middleBlock (originalPsi Q₀ (c + z) i j)
        (originalPsi Q₀ (c - z) i j) u * rotation (r j) =
      rotation (ell' i) * middleBlock (originalPsi Q₀ (c' + w) i j)
        (originalPsi Q₀ (c' - w) i j) v * rotation (r' j) := by
    ext s t
    simpa only [originalF, Equiv.symm_apply_apply] using
      congrFun (congrFun hF (finProdFinEquiv (i, s))) (finProdFinEquiv (j, t))
  have hangles (i j : Fin q) : ell i + r j = ell' i + r' j :=
    sandwich_angle_unique _ _ _ _ _ _ _ _ (Q₀ i j) u v
      (hblocks i j) (hpos i j) (hpos' i j) (ht i j) (ht' i j)
  let j₀ : Fin q := ⟨0, hq⟩
  have hell : ell = ell' := funext fun i => by
    have hh := hangles i j₀; rw [hr₀ j₀ rfl, hr₀' j₀ rfl] at hh; simpa only [add_zero] using hh
  have hright : r = r' := funext fun j => add_left_cancel (hell ▸ hangles j₀ j)
  subst ell' r'
  have hm (i j : Fin q) :
      middleBlock (originalPsi Q₀ (c + z) i j) (originalPsi Q₀ (c - z) i j) u =
      middleBlock (originalPsi Q₀ (c' + w) i j) (originalPsi Q₀ (c' - w) i j) v :=
    lift_injective (rotation (ell i)) (rotation (r j))
      (rotation_orthogonal _) (rotation_orthogonal _) (hblocks i j)
  apply (originalG_fibres ell r ell r c z c' w u v hu hv).mpr
  rcases middleFamily_fibres (originalPsi Q₀ (c + z)) (originalPsi Q₀ (c - z))
      (originalPsi Q₀ (c' + w)) (originalPsi Q₀ (c' - w)) u v hu hv hm with
    ⟨hAB, hAB', hAA'⟩ | ⟨huv, hAA', hBB'⟩ | ⟨huv, hAB', hBA'⟩
  · obtain ⟨hc, hz⟩ := symm_inj c z c' w
      (hinj hplus hplus' hAA') (hinj hminus hminus' (hAB.symm.trans (hAA'.trans hAB')))
    have hz₀ : z = 0 := by
      ext i j; have hh := congrFun (congrFun (hinj hplus hminus hAB) i) j; dsimp at hh ⊢; linarith
    exact ⟨rfl, rfl, hc, Or.inl ⟨hz₀, hz.symm.trans hz₀⟩⟩
  · obtain ⟨hc, hz⟩ := symm_inj c z c' w (hinj hplus hplus' hAA') (hinj hminus hminus' hBB')
    exact ⟨rfl, rfl, hc, Or.inr (Or.inl ⟨huv, hz⟩)⟩
  · obtain ⟨hc, hz⟩ := symm_inj c z c' (-w)
      (by simpa only [sub_eq_add_neg] using hinj hplus hminus' hAB')
      (by simpa only [sub_neg_eq_add] using hinj hminus hplus' hBA')
    exact ⟨rfl, rfl, hc, Or.inr (Or.inr ⟨huv, hz⟩)⟩

attribute [local instance] Matrix.normedAddCommGroup

theorem exists_uniform_normalized_original {q : ℕ} (Q₀ : Mat q)
    (hQ : ∀ i j, Q₀ i j ≠ 0) (V : Set (Mat q))
    (hV : IsOpen V) (h₀ : (0 : Mat q) ∈ V) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ originalK q η, NormalizedOriginal Q₀ V p := by
  have h_pos_open : IsOpen {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const (by have := continuous_originalPsi Q₀; fun_prop)
  let W := V ∩ {H : Mat q | ∀ i j, 0 < originalPsi Q₀ H i j * Q₀ i j}
  have hW₀ : (0 : Mat q) ∈ W := ⟨h₀, fun i j => by rw [originalPsi_zero]; exact mul_self_pos.mpr (hQ i j)⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hV.inter h_pos_open) 0 hW₀
  let η := min (δ / 4) (Real.pi / 8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηδ : η ≤ δ / 4 := min_le_left _ _
  have hηπ : η ≤ Real.pi / 8 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  rintro ⟨ell, r, c, z, u⟩ ⟨he, hr, hr₀, _, _, hcn, hzn, hu⟩
  have h_norm {A : Mat q} (hA : frobSq A ≤ η ^ 2) : ‖A‖ ≤ η :=
    (pi_norm_le_iff_of_nonneg hη.le).mpr fun i => (pi_norm_le_iff_of_nonneg hη.le).mpr fun j => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hη.le] using abs_entry_le_of_frobSq_le hA i j
  have hcnorm := h_norm hcn
  have hznorm := h_norm hzn
  have hcplus : c + z ∈ W := hball (by
    change dist (c + z) 0 < δ; rw [dist_zero_right]
    have := norm_add_le c z; linarith)
  have hcminus : c - z ∈ W := hball (by
    change dist (c - z) 0 < δ; rw [dist_zero_right]
    have := norm_sub_le c z; linarith)
  refine ⟨hu, hr₀, fun i j => ?_, fun i j => ?_, hcplus.1, hcminus.1⟩
  · have ha : |ell i + r j| ≤ 2 * η := (abs_add_le _ _).trans (by linarith [he i, hr j])
    have hh := abs_le.mp ha
    constructor <;> linarith [Real.pi_pos]
  · have h₁ := hcplus.2 i j; have h₂ := hcminus.2 i j; nlinarith

end GS.Extensions
end

namespace GS.Continuation
open GS.Extensions

theorem exists_open_matrixExp_injective (n : ℕ) :
    ∃ V : Set (Mat n), IsOpen V ∧ (0 : Mat n) ∈ V ∧ Set.InjOn (@matrixExp n) V := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat n → Mat n)
      (ContinuousLinearEquiv.refl ℝ (Mat n) : Mat n →L[ℝ] Mat n) 0 := by
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.one_def] using
      (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat n))
  obtain ⟨V, hsub, hV, hzero⟩ := mem_nhds_iff.mp hd.eventually_left_inverse
  refine ⟨V, hV, hzero, fun A hA B hB hab => ?_⟩
  have heA : _ = A := hsub hA
  have heB : _ = B := hsub hB
  have he : NormedSpace.exp A = NormedSpace.exp B := by simpa only [matrixExp_eq_exp] using hab
  rw [he] at heA
  exact heA.symm.trans heB

theorem original_same_fibres {q : ℕ} (hq : 0 < q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p' := by
  obtain ⟨V, hV, hzero, hinj⟩ := exists_open_matrixExp_injective q
  have hinj_psi : Set.InjOn (originalPsi Q₀) V := fun A hA B hB he =>
    hinj hA hB (by simpa only [originalPsi, ← Matrix.mul_assoc, hQ₀.1, Matrix.one_mul] using congrArg (Q₀ᵀ * ·) he)
  obtain ⟨η, hη, hn⟩ := exists_uniform_normalized_original Q₀ hentries V hV hzero
  exact ⟨η, hη, fun p hp p' hp' => original_same_fibres_normalized hq Q₀ V hinj_psi p p' (hn p hp) (hn p' hp')⟩

abbrev OriginalFImage {q : ℕ} (Q₀ : Mat q) (η : ℝ) :=
  Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val)

def originalFImageBase {q : ℕ} (Q₀ : Mat q) (η : ℝ) (hη : 0 ≤ η) :
    OriginalFImage Q₀ η :=
  ⟨basePoint Q₀, ⟨⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩, originalF_basePoint Q₀⟩⟩

end GS.Continuation

open GS.GlobalGeometry GS.Nonmanifold
namespace GS.Nonmanifold

theorem skew_of_exp_orthogonal {q : ℕ} (V : Set (Mat q))
    (hinj : Set.InjOn (@matrixExp q) V) (H : Mat q)
    (ht : Hᵀ ∈ V) (hn : -H ∈ V) (hH : Orthogonal (matrixExp H)) : IsSkew H := by
  apply hinj ht hn
  rw [matrixExp_transpose]
  calc (matrixExp H)ᵀ = (matrixExp H)ᵀ * (matrixExp H * matrixExp (-H)) := by
        rw [matrixExp_mul_neg, Matrix.mul_one]
    _ = matrixExp (-H) := by rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]

theorem exists_open_exp_skew_detection (q : ℕ) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0 : Mat q) ∈ V ∧
      ∀ H ∈ V, Orthogonal (matrixExp H) → IsSkew H := by
  obtain ⟨U, hU, h0, hinj⟩ := exists_open_matrixExp_injective q
  refine ⟨(fun H : Mat q => Hᵀ) ⁻¹' U ∩ (fun H : Mat q => -H) ⁻¹' U,
    (hU.preimage (by fun_prop)).inter (hU.preimage (by fun_prop)),
    ⟨by simpa using h0, by simpa using h0⟩,
    fun H hH ho => skew_of_exp_orthogonal U hinj H hH.1 hH.2 ho⟩

abbrev UpperIndex (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}

def packSkew {q : ℕ} (A : Mat q) : UpperIndex q → ℝ :=
  fun ij => A ij.val.1 ij.val.2

def unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) : Mat q := fun i j =>
  if h : i < j then x ⟨(i, j), h⟩
  else if h : j < i then -x ⟨(j, i), h⟩ else 0

theorem unpackSkew_isSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    IsSkew (unpackSkew x) := by
  ext i j
  change unpackSkew x j i = -unpackSkew x i j
  by_cases hij : i < j
  · simp [unpackSkew, hij, not_lt.mpr (le_of_lt hij)]
  · by_cases hji : j < i <;> simp [unpackSkew, hij, hji]

theorem pack_unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    packSkew (unpackSkew x) = x := by
  funext ij; simp [packSkew, unpackSkew, ij.property]

theorem unpack_packSkew {q : ℕ} {A : Mat q} (hA : IsSkew A) :
    unpackSkew (packSkew A) = A := by
  ext i j
  have he : A j i = -A i j := congrFun (congrFun hA i) j
  by_cases hij : i < j
  · simp [unpackSkew, packSkew, hij]
  · by_cases hji : j < i
    · simp [unpackSkew, packSkew, hij, hji, he]
    · obtain rfl : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      have hd : A i i = 0 := by linarith [he]
      simp [unpackSkew, packSkew, hd]

theorem unpackSkew_smul {q : ℕ} (t : ℝ) (x : UpperIndex q → ℝ) :
    unpackSkew (t • x) = t • unpackSkew x := by
  ext i j; by_cases hij : i < j <;> by_cases hji : j < i <;> simp [unpackSkew, hij, hji]

theorem continuous_unpackSkew (q : ℕ) : Continuous (@unpackSkew q) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  by_cases hij : i < j <;> by_cases hji : j < i <;> simp [unpackSkew, hij, hji] <;> fun_prop

def packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ) :
    Matrix (Fin 2) (UpperIndex q) ℝ := fun r ij => W r ij.val

def unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    Matrix (Fin 2) (Fin q × Fin q) ℝ := fun r ij => unpackSkew (Z r) ij.1 ij.2

theorem pack_unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    packRows (unpackRows Z) = Z :=
  funext fun r => pack_unpackSkew (Z r)

theorem unpack_packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : ∀ r, IsSkew (fun i j => W r (i, j))) :
    unpackRows (packRows W) = W := by
  ext r ij; exact congrFun (congrFun (unpack_packSkew (hW r)) ij.1) ij.2

theorem unpackRows_isSkew {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) (r : Fin 2) :
    IsSkew (fun i j => unpackRows Z r (i, j)) := unpackSkew_isSkew (Z r)

theorem packRows_rank_le_one {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : W.rank ≤ 1) : (packRows W).rank ≤ 1 :=
  rank_le_one_of_two_column_minors _ fun j k => rank_le_one_two_column_minor W hW j.val k.val

theorem unpackRows_rank_le_one {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ)
    (hZ : Z.rank ≤ 1) : (unpackRows Z).rank ≤ 1 := by
  obtain ⟨u, _, z, he⟩ := exists_unit_outer_of_rank_le_one Z hZ
  have h_out : unpackRows (outer u z) = outer u (fun ij => unpackSkew z ij.1 ij.2) := by
    ext r ij; exact congrFun (congrFun (unpackSkew_smul (u r) z) ij.1) ij.2
  rw [← he, h_out]
  exact rank_outer_le_one _ _

theorem continuous_unpackRows (q : ℕ) : Continuous (@unpackRows q) := by
  apply continuous_pi; intro r; apply continuous_pi; intro ij
  exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
    ((continuous_unpackSkew q).comp (continuous_apply r)))

theorem three_le_card_upperIndex (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := by
  let f : Fin 3 → UpperIndex q :=
    ![⟨(⟨0, by omega⟩, ⟨1, by omega⟩), Nat.zero_lt_succ 0⟩,
      ⟨(⟨0, by omega⟩, ⟨2, by omega⟩), Nat.zero_lt_succ 1⟩,
      ⟨(⟨1, by omega⟩, ⟨2, by omega⟩), Nat.lt_succ_self 1⟩]
  have hf : Function.Injective f := fun i j h => by
    have he := congrArg (fun x : UpperIndex q => (x.val.1.val, x.val.2.val)) h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Fintype.card_le_of_injective _ hf

abbrev NonzeroIndex (q : ℕ) := {i : Fin q // i.val ≠ 0}

def packRight {q : ℕ} (r : Fin q → ℝ) : NonzeroIndex q → ℝ := fun j => r j.val

def unpackRight {q : ℕ} (x : NonzeroIndex q → ℝ) : Fin q → ℝ :=
  fun j => if h : j.val = 0 then 0 else x ⟨j, h⟩

theorem unpackRight_anchored {q : ℕ} (x : NonzeroIndex q → ℝ) :
    ∀ j : Fin q, j.val = 0 → unpackRight x j = 0 := by
  intro j hj; simp [unpackRight, hj]

theorem pack_unpackRight {q : ℕ} (x : NonzeroIndex q → ℝ) :
    packRight (unpackRight x) = x := by
  funext j; simp [packRight, unpackRight, j.property]

theorem unpack_packRight {q : ℕ} (r : Fin q → ℝ)
    (hr : ∀ j : Fin q, j.val = 0 → r j = 0) :
    unpackRight (packRight r) = r := by
  funext j; by_cases hj : j.val = 0 <;> simp [packRight, unpackRight, hj, hr j]

theorem continuous_unpackRight (q : ℕ) : Continuous (@unpackRight q) := by
  apply continuous_pi; intro j
  by_cases hj : j.val = 0
  · simp only [unpackRight, dif_pos hj]; exact continuous_const
  · simp only [unpackRight, dif_neg hj]; exact continuous_apply _

def originalModelSet (q : ℕ) : Set (OriginalImageCoordinates q) :=
  {p | (∀ j : Fin q, j.val = 0 → p.2.1 j = 0) ∧ IsSkew p.2.2.1 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i, j))) ∧ p.2.2.2.rank ≤ 1}

abbrev OriginalModel (q : ℕ) := ↥(originalModelSet q)

abbrev ModelCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (NonzeroIndex q → ℝ) × (UpperIndex q → ℝ) ×
    {Z : Matrix (Fin 2) (UpperIndex q) ℝ // Z.rank ≤ 1}

def encodeModel {q : ℕ} (p : OriginalModel q) : ModelCoordinates q :=
  (p.val.1, packRight p.val.2.1, packSkew p.val.2.2.1,
    ⟨packRows p.val.2.2.2, packRows_rank_le_one _ p.property.2.2.2⟩)

def decodeModel {q : ℕ} (p : ModelCoordinates q) : OriginalModel q :=
  ⟨(p.1, unpackRight p.2.1, unpackSkew p.2.2.1, unpackRows p.2.2.2.val),
    unpackRight_anchored _, unpackSkew_isSkew _, unpackRows_isSkew _,
    unpackRows_rank_le_one _ p.2.2.2.property⟩

theorem decode_encodeModel {q : ℕ} (p : OriginalModel q) :
    decodeModel (encodeModel p) = p := by
  rcases p with ⟨⟨ell, r, c, W⟩, hr, hc, hW, _⟩
  apply Subtype.ext
  change (ell, unpackRight (packRight r), unpackSkew (packSkew c), unpackRows (packRows W)) = (ell, r, c, W)
  rw [unpack_packRight r hr, unpack_packSkew hc, unpack_packRows W hW]

theorem encode_decodeModel {q : ℕ} (p : ModelCoordinates q) :
    encodeModel (decodeModel p) = p := by
  rcases p with ⟨ell, r, c, W⟩
  exact Prod.ext rfl (Prod.ext (pack_unpackRight r)
    (Prod.ext (pack_unpackSkew c) (Subtype.ext (pack_unpackRows W.val))))

theorem continuous_encodeModel (q : ℕ) : Continuous (@encodeModel q) := by
  unfold encodeModel packRight packSkew packRows; fun_prop

theorem continuous_decodeModel (q : ℕ) : Continuous (@decodeModel q) :=
  (continuous_fst.prodMk (((continuous_unpackRight q).comp (by fun_prop)).prodMk
    (((continuous_unpackSkew q).comp (by fun_prop)).prodMk
      ((continuous_unpackRows q).comp (by fun_prop))))).subtype_mk _

def modelRadiusSq {q : ℕ} (p : OriginalImageCoordinates q) : ℝ :=
  (∑ i, p.1 i ^ 2) + (∑ j, p.2.1 j ^ 2) + frobSq p.2.2.1 + frobSq p.2.2.2

theorem continuous_modelRadiusSq (q : ℕ) : Continuous (@modelRadiusSq q) := by
  unfold modelRadiusSq frobSq frobInner; fun_prop

theorem originalG_image_subset_model (q : ℕ) (η : ℝ) :
    originalG '' originalK q η ⊆ originalModelSet q := by
  rw [originalG_image_eq]
  rintro p ⟨_, _, hr0, hc, _, hW, hRank, _⟩
  exact ⟨hr0, hc, hW, hRank⟩

theorem small_modelRadius_mem_originalG {q : ℕ} {η : ℝ} (hη : 0 < η)
    (p : OriginalImageCoordinates q) (hp : p ∈ originalModelSet q)
    (hn : modelRadiusSq p < η ^ 2) : p ∈ originalG '' originalK q η := by
  rw [originalG_image_eq]
  have hL : 0 ≤ ∑ i, p.1 i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR : 0 ≤ ∑ j, p.2.1 j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := frobSq_nonneg p.2.2.1
  have hW := frobSq_nonneg p.2.2.2
  refine ⟨fun i => ?_, fun j => ?_, hp.1, hp.2.1,
    by dsimp [modelRadiusSq] at hn; linarith, hp.2.2.1, hp.2.2.2,
    by dsimp [modelRadiusSq] at hn; linarith⟩
  · have hs : p.1 i ^ 2 ≤ ∑ k, p.1 k ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hh : p.1 i ^ 2 < η ^ 2 := by dsimp [modelRadiusSq] at hn; linarith
    nlinarith [sq_abs (p.1 i), abs_nonneg (p.1 i)]
  · have hs : p.2.1 j ^ 2 ≤ ∑ k, p.2.1 k ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have hh : p.2.1 j ^ 2 < η ^ 2 := by dsimp [modelRadiusSq] at hn; linarith
    nlinarith [sq_abs (p.2.1 j), abs_nonneg (p.2.1 j)]

def originalGAsModel {q : ℕ} {η : ℝ} (p : ↥(originalK q η)) : OriginalModel q :=
  ⟨originalG p.val, originalG_image_subset_model q η ⟨p.val, p.property, rfl⟩⟩

def independentG {q : ℕ} {η : ℝ} (p : ↥(originalK q η)) : ModelCoordinates q :=
  encodeModel (originalGAsModel p)

theorem continuous_independentG (q : ℕ) (η : ℝ) :
    Continuous (@independentG q η) :=
  (continuous_encodeModel q).comp (((continuous_originalG q).comp continuous_subtype_val).subtype_mk _)

theorem independentG_eq_iff {q : ℕ} {η : ℝ} (p p' : ↥(originalK q η)) :
    independentG p = independentG p' ↔ originalG p.val = originalG p'.val := by
  refine ⟨fun h => ?_, fun h => congrArg encodeModel (Subtype.ext h)⟩
  have he := congrArg decodeModel h
  change decodeModel (encodeModel (originalGAsModel p)) =
    decodeModel (encodeModel (originalGAsModel p')) at he
  rw [decode_encodeModel, decode_encodeModel] at he
  exact congrArg Subtype.val he

def modelCoordinatesZero (q : ℕ) : ModelCoordinates q := (0, 0, 0, ⟨0, by simp⟩)

theorem decode_modelCoordinatesZero (q : ℕ) :
    (decodeModel (modelCoordinatesZero q)).val = (0, 0, 0, 0) :=
  Prod.ext rfl <| Prod.ext (funext fun _ => by simp [decodeModel, modelCoordinatesZero, unpackRight]) <|
    Prod.ext (by ext; simp [decodeModel, modelCoordinatesZero, unpackSkew])
      (by ext; simp [decodeModel, modelCoordinatesZero, unpackRows, unpackSkew])

end GS.Nonmanifold

open GS.Nonmanifold
namespace GS.NonmanifoldCompletion

theorem diagTwo_scalar (a b : ℝ) :
    diagTwo a b = ((a + b) / 2) • (1 : Mat 2) + ((a - b) / 2) • diagTwo 1 (-1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, Matrix.one_apply] <;> ring

theorem exists_common_middle_diagonalizer (u : CircleVector) (hu : OnCircle u) :
    ∃ S : Mat 2, Orthogonal S ∧
      ∀ a b : ℝ, middleBlock a b u = S * diagTwo a b * Sᵀ := by
  have h_half : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 - s ^ 2 = u 0 ∧ 2 * c * s = u 1 := by
    have hu' : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
    by_cases hx : u 0 = -1
    · have hy : u 1 = 0 := by nlinarith [sq_nonneg (u 1)]
      exact ⟨0, 1, by norm_num, by norm_num [hx], by norm_num [hy]⟩
    · have hlow : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 0 + 1)]
      have hp : 0 < 2 * (1 + u 0) := by
        have : -1 < u 0 := lt_of_le_of_ne hlow (Ne.symm hx)
        linarith
      let r := Real.sqrt (2 * (1 + u 0))
      have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
      have hrs : r ^ 2 = 2 * (1 + u 0) := Real.sq_sqrt hp.le
      refine ⟨(1 + u 0) / r, u 1 / r, ?_, ?_, ?_⟩
      · field_simp [hr0]; nlinarith [hu', hrs]
      · field_simp [hr0]; nlinarith [hu', hrs, congrArg (· * u 0) hrs]
      · field_simp [hr0]; nlinarith [congrArg (· * u 1) hrs]
  obtain ⟨c, s, hunit, hdiff, hprod⟩ := h_half
  let v : CircleVector := ![c, s]
  let S := T v
  have hS : Orthogonal S := T_orthogonal hunit
  have hconj : S * diagTwo 1 (-1) * Sᵀ = T u := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [S, v, T, diagTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two] <;>
      nlinarith [hdiff, hprod]
  refine ⟨S, hS, fun a b => ?_⟩
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS.2, hconj]
  rfl

def localRotationAngle (U : Mat 2) : ℝ := Real.arcsin (U 1 0)

theorem continuous_localRotationAngle : Continuous localRotationAngle :=
  Real.continuous_arcsin.comp (by fun_prop)

theorem rotation_localRotationAngle (U : Mat 2) (hU : Orthogonal U)
    (hdet : 0 < U.det) (ha : 0 < U 0 0) :
    rotation (localRotationAngle U) = U := by
  have hd : U.det = 1 := by
    have hs : U.det ^ 2 = 1 := by
      simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using congrArg Matrix.det hU.1
    nlinarith
  have hc := congrFun (congrFun hU.1 0) 0
  have hp := congrFun (congrFun hU.1 0) 1
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_two] at hc hp
  have hdet' : U 0 0 * U 1 1 - U 0 1 * U 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hd
  have hdiag : U 1 1 = U 0 0 := by linear_combination U 0 0 * hdet' + U 1 0 * hp - U 1 1 * hc
  have hoff : U 0 1 = -U 1 0 := by linear_combination -(U 1 0) * hdet' + U 0 0 * hp - U 0 1 * hc
  have hl : -1 ≤ U 1 0 := by nlinarith [sq_nonneg (U 0 0), sq_nonneg (U 1 0 + 1)]
  have hr : U 1 0 ≤ 1 := by nlinarith [sq_nonneg (U 0 0), sq_nonneg (U 1 0 - 1)]
  have hsin : Real.sin (localRotationAngle U) = U 1 0 := Real.sin_arcsin hl hr
  have hsqrt := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - (U 1 0) ^ 2)
  have hcos : Real.cos (localRotationAngle U) = U 0 0 := by
    rw [localRotationAngle, Real.cos_arcsin]
    nlinarith [Real.sqrt_nonneg (1 - (U 1 0) ^ 2)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotation, hsin, hcos, hdiag, hoff]

def rotationChartDomain (η : ℝ) : Set (Mat 2) :=
  {U | 0 < U.det ∧ 0 < U 0 0 ∧ |localRotationAngle U| < η}

theorem isOpen_rotationChartDomain (η : ℝ) : IsOpen (rotationChartDomain η) := by
  have hdet : IsOpen {U : Mat 2 | 0 < U.det} := isOpen_lt continuous_const (by fun_prop)
  have hentry : IsOpen {U : Mat 2 | 0 < U 0 0} := isOpen_lt continuous_const (by fun_prop)
  exact hdet.inter (hentry.inter (isOpen_lt continuous_localRotationAngle.abs continuous_const))

theorem one_mem_rotationChartDomain {η : ℝ} (hη : 0 < η) :
    (1 : Mat 2) ∈ rotationChartDomain η :=
  ⟨by simp, by simp, by simpa [localRotationAngle] using hη⟩

theorem exists_open_frob_small_skew_log {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (η : ℝ) (hη : 0 < η) :
    ∃ U : Set (Mat q), IsOpen U ∧ Q₀ ∈ U ∧
      ∀ A ∈ U, Orthogonal A →
        ∃ H : Mat q, IsSkew H ∧ frobSq H < η ^ 2 ∧ originalPsi Q₀ H = A := by
  letI : SeminormedRing (Mat q) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat q) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat q → Mat q)
      (ContinuousLinearEquiv.refl ℝ (Mat q) : Mat q →L[ℝ] Mat q) 0 := by
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearEquiv.coe_refl] using
      (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat q))
  obtain ⟨g, hleft, hright, hgc⟩ :
      ∃ g : Mat q → Mat q,
        (∀ᶠ H in 𝓝 (0 : Mat q), g (matrixExp H) = H) ∧
        (∀ᶠ A in 𝓝 (1 : Mat q), matrixExp (g A) = A) ∧ ContinuousAt g 1 :=
    ⟨_,
      by simpa only [matrixExp_eq_exp] using hd.eventually_left_inverse,
      by simpa [matrixExp_eq_exp] using hd.eventually_right_inverse,
      by simpa using hd.localInverse_continuousAt⟩
  have hg0 : g 1 = 0 := by simpa only [matrixExp_zero] using hleft.self_of_nhds
  obtain ⟨V, hV, hV0, hdetect⟩ := exists_open_exp_skew_detection q
  let D : Set (Mat q) := {H | frobSq H < η ^ 2}
  have hD : IsOpen D := isOpen_lt continuous_frobSq continuous_const
  have hD0 : (0 : Mat q) ∈ D := by
    change frobSq (0 : Mat q) < η ^ 2
    simpa [frobSq, frobInner] using sq_pos_of_pos hη
  have hlog : ∀ᶠ A in 𝓝 (1 : Mat q), g A ∈ D ∩ V :=
    hgc.tendsto.eventually (hg0 ▸ (hD.inter hV).mem_nhds ⟨hD0, hV0⟩)
  obtain ⟨U, hsub, hU, h1⟩ := mem_nhds_iff.mp (hright.and hlog)
  refine ⟨(fun A : Mat q => Q₀ᵀ * A) ⁻¹' U, hU.preimage (by fun_prop),
    by change Q₀ᵀ * Q₀ ∈ U; simpa only [hQ₀.1] using h1, fun A hA ho => ?_⟩
  obtain ⟨he, hD', hV'⟩ := hsub hA
  refine ⟨g (Q₀ᵀ * A), hdetect _ hV' (he.symm ▸ hQ₀.transpose.mul ho), hD', ?_⟩
  change Q₀ * matrixExp (g (Q₀ᵀ * A)) = A
  rw [he, ← Matrix.mul_assoc, hQ₀.2, Matrix.one_mul]

attribute [local instance] Matrix.normedAddCommGroup

theorem originalF_mem_localFamily {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    (ell r : Fin q → ℝ) (c z : Mat q) (u : CircleVector)
    (hc : IsSkew c) (hz : IsSkew z) (hu : OnCircle u) :
    originalF Q₀ (ell, r, c, z, u) ∈ localFamily q := by
  obtain ⟨S, hS, hdiag⟩ := exists_common_middle_diagonalizer u hu
  let A := originalPsi Q₀ (c + z)
  let B := originalPsi Q₀ (c - z)
  let U : Fin q → Mat 2 := fun i => rotation (ell i) * S
  let V : Fin q → Mat 2 := fun j => Sᵀ * rotation (r j)
  have hU : ∀ i, Orthogonal (U i) := fun i => (rotation_orthogonal (ell i)).mul hS
  have hV : ∀ j, Orthogonal (V j) := fun j => hS.transpose.mul (rotation_orthogonal (r j))
  have hA : Orthogonal A := hQ₀.mul (matrixExp_orthogonal (by change (c + z)ᵀ = -(c + z); rw [Matrix.transpose_add, hc, hz]; abel))
  have hB : Orthogonal B := hQ₀.mul (matrixExp_orthogonal (by change (c - z)ᵀ = -(c - z); rw [Matrix.transpose_sub, hc, hz]; abel))
  have he : originalF Q₀ (ell, r, c, z, u) =
      flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
    ext i j
    let x : Fin q × Fin 2 := finProdFinEquiv.symm i
    let y : Fin q × Fin 2 := finProdFinEquiv.symm j
    change (rotation (ell x.1) * middleBlock (A x.1 y.1) (B x.1 y.1) u * rotation (r y.1)) x.2 y.2 =
      (blockMatrix U * centralPair A B * blockMatrix V) x y
    rw [small_block_sandwich, hdiag]
    simp only [U, V, x, y, Matrix.mul_assoc]
  rw [he]
  exact block_sandwich_mem_localFamily U V A B hU hV hA hB

theorem originalF_mem_of_mem_K {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀)
    {η : ℝ} {p : OriginalParameters q} (hp : p ∈ originalK q η) :
    originalF Q₀ p ∈ localFamily q := by
  rcases p with ⟨ell, r, c, z, u⟩
  rcases hp with ⟨_, _, _, hc, hz, _, _, hu⟩
  exact originalF_mem_localFamily Q₀ hQ₀ ell r c z u hc hz hu

theorem basePoint_mem_localFamily {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) :
    basePoint Q₀ ∈ localFamily q := by
  have h := originalF_mem_of_mem_K Q₀ hQ₀ (originalBaseParameters_mem q (le_refl (0 : ℝ)))
  rwa [originalF_basePoint] at h

def DiagonalTwo (D : Mat 2) : Prop := D 0 1 = 0 ∧ D 1 0 = 0

theorem diagonalTwo_symmetric (D : Mat 2) (hD : DiagonalTwo D) : Dᵀ = D := by
  have heq : D = diagTwo (D 0 0) (D 1 1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, hD.1, hD.2]
  rw [heq]; ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo]

theorem diagonalTwo_involution {D : Mat 2} (hd : DiagonalTwo D)
    (ho : Orthogonal D) : D * D = 1 := by
  simpa only [diagonalTwo_symmetric D hd] using ho.1

def gaugeMiddle {q : ℕ} (D E : Fin q → Mat 2) (a : Fin 2) (A : Mat q) : Mat q :=
  Matrix.diagonal (fun i => D i a a) * A * Matrix.diagonal (fun j => E j a a)

@[simp] theorem gaugeMiddle_apply {q : ℕ} (D E : Fin q → Mat 2)
    (a : Fin 2) (A : Mat q) (i j : Fin q) :
    gaugeMiddle D E a A i j = D i a a * A i j * E j a a := by
  simp [gaugeMiddle, Matrix.mul_apply, Matrix.diagonal]

theorem gaugeMiddle_orthogonal {q : ℕ} (D E : Fin q → Mat 2)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (a : Fin 2) (A : Mat q) (hA : Orthogonal A) : Orthogonal (gaugeMiddle D E a A) := by
  have h_entry {M : Mat 2} (hd : DiagonalTwo M) (ho : Orthogonal M) : (M a a) ^ 2 = 1 := by
    have h := congrFun (congrFun ho.1 a) a
    fin_cases a <;> simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_two, hd.1, hd.2, pow_two] using h
  have h_diag (s : Fin q → ℝ) (hs : ∀ i, (s i) ^ 2 = 1) : Orthogonal (Matrix.diagonal s) := by
    constructor <;> ext i j <;> by_cases hij : i = j <;>
      simp [Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply, Matrix.one_apply, hij, eq_comm, ← pow_two, hs]
  exact ((h_diag _ fun i => h_entry (hD i).1 (hD i).2).mul hA).mul
    (h_diag _ fun j => h_entry (hE j).1 (hE j).2)

theorem diagonal_gauge_middle (D E : Mat 2) (hD : DiagonalTwo D)
    (hE : DiagonalTwo E) (a b : ℝ) :
    D * diagTwo a b * E = diagTwo (D 0 0 * a * E 0 0) (D 1 1 * b * E 1 1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, hD.1, hD.2, hE.1, hE.2]

theorem normalize_scalar_base_fibre {q : ℕ} (hq : 0 < q)
    (Q₀ A B : Mat q) (hentries : ∀ i j, Q₀ i j ≠ 0)
    (U V : Fin q → Mat 2) (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hbase : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q₀ i j • (1 : Mat 2)) :
    ∃ (S : Mat 2) (D E : Fin q → Mat 2), Orthogonal S ∧
      (∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i)) ∧
      (∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j)) ∧
      (∀ i, U i * D i * S = 1) ∧ (∀ j, Sᵀ * E j * V j = 1) ∧
      gaugeMiddle D E 0 A = Q₀ ∧ gaugeMiddle D E 1 B = Q₀ := by
  let i₀ : Fin q := ⟨0, hq⟩
  let S := V i₀
  let D : Fin q → Mat 2 := fun i => S * U i
  let E : Fin q → Mat 2 := fun j => V j * Sᵀ
  have hS : Orthogonal S := hV i₀
  have hdiag (i j : Fin q) : DiagonalTwo (V j * U i) := by
    have hh' : diagTwo (A i j) (B i j) = Q₀ i j • ((U i)ᵀ * (V j)ᵀ) := by
      calc diagTwo (A i j) (B i j) = (U i)ᵀ * (U i * diagTwo (A i j) (B i j) * V j) * (V j)ᵀ := by
            simp only [← Matrix.mul_assoc, (hU i).1, Matrix.one_mul]
            rw [Matrix.mul_assoc _ (V j) (V j)ᵀ, (hV j).2, Matrix.mul_one]
        _ = (U i)ᵀ * (Q₀ i j • (1 : Mat 2)) * (V j)ᵀ := by rw [hbase i j]
        _ = _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have h01 : Q₀ i j * ((U i)ᵀ * (V j)ᵀ) 0 1 = 0 := by simpa [diagTwo] using (congrFun (congrFun hh' 0) 1).symm
    have h10 : Q₀ i j * ((U i)ᵀ * (V j)ᵀ) 1 0 = 0 := by simpa [diagTwo] using (congrFun (congrFun hh' 1) 0).symm
    have h_ut : DiagonalTwo ((U i)ᵀ * (V j)ᵀ) :=
      ⟨(mul_eq_zero.mp h01).resolve_left (hentries i j), (mul_eq_zero.mp h10).resolve_left (hentries i j)⟩
    have h_t : DiagonalTwo ((U i)ᵀ * (V j)ᵀ)ᵀ := ⟨h_ut.2, h_ut.1⟩
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h_t
  have hdD (i : Fin q) : DiagonalTwo (D i) := hdiag i i₀
  have hdE (j : Fin q) : DiagonalTwo (E j) := by
    have he : E j = (V j * U i₀) * (S * U i₀)ᵀ := by
      dsimp [E]; rw [Matrix.transpose_mul]
      calc V j * Sᵀ = V j * (U i₀ * (U i₀)ᵀ) * Sᵀ := by rw [(hU i₀).2, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [he]
    have d_mul {M₁ M₂ : Mat 2} (h1 : DiagonalTwo M₁) (h2 : DiagonalTwo M₂) : DiagonalTwo (M₁ * M₂) :=
      ⟨by simp [Matrix.mul_apply, Fin.sum_univ_two, h1.1, h1.2, h2.1, h2.2],
       by simp [Matrix.mul_apply, Fin.sum_univ_two, h1.1, h1.2, h2.1, h2.2]⟩
    exact d_mul (hdiag i₀ j) ⟨(hdiag i₀ i₀).2, (hdiag i₀ i₀).1⟩
  have hoD (i : Fin q) : Orthogonal (D i) := hS.mul (hU i)
  have hoE (j : Fin q) : Orthogonal (E j) := (hV j).mul hS.transpose
  have hleft (i : Fin q) : U i * D i * S = 1 := by
    rw [← diagonalTwo_symmetric (D i) (hdD i)]; dsimp [D]; rw [Matrix.transpose_mul]
    calc U i * ((U i)ᵀ * Sᵀ) * S = (U i * (U i)ᵀ) * (Sᵀ * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hU i).2, hS.1, Matrix.one_mul]
  have hright (j : Fin q) : Sᵀ * E j * V j = 1 := by
    rw [← diagonalTwo_symmetric (E j) (hdE j)]; dsimp [E]; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Sᵀ * (S * (V j)ᵀ) * V j = (Sᵀ * S) * ((V j)ᵀ * V j) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS.1, (hV j).1, Matrix.one_mul]
  have hmiddle (i j : Fin q) :
      diagTwo (gaugeMiddle D E 0 A i j) (gaugeMiddle D E 1 B i j) = Q₀ i j • (1 : Mat 2) := by
    rw [gaugeMiddle_apply, gaugeMiddle_apply, ← diagonal_gauge_middle (D i) (E j) (hdD i) (hdE j)]
    change (S * U i) * diagTwo (A i j) (B i j) * (V j * Sᵀ) = _
    calc _ = S * (U i * diagTwo (A i j) (B i j) * V j) * Sᵀ := by simp only [Matrix.mul_assoc]
      _ = S * (Q₀ i j • (1 : Mat 2)) * Sᵀ := by rw [hbase]
      _ = _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS.2]
  exact ⟨S, D, E, hS, fun i => ⟨hdD i, hoD i⟩, fun j => ⟨hdE j, hoE j⟩, hleft, hright,
    by ext i j; simpa [diagTwo, Matrix.one_apply] using congrFun (congrFun (hmiddle i j) 0) 0,
    by ext i j; simpa [diagTwo, Matrix.one_apply] using congrFun (congrFun (hmiddle i j) 1) 1⟩

theorem conjugate_reflection_coordinates (C : Mat 2) (hC : Orthogonal C) :
    ∃ u : CircleVector, OnCircle u ∧
      ∀ a b : ℝ, middleBlock a b u = Cᵀ * diagTwo a b * C := by
  let F : Mat 2 := diagTwo 1 (-1)
  have hF : Orthogonal F := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [F, diagTwo, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply]
  let K := Cᵀ * F * C
  have hK : Orthogonal K := (hC.transpose.mul hF).mul hC
  have hs : Kᵀ = K := by
    dsimp [K]; rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    have hf : Fᵀ = F := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hf, Matrix.mul_assoc]
  have hr0 := congrFun (congrFun hC.2 0) 0
  have hr1 := congrFun (congrFun hC.2 1) 1
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply] at hr0 hr1
  have htrace : K 1 1 = -K 0 0 := by
    dsimp [K, F]; simp [diagTwo, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    nlinarith [hr0, hr1]
  let u : CircleVector := ![K 0 0, K 0 1]
  have he : T u = K := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [T, u, htrace]
    exact (congrFun (congrFun hs 0) 1).symm
  have hu : OnCircle u := by
    simpa [OnCircle, u, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.one_apply, pow_two] using congrFun (congrFun hK.2 0) 0
  refine ⟨u, hu, fun a b => ?_⟩
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hC.1]
  change ((a + b) / 2) • (1 : Mat 2) + ((a - b) / 2) • T u = ((a + b) / 2) • (1 : Mat 2) + ((a - b) / 2) • K
  rw [he]

theorem original_coordinates_of_gauged_near {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (η : ℝ) (hη : 0 < η)
    (L : Set (Mat q))
    (hlog : ∀ A ∈ L, Orthogonal A → ∃ H : Mat q,
      IsSkew H ∧ frobSq H < η ^ 2 ∧ originalPsi Q₀ H = A)
    (S : Mat 2) (D E : Fin q → Mat 2) (hS : Orthogonal S)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (U V : Fin q → Mat 2) (A B : Mat q)
    (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hA : Orthogonal A) (hB : Orthogonal B)
    (hUl : ∀ i, U i * D i * S ∈ rotationChartDomain (η / 4))
    (hVr : ∀ j, Sᵀ * E j * V j ∈ rotationChartDomain (η / 4))
    (hAL : gaugeMiddle D E 0 A ∈ L) (hBL : gaugeMiddle D E 1 B ∈ L) :
    ∃ p ∈ originalK q η, originalF Q₀ p =
      flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  let i₀ : Fin q := ⟨0, hq⟩
  let α : Fin q → ℝ := fun i => localRotationAngle (U i * D i * S)
  let β : Fin q → ℝ := fun j => localRotationAngle (Sᵀ * E j * V j)
  have hα (i : Fin q) : rotation (α i) = U i * D i * S :=
    rotation_localRotationAngle _ (((hU i).mul (hD i).2).mul hS) (hUl i).1 (hUl i).2.1
  have hβ (j : Fin q) : rotation (β j) = Sᵀ * E j * V j :=
    rotation_localRotationAngle _ ((hS.transpose.mul (hE j).2).mul (hV j)) (hVr j).1 (hVr j).2.1
  obtain ⟨H, hH, hHn, hHA⟩ := hlog _ hAL (gaugeMiddle_orthogonal D E hD hE 0 A hA)
  obtain ⟨K, hK, hKn, hKB⟩ := hlog _ hBL (gaugeMiddle_orthogonal D E hD hE 1 B hB)
  let c := (1 / 2 : ℝ) • (H + K)
  let z := (1 / 2 : ℝ) • (H - K)
  have hc : IsSkew c := isSkew_smul _ (by change (H + K)ᵀ = -(H + K); rw [Matrix.transpose_add, hH, hK]; abel)
  have hz : IsSkew z := isSkew_smul _ (by change (H - K)ᵀ = -(H - K); rw [Matrix.transpose_sub, hH, hK]; abel)
  have hsum : frobSq c + frobSq z = (frobSq H + frobSq K) / 2 := by
    have hscale (M : Mat q) : frobSq ((1 / 2 : ℝ) • M) = (1 / 2 : ℝ) ^ 2 * frobSq M := by
      unfold frobSq
      rw [frobInner_smul_left, frobInner_comm M ((1 / 2 : ℝ) • M), frobInner_smul_left]; ring
    dsimp [c, z]; rw [hscale, hscale, frobSq_add, frobSq_sub]; ring
  have hcn : frobSq c < η ^ 2 := by linarith [frobSq_nonneg z]
  have hzn : frobSq z < η ^ 2 := by linarith [frobSq_nonneg c]
  have hplus : c + z = H := by ext i j; simp [c, z]; ring
  have hminus : c - z = K := by ext i j; simp [c, z]; ring
  obtain ⟨u, hu, hconj⟩ := conjugate_reflection_coordinates (S * rotation (β i₀))
    (hS.mul (rotation_orthogonal (β i₀)))
  let ell : Fin q → ℝ := fun i => α i + β i₀
  let r : Fin q → ℝ := fun j => β j - β i₀
  have hell (i : Fin q) : |ell i| ≤ η := by
    have := (hUl i).2.2; have := (hVr i₀).2.2; dsimp [ell]; linarith [abs_add_le (α i) (β i₀)]
  have hr (j : Fin q) : |r j| ≤ η := by
    have := (hVr j).2.2; have := (hVr i₀).2.2; dsimp [r]; linarith [abs_sub (β j) (β i₀)]
  have hr0 (j : Fin q) (hj : j.val = 0) : r j = 0 := by rw [show j = i₀ from Fin.ext hj]; exact sub_self _
  refine ⟨(ell, r, c, z, u), ⟨hell, hr, hr0, hc, hz, hcn.le, hzn.le, hu⟩, ?_⟩
  ext i j
  let x : Fin q × Fin 2 := finProdFinEquiv.symm i
  let y : Fin q × Fin 2 := finProdFinEquiv.symm j
  change (rotation (ell x.1) * middleBlock
    (originalPsi Q₀ (c + z) x.1 y.1) (originalPsi Q₀ (c - z) x.1 y.1) u *
    rotation (r y.1)) x.2 y.2 =
    (blockMatrix U * centralPair A B * blockMatrix V) x y
  rw [small_block_sandwich, hplus, hminus, hHA, hKB]
  have o_canc (W : Mat 2) (hW : Orthogonal W) (X : Mat 2) : W * (Wᵀ * X) = X := by
    rw [← Matrix.mul_assoc, hW.2, Matrix.one_mul]
  have i_canc (W : Mat 2) (hW : W * W = 1) (X : Mat 2) : W * (W * X) = X := by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have he : rotation (α x.1 + β i₀) * middleBlock (gaugeMiddle D E 0 A x.1 y.1) (gaugeMiddle D E 1 B x.1 y.1) u * rotation (β y.1 - β i₀) =
      rotation (α x.1) * Sᵀ * diagTwo (gaugeMiddle D E 0 A x.1 y.1) (gaugeMiddle D E 1 B x.1 y.1) * S * rotation (β y.1) := by
    rw [hconj, rotation_add, Matrix.transpose_mul]
    have htail : rotation (β i₀) * rotation (β y.1 - β i₀) = rotation (β y.1) := by
      rw [← rotation_add]; congr 1; ring
    simp only [Matrix.mul_assoc, o_canc (rotation (β i₀)) (rotation_orthogonal (β i₀)), htail]
  change _ = (U x.1 * diagTwo (A x.1 y.1) (B x.1 y.1) * V y.1) x.2 y.2
  rw [show ell x.1 = α x.1 + β i₀ from rfl, show r y.1 = β y.1 - β i₀ from rfl,
    he, hα, hβ, gaugeMiddle_apply, gaugeMiddle_apply,
    ← diagonal_gauge_middle (D x.1) (E y.1) (hD x.1).1 (hE y.1).1]
  simp only [Matrix.mul_assoc, o_canc S hS,
    i_canc (D x.1) (diagonalTwo_involution (hD x.1).1 (hD x.1).2),
    i_canc (E y.1) (diagonalTwo_involution (hE y.1).1 (hE y.1).2)]

theorem exists_open_original_local_coverage {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ W : Set (Mat (q * 2)), IsOpen W ∧ basePoint Q₀ ∈ W ∧
      ∀ M ∈ localFamily q, M ∈ W → ∃ p ∈ originalK q η, originalF Q₀ p = M := by
  have hlocal (p : SmallBlockParameters q) (hp : p ∈ smallFactorSet q)
      (he : smallFactorMap p = basePoint Q₀) :
      ∃ N : Set (SmallBlockParameters q), IsOpen N ∧ p ∈ N ∧
        ∀ p' ∈ N, p' ∈ smallFactorSet q → smallFactorMap p' ∈ originalF Q₀ '' originalK q η := by
    rcases p with ⟨U, A, B, V⟩
    rcases hp with ⟨hU, hA, hB, hV⟩
    obtain ⟨S, D, E, hS, hD, hE, hleft, hright, hAg, hBg⟩ := normalize_scalar_base_fibre hq
      Q₀ A B hentries U V hU hV (smallFactorMap_eq_base_blocks Q₀ _ he)
    obtain ⟨L, hL, hQL, hlog⟩ := exists_open_frob_small_skew_log Q₀ hQ₀ η hη
    let N : Set (SmallBlockParameters q) := {p' |
      (∀ i, p'.1 i * D i * S ∈ rotationChartDomain (η / 4)) ∧
      (∀ j, Sᵀ * E j * p'.2.2.2 j ∈ rotationChartDomain (η / 4)) ∧
      gaugeMiddle D E 0 p'.2.1 ∈ L ∧ gaugeMiddle D E 1 p'.2.2.1 ∈ L}
    have hNU : IsOpen {p' : SmallBlockParameters q | ∀ i, p'.1 i * D i * S ∈ rotationChartDomain (η / 4)} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => (isOpen_rotationChartDomain (η / 4)).preimage (by fun_prop)
    have hNV : IsOpen {p' : SmallBlockParameters q | ∀ j, Sᵀ * E j * p'.2.2.2 j ∈ rotationChartDomain (η / 4)} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => (isOpen_rotationChartDomain (η / 4)).preimage (by fun_prop)
    have hNA : IsOpen {p' : SmallBlockParameters q | gaugeMiddle D E 0 p'.2.1 ∈ L} := by
      apply hL.preimage; unfold gaugeMiddle; fun_prop
    have hNB : IsOpen {p' : SmallBlockParameters q | gaugeMiddle D E 1 p'.2.2.1 ∈ L} := by
      apply hL.preimage; unfold gaugeMiddle; fun_prop
    have hI : (1 : Mat 2) ∈ rotationChartDomain (η / 4) := one_mem_rotationChartDomain (by positivity)
    refine ⟨N, hNU.inter (hNV.inter (hNA.inter hNB)),
      ⟨fun i => by simpa only [hleft] using hI, fun j => by simpa only [hright] using hI,
        by simpa only [hAg] using hQL, by simpa only [hBg] using hQL⟩, ?_⟩
    rintro ⟨U', A', B', V'⟩ ⟨hUl, hVr, hAL, hBL⟩ ⟨hU', hA', hB', hV'⟩
    exact original_coordinates_of_gauged_near hq Q₀ η hη L hlog
      S D E hS hD hE U' V' A' B' hU' hV' hA' hB' hUl hVr hAL hBL
  let opens : Set (Set (SmallBlockParameters q)) :=
    {N | IsOpen N ∧ ∀ k ∈ N, k ∈ smallFactorSet q → smallFactorMap k ∈ originalF Q₀ '' originalK q η}
  let O : Set (SmallBlockParameters q) := ⋃ N ∈ opens, N
  have hO : IsOpen O := isOpen_iUnion fun _ => isOpen_iUnion fun hN => hN.1
  have hfull : ∀ k ∈ smallFactorSet q, smallFactorMap k = basePoint Q₀ → k ∈ O := fun k hk he => by
    obtain ⟨N, hN, hkN, hmap⟩ := hlocal k hk he
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨⟨hN, hmap⟩, hkN⟩⟩
  obtain ⟨W, hW, hbase, hcover⟩ := compact_full_fibre_neighbourhood smallFactorMap
    (continuous_smallFactorMap q) (smallFactorSet q) (isCompact_smallFactorSet q)
    O hO (basePoint Q₀) hfull
  refine ⟨W, hW, hbase, fun M hM hMW => ?_⟩
  obtain ⟨k, ⟨hks, hkO⟩, he⟩ := hcover M hMW (by simpa only [image_smallFactorMap] using hM)
  obtain ⟨N, hkN⟩ := Set.mem_iUnion.mp hkO
  obtain ⟨hN, hkN⟩ := Set.mem_iUnion.mp hkN
  exact he ▸ hN.2 k hkN hks

structure PointedNeighbourhoodModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_nhds : source ∈ 𝓝 x
  target_nhds : target ∈ 𝓝 y
  chart : ↥source ≃ₜ ↥target
  map_point : ∀ hx : x ∈ source, (chart ⟨x, hx⟩).val = y

def familyBase {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) : ↥(localFamily q) :=
  ⟨basePoint Q₀, basePoint_mem_localFamily Q₀ hQ₀⟩

def compactSourceInFamily {q : ℕ} (Q₀ : Mat q) (η : ℝ) : Set ↥(localFamily q) :=
  {M | M.val ∈ OriginalFImage Q₀ η}

def compactSourceHomeomorph {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (η : ℝ) :
    ↥(compactSourceInFamily Q₀ η) ≃ₜ OriginalFImage Q₀ η where
  toFun M := ⟨M.val.val, M.property⟩
  invFun M := ⟨⟨M.val, by obtain ⟨p, he⟩ := M.property; rw [← he]; exact originalF_mem_of_mem_K Q₀ hQ₀ p.property⟩, M.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem original_pointed_neighbourhood_model {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    Nonempty (PointedNeighbourhoodModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨η, hη, hfib⟩ := original_same_fibres hq Q₀ hQ₀ hentries
  let : CompactSpace ↥(originalK q η) := isCompact_iff_compactSpace.mp (isCompact_originalK q η)
  obtain ⟨h, he⟩ := exists_homeomorph_ranges_of_same_fibres
    (fun p : ↥(originalK q η) => originalF Q₀ p.val) (@independentG q η)
    ((continuous_originalF Q₀).comp continuous_subtype_val)
    (continuous_independentG q η)
    (fun p p' => (hfib p.val p.property p'.val p'.property).trans (independentG_eq_iff p p').symm)
  obtain ⟨W, hW, hbase, hcover⟩ := exists_open_original_local_coverage hq Q₀ hQ₀ hentries η hη
  let U : Set (ModelCoordinates q) := {x | modelRadiusSq (decodeModel x).val < η ^ 2}
  have hU : IsOpen U := isOpen_lt ((continuous_modelRadiusSq q).comp (continuous_subtype_val.comp (continuous_decodeModel q))) continuous_const
  have hzero : modelCoordinatesZero q ∈ U := by
    change modelRadiusSq (decodeModel (modelCoordinatesZero q)).val < η ^ 2
    rw [decode_modelCoordinatesZero]; simpa [modelRadiusSq, frobSq, frobInner] using sq_pos_of_pos hη
  refine ⟨{
    source := compactSourceInFamily Q₀ η
    target := Set.range (@independentG q η)
    source_nhds := Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hbase) fun M hM => by
      obtain ⟨p, hp, heq⟩ := hcover M.val M.property hM; exact ⟨⟨p, hp⟩, heq⟩
    target_nhds := Filter.mem_of_superset (hU.mem_nhds hzero) fun x hx => by
      obtain ⟨p, hp, heq⟩ := small_modelRadius_mem_originalG hη (decodeModel x).val (decodeModel x).property hx
      have hh : originalGAsModel (⟨p, hp⟩ : ↥(originalK q η)) = decodeModel x := Subtype.ext heq
      exact ⟨⟨p, hp⟩, by change encodeModel (originalGAsModel ⟨p, hp⟩) = x; rw [hh, encode_decodeModel]⟩
    chart := (compactSourceHomeomorph Q₀ hQ₀ η).trans h
    map_point := fun hx => ?_ }⟩
  let p₀ : ↥(originalK q η) := ⟨originalBaseParameters q, originalBaseParameters_mem q hη.le⟩
  have he' := congrArg Subtype.val (he p₀)
  have hs : compactSourceHomeomorph Q₀ hQ₀ η ⟨familyBase Q₀ hQ₀, hx⟩ = ⟨originalF Q₀ p₀.val, ⟨p₀, rfl⟩⟩ :=
    Subtype.ext (originalF_basePoint Q₀).symm
  have hp₀ : originalGAsModel p₀ = decodeModel (modelCoordinatesZero q) :=
    Subtype.ext ((originalG_basePoint q).trans (decode_modelCoordinatesZero q).symm)
  change (h (compactSourceHomeomorph Q₀ hQ₀ η ⟨familyBase Q₀ hQ₀, hx⟩)).val = _
  rw [hs, he']
  change encodeModel (originalGAsModel p₀) = modelCoordinatesZero q
  rw [hp₀, encode_decodeModel]

end GS.NonmanifoldCompletion
