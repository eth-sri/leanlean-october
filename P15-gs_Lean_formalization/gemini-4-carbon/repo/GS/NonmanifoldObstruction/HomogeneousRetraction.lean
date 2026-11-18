module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry GS.Nonmanifold Filter
open scoped BigOperators Topology
namespace GS.NonmanifoldObstruction

abbrev RankCone (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1}

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def coneZero : RankCone κ := ⟨0, by simp⟩
def vectorSq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2
abbrev ConeSpace (ι κ : Type*) [Fintype κ] [DecidableEq κ] := (ι → ℝ) × RankCone κ
def productZero : ConeSpace ι κ := (0, coneZero)

def rowGram (W : Matrix (Fin 2) κ ℝ) : Mat 2 := fun i j => ∑ k, W i k * W j k
def circleCoord (W : Matrix (Fin 2) κ ℝ) : CircleVector :=
  ![rowGram W 0 0 - rowGram W 1 1, 2 * rowGram W 0 1]
def frobRad (W : Matrix (Fin 2) κ ℝ) : ℝ := Real.sqrt (frobSq W)
def planeSq (v : CircleVector) : ℝ := v 0 ^ 2 + v 1 ^ 2
def planeRad (v : CircleVector) : ℝ := Real.sqrt (planeSq v)

private theorem circleCoord_sq (W : Matrix (Fin 2) κ ℝ) (hW : W.rank ≤ 1) :
    planeSq (circleCoord W) = frobSq W ^ 2 := by
  obtain ⟨u, hu, z, rfl⟩ := exists_unit_outer_of_rank_le_one W hW
  rw [frobSq_outer hu z]
  have hg (i j : Fin 2) : rowGram (outer u z) i j = (u i * u j) * ∑ k, z k ^ 2 := by
    simp only [rowGram, outer, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  calc planeSq (circleCoord (outer u z))
    _ = (rowGram (outer u z) 0 0 - rowGram (outer u z) 1 1) ^ 2 + (2 * rowGram (outer u z) 0 1) ^ 2 := rfl
    _ = (u 0 ^ 2 + u 1 ^ 2) ^ 2 * (∑ j, z j ^ 2) ^ 2 := by simp only [hg]; ring
    _ = (∑ j, z j ^ 2) ^ 2 := by rw [show u 0 ^ 2 + u 1 ^ 2 = 1 from hu]; ring

def coneToPlane (W : RankCone κ) : CircleVector := fun i => circleCoord W.val i / frobRad W.val

@[simp] theorem coneToPlane_zero : coneToPlane (coneZero : RankCone κ) = 0 := by
  ext i; simp [coneToPlane, coneZero, circleCoord, rowGram, frobRad, frobSq, frobInner]

theorem coneToPlane_sq (W : RankCone κ) : planeSq (coneToPlane W) = frobSq W.val := by
  by_cases hz : W.val = 0
  · rw [show W = coneZero from Subtype.ext hz, coneToPlane_zero]
    simp [planeSq, coneZero, frobSq, frobInner]
  · have hr : frobRad W.val ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hz))
    have hn : frobRad W.val ^ 2 = frobSq W.val := Real.sq_sqrt (frobSq_nonneg W.val)
    have hg := circleCoord_sq W.val W.property
    dsimp [planeSq, coneToPlane] at hg ⊢
    field_simp [hr]; nlinarith [congrArg (frobSq W.val * ·) hn]

theorem coneToPlane_zero_iff (W : RankCone κ) : coneToPlane W = 0 ↔ W = coneZero := by
  refine ⟨fun h => ?_, fun h => h ▸ coneToPlane_zero⟩
  have hs := coneToPlane_sq W
  rw [h, show planeSq 0 = 0 by simp [planeSq]] at hs
  exact Subtype.ext ((frobSq_eq_zero_iff W.val).mp hs.symm)

theorem continuous_coneToPlane : Continuous (coneToPlane : RankCone κ → CircleVector) := by
  refine continuous_iff_continuousAt.mpr fun W => continuousAt_pi.mpr fun i => ?_
  have hcRad : Continuous (fun Z : RankCone κ => frobRad Z.val) :=
    Real.continuous_sqrt.comp (continuous_frobSq.comp continuous_subtype_val)
  by_cases hz : W.val = 0
  · substs; rw [show W = coneZero from Subtype.ext hz]
    have hr : Tendsto (fun Z : RankCone κ => frobRad Z.val) (𝓝 coneZero) (𝓝 0) := by
      simpa [ContinuousAt, coneZero, frobRad, frobSq, frobInner] using hcRad.continuousAt (x := coneZero)
    change Tendsto (fun Z : RankCone κ => coneToPlane Z i) (𝓝 coneZero) (𝓝 (coneToPlane coneZero i))
    rw [coneToPlane_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hr.neg) hr (fun Z => ?_) (fun Z => ?_)
    all_goals
      have hn := coneToPlane_sq Z
      have hsq : frobRad Z.val ^ 2 = frobSq Z.val := Real.sq_sqrt (frobSq_nonneg Z.val)
      have hp : 0 ≤ frobRad Z.val := Real.sqrt_nonneg _
      have hi : (coneToPlane Z i) ^ 2 ≤ frobSq Z.val := by
        fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, id_eq] <;> dsimp [planeSq] at hn <;>
          nlinarith [sq_nonneg (coneToPlane Z 0), sq_nonneg (coneToPlane Z 1)]
      have habs : |coneToPlane Z i| ≤ frobRad Z.val := by nlinarith [sq_abs (coneToPlane Z i), abs_nonneg (coneToPlane Z i)]
      first | exact (abs_le.mp habs).1 | exact (abs_le.mp habs).2
  · have hcc : Continuous (circleCoord : Matrix (Fin 2) κ ℝ → CircleVector) :=
      continuous_pi fun j => by fin_cases j <;> simp [circleCoord, rowGram] <;> fun_prop
    exact ((continuous_apply i).comp (hcc.comp continuous_subtype_val)).continuousAt.div
      hcRad.continuousAt (ne_of_gt (Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hz)))

def planeMat (v : CircleVector) : Mat 2 :=
  !![(planeRad v + v 0) / 2, v 1 / 2; v 1 / 2, (planeRad v - v 0) / 2]

def padTwo (d : ℕ) (A : Mat 2) : Matrix (Fin 2) (Fin (d + 2)) ℝ :=
  fun i => Fin.cases (A i 0) (Fin.cases (A i 1) (fun _ : Fin d => 0))

def planeToCone (d : ℕ) (v : CircleVector) : RankCone (Fin (d + 2)) :=
  ⟨padTwo d (planeMat v), by
    have h : planeRad v ^ 2 = planeSq v := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hA : (planeMat v).rank ≤ 1 := rank_le_one_of_two_column_minors _ fun j k => by
      dsimp [planeSq] at h; fin_cases j <;> fin_cases k <;> simp [planeMat] <;> nlinarith [h]
    refine rank_le_one_of_two_column_minors _ fun j k => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => by simp [padTwo]) j) j <;>
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun _ => by simp [padTwo]) k) k
    · simp [padTwo]
    · exact rank_le_one_two_column_minor _ hA 0 1
    · exact rank_le_one_two_column_minor _ hA 1 0
    · simp [padTwo]⟩

theorem continuous_planeToCone (d : ℕ) : Continuous (planeToCone d) := by
  have hcR : Continuous planeRad := by unfold planeRad planeSq; fun_prop
  apply Continuous.subtype_mk
  apply continuous_pi; intro i; apply continuous_pi; intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => continuous_const) j) j <;>
    fin_cases i <;> dsimp [padTwo, planeMat]
  · exact (hcR.add (continuous_apply 0)).div_const 2
  · exact (continuous_apply 1).div_const 2
  · exact (continuous_apply 1).div_const 2
  · exact (hcR.sub (continuous_apply 0)).div_const 2

@[simp] theorem planeToCone_zero (d : ℕ) : planeToCone d 0 = coneZero := by
  apply Subtype.ext; ext i j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j <;>
    fin_cases i <;> simp [planeToCone, planeMat, planeRad, planeSq, padTwo, coneZero] <;> rfl

theorem coneToPlane_planeToCone (d : ℕ) (v : CircleVector) :
    coneToPlane (planeToCone d v) = v := by
  by_cases hv : v = 0
  · subst hv; simp
  · have hsq : planeRad v ^ 2 = planeSq v := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hr : planeRad v ≠ 0 := fun h0 => hv <| by
      rw [h0] at hsq; dsimp [planeSq] at hsq
      ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hfrob : frobRad (planeToCone d v).val = planeRad v := by
      dsimp [frobRad, planeRad]; congr 1
      dsimp [planeSq] at hsq ⊢
      simp [planeToCone, padTwo, frobSq, frobInner, planeMat, Fin.sum_univ_succ, Fin.sum_univ_two]
      nlinarith [hsq]
    have hg : rowGram (planeToCone d v).val = planeRad v • planeMat v := by
      dsimp [planeSq] at hsq
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [rowGram, planeToCone, padTwo, planeMat, Fin.sum_univ_succ, Fin.sum_univ_two] <;> nlinarith [hsq]
    ext i
    change circleCoord (planeToCone d v).val i / frobRad (planeToCone d v).val = v i
    rw [hfrob]; fin_cases i <;> simp [circleCoord, hg, planeMat] <;> field_simp [hr] <;> ring

end GS.NonmanifoldObstruction
