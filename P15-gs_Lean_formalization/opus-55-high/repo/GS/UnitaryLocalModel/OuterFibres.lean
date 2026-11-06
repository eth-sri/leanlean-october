module

public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.Frobenius

@[expose] public section


/-!
# Exact fibres of the real three-row rank-one parametrization

These are the sphere fibres required by the unitary local model. The sign
identification and collapsed zero fibre are proved, including all degeneracies.
-/
noncomputable section
namespace GS.UnitaryLocalModel

section
variable {κ : Type*}
def sphereOuter (u : AxisVector) (z : κ → ℝ) : Matrix (Fin 3) κ ℝ :=
  fun i j => u i * z j

/-- The rank-one parameter map is continuous, without a nonzero hypothesis. -/
theorem continuous_sphereOuter :
    Continuous (fun p : AxisVector × (κ → ℝ) => sphereOuter p.1 p.2) := by
  unfold sphereOuter
  fun_prop

end

theorem onSphere_has_nonzero {u : AxisVector} (hu : OnSphere u) : ∃ i, u i ≠ 0 := by
  by_contra! h
  simp [OnSphere, h] at hu

section
variable {κ : Type*}
theorem sphereOuter_simultaneous_neg (u : AxisVector) (z : κ → ℝ) :
    sphereOuter (-u) (-z) = sphereOuter u z := by
  ext i j
  simp [sphereOuter]

theorem sphereOuter_zero_iff {u : AxisVector} (hu : OnSphere u) (z : κ → ℝ) :
    sphereOuter u z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; ext; simp [sphereOuter]⟩
  obtain ⟨i,hi⟩ := onSphere_has_nonzero hu
  funext j
  simpa [sphereOuter, hi] using congrFun (congrFun h i) j

theorem sphereOuter_col_sq {u : AxisVector} (hu : OnSphere u)
    (z : κ → ℝ) (j : κ) :
    sphereOuter u z 0 j ^ 2 + sphereOuter u z 1 j ^ 2 + sphereOuter u z 2 j ^ 2 = z j ^ 2 := by
  simp only [sphereOuter, mul_pow, ← add_mul]
  rw [hu, one_mul]

/-- The sphere variable does not change the squared Frobenius radius. -/
theorem frobSq_sphereOuter [Fintype κ] {u : AxisVector}
    (hu : OnSphere u) (z : κ → ℝ) :
    frobSq (sphereOuter u z) = ∑ j, z j ^ 2 := by
  simp only [frobSq, frobInner, Fin.sum_univ_three, ← Finset.sum_add_distrib, ← pow_two, sphereOuter_col_sq hu]

end

section
variable {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
/-- Equality plus one equal nonzero column coefficient fixes both factors. -/
theorem sphereOuter_unique_of_column (hu : OnSphere u) (h : sphereOuter u z = sphereOuter v w)
    (j : κ) (hzj : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have h i k : u i * z k = v i * w k := congrFun (congrFun h i) k
  obtain ⟨i,hi⟩ := onSphere_has_nonzero hu
  have huv : u = v := funext fun i => by grind [h i j]
  exact ⟨huv, funext fun k => by grind [h i k]⟩

/-- Nonzero rank-one fibres: exactly the simultaneous sign ambiguity. -/
theorem sphereOuter_fibres_nonzero (hu : OnSphere u) (hv : OnSphere v) (hz : z ≠ 0) :
    sphereOuter u z = sphereOuter v w ↔ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  refine ⟨fun h => ?_, by rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [sphereOuter_simultaneous_neg]⟩
  obtain ⟨j,hj⟩ : ∃ j, z j ≠ 0 := by by_contra! hn; exact hz (funext hn)
  have he : z j ^ 2 = w j ^ 2 := by rw [← sphereOuter_col_sq hu z j, h, sphereOuter_col_sq hv w j]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 he with hp | hp
  · exact .inl (sphereOuter_unique_of_column hu h j hj hp)
  · exact .inr (sphereOuter_unique_of_column hu (h.trans (sphereOuter_simultaneous_neg v w).symm) j hj hp)

/-- Explicit failure of uniqueness at the zero stratum. -/
theorem sphereOuter_zero_fibre (u v : AxisVector) :
    sphereOuter u (0 : κ → ℝ) = sphereOuter v (0 : κ → ℝ) := by
  ext i j
  simp [sphereOuter]

/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem sphereOuter_fibres (hu : OnSphere u) (hv : OnSphere v) :
    sphereOuter u z = sphereOuter v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · subst z
    rw [(sphereOuter_zero_iff hu 0).mpr rfl, eq_comm, sphereOuter_zero_iff hv]
    grind
  · simp [sphereOuter_fibres_nonzero hu hv hz, hz]

end

end GS.UnitaryLocalModel
