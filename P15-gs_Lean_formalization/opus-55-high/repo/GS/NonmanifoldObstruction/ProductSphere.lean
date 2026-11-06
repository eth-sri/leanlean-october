module

public import GS.NonmanifoldObstruction.HomogeneousRetraction

@[expose] public section


/-!
# Spherical sections in a punctured product, not just a punctured cone

The auxiliary sphere is the explicit unit sphere in (ι -> ℝ) x ℝ².
The corresponding product has the genuine rank-one cone as its last factor.
These maps do NOT delete the full singular stratum: (x,0) with x != 0
remains in the domain.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Nonmanifold
namespace GS.NonmanifoldObstruction

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

section
variable (x : ι → ℝ)
def vectorSq : ℝ := ∑ i, x i^2

theorem vectorSq_nonneg : 0 ≤ vectorSq x := by
  unfold vectorSq; positivity

theorem vectorSq_eq_zero_iff : vectorSq x = 0 ↔ x = 0 := by
  simp [vectorSq, Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg, funext_iff]

end

abbrev PlaneSpace (ι : Type*) := (ι → ℝ) × CircleVector
abbrev ConeSpace (ι κ : Type*) [Fintype κ] [DecidableEq κ] := (ι → ℝ) × RankCone κ

def productZero : ConeSpace ι κ := (0, coneZero)

def planeEnergy (p : PlaneSpace ι) : ℝ := vectorSq p.1 + planeSq p.2

section
variable (p : ConeSpace ι κ)
def coneEnergy : ℝ := vectorSq p.1 + frobSq p.2.val

theorem coneEnergy_nonneg : 0 ≤ coneEnergy p :=
  add_nonneg (vectorSq_nonneg _) (frobSq_nonneg _)

theorem coneEnergy_eq_zero_iff :
    coneEnergy p = 0 ↔ p = productZero := by
  simp [coneEnergy, add_eq_zero_iff_of_nonneg, vectorSq_nonneg, frobSq_nonneg, vectorSq_eq_zero_iff,
    frobSq_eq_zero_iff, productZero, coneZero, Prod.ext_iff, Subtype.ext_iff]

end

theorem planeEnergy_smul (t : ℝ) (p : PlaneSpace ι) :
    planeEnergy (t • p) = t^2 * planeEnergy p := by
  simp [planeEnergy, vectorSq, planeSq, mul_pow, ← Finset.mul_sum]
  ring

theorem continuous_planeEnergy : Continuous (@planeEnergy ι _) := by
  unfold planeEnergy vectorSq planeSq
  fun_prop

theorem continuous_coneEnergy : Continuous (@coneEnergy ι κ _ _ _) := by
  have := continuous_frobSq (ι := Fin 2) (κ := κ)
  unfold coneEnergy vectorSq
  fun_prop

def productRetraction (p : ConeSpace ι κ) : PlaneSpace ι := (p.1, coneToPlane p.2)

def productSection (d : ℕ) (p : PlaneSpace ι) : ConeSpace ι (Fin (d+2)) :=
  (p.1, planeToCone d p.2)

theorem continuous_productRetraction : Continuous (@productRetraction ι κ _ _) :=
  continuous_fst.prodMk (continuous_coneToPlane.comp continuous_snd)

section
variable (d : ℕ)
theorem continuous_productSection : Continuous (@productSection ι d) :=
  continuous_fst.prodMk ((continuous_planeToCone d).comp continuous_snd)

@[simp] theorem productRetraction_section (p : PlaneSpace ι) :
    productRetraction (productSection d p) = p :=
  Prod.ext rfl (coneToPlane_planeToCone d p.2)

@[simp] theorem productSection_zero :
    productSection d (0 : PlaneSpace ι) = productZero :=
  Prod.ext rfl (planeToCone_zero d)

end

theorem productRetraction_energy (p : ConeSpace ι κ) :
    planeEnergy (productRetraction p) = coneEnergy p := by
  simp [productRetraction, planeEnergy, coneEnergy, coneToPlane_sq]

theorem productSection_energy (d : ℕ) (p : PlaneSpace ι) :
    coneEnergy (productSection d p) = planeEnergy p := by
  simp [productSection, planeEnergy, coneEnergy, planeToCone_sq]

abbrev PlaneSphere (ι : Type*) [Fintype ι] := {p : PlaneSpace ι // planeEnergy p = 1}
abbrev PuncturedProduct (ι κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {p : ConeSpace ι κ // p ≠ productZero}

section
variable (p : ConeSpace ι κ)
def productRadius : ℝ := Real.sqrt (coneEnergy p)

theorem productRadius_sq : productRadius p ^ 2 = coneEnergy p :=
  Real.sq_sqrt (coneEnergy_nonneg p)

end

theorem productRadius_pos (p : PuncturedProduct ι κ) : 0 < productRadius p.val :=
  Real.sqrt_pos.mpr ((coneEnergy_nonneg _).lt_of_ne fun h => p.2 ((coneEnergy_eq_zero_iff _).mp h.symm))

theorem continuous_productRadius : Continuous (@productRadius ι κ _ _ _) :=
  Real.continuous_sqrt.comp continuous_coneEnergy

/-- Defined on the puncture at the single marked point, including points (x,0). -/
def sphereProjection (p : PuncturedProduct ι κ) : PlaneSphere ι :=
  ⟨(productRadius p.val)⁻¹ • productRetraction p.val, by
    rw [planeEnergy_smul, productRetraction_energy, ← productRadius_sq]
    have hn := ne_of_gt (productRadius_pos p)
    grind⟩

theorem continuous_sphereProjection : Continuous (@sphereProjection ι κ _ _ _) :=
  (((continuous_productRadius.comp continuous_subtype_val).inv₀
    (fun p => (productRadius_pos p).ne')).smul
    (continuous_productRetraction.comp continuous_subtype_val)).subtype_mk _

/-- A sphere of arbitrary positive radius in the full cone product. -/
def smallSphereSection (d : ℕ) (t : ℝ) (ht : 0 < t) (v : PlaneSphere ι) :
    PuncturedProduct ι (Fin (d+2)) :=
  ⟨productSection d (t • v.val), fun hz => by
    have he := (coneEnergy_eq_zero_iff _).mpr hz
    rw [productSection_energy, planeEnergy_smul, v.property, mul_one] at he
    nlinarith⟩

section
variable (d : ℕ) (t : ℝ) (ht : 0<t)

theorem continuous_smallSphereSection :
    Continuous (@smallSphereSection ι _ d t ht) :=
  ((continuous_productSection d).comp (continuous_subtype_val.const_smul t)).subtype_mk _

/-- This split identity is the input for the ordinary homology obstruction. -/
theorem sphereProjection_smallSphereSection (v : PlaneSphere ι) : sphereProjection (smallSphereSection d t ht v) = v := by
  have : productRadius (productSection d (t • v.val)) = t := by
    simp [productRadius, productSection_energy, planeEnergy_smul, v.property, ht.le]
  apply Subtype.ext
  simp [sphereProjection, smallSphereSection, this, smul_smul, ht.ne']

end

end GS.NonmanifoldObstruction
