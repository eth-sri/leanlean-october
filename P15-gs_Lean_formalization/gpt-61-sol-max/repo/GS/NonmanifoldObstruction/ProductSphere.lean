
import GS.NonmanifoldObstruction.HomogeneousRetraction



/-!
# Spherical sections in a punctured product, not just a punctured cone

The auxiliary sphere is the explicit unit sphere in (ι -> ℝ) x ℝ².
The corresponding product has the genuine rank-one cone as its last factor.
These maps do NOT delete the full singular stratum: (x,0) with x != 0
remains in the domain.
-/
noncomputable section
namespace GS.NonmanifoldObstruction

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

variable (d : ℕ)

def vectorSq (x : ι → ℝ) : ℝ := ∑ i, x i^2









abbrev PlaneSpace (ι : Type*) := (ι → ℝ) × CircleVector
abbrev ConeSpace (ι κ : Type*) [Fintype κ] [DecidableEq κ] := (ι → ℝ) × RankCone κ

def productZero : ConeSpace ι κ := (0, coneZero)















def productRetraction (p : ConeSpace ι κ) := (p.1, coneToPlane p.2)

def productSection  (p : PlaneSpace ι) := (p.1, planeToCone d p.2)

theorem continuous_productRetraction : Continuous (@productRetraction ι κ _ _) :=
  continuous_fst.prodMk (continuous_coneToPlane.comp continuous_snd)

theorem continuous_productSection  : Continuous (@productSection ι d) :=
  continuous_fst.prodMk ((continuous_planeToCone d).comp continuous_snd)

@[simp] theorem productRetraction_section  (p : PlaneSpace ι) :
    productRetraction (productSection d p) = p := Prod.ext rfl (coneToPlane_planeToCone d p.2)

@[simp] theorem productSection_zero  :
    productSection d (0 : PlaneSpace ι) = productZero := Prod.ext rfl (planeToCone_zero d)






























end GS.NonmanifoldObstruction
