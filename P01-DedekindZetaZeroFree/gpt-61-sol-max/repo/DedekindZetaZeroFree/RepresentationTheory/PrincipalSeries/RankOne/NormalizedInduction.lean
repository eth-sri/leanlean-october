module

public import Mathlib

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CoveredBorelRetractionAndInduction

@[expose] public section


noncomputable section

set_option maxHeartbeats 1200000

namespace DedekindZetaZeroFree.KPRankOneInduction

open scoped Topology NNReal Matrix OnePoint Classical
open IsDedekindDomain NumberField MeasureTheory

variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))

abbrev LocalField := v.adicCompletion F
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (LocalField F v)
abbrev PGL2 := Matrix.ProjGenLinGroup (Fin 2) (LocalField F v)

instance pglTopology : TopologicalSpace (PGL2 F v) := by
  unfold PGL2 Matrix.ProjGenLinGroup
  infer_instance








def upperBorel : Subgroup (PGL2 F v) where
  carrier := {g | ∃ A : GL2 F v, Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 = 0}
  one_mem' := (KPRankOneInductionRaw.upperBorel F v).one_mem
  mul_mem' := (KPRankOneInductionRaw.upperBorel F v).mul_mem
  inv_mem' := (KPRankOneInductionRaw.upperBorel F v).inv_mem

def diagonalTorus : Subgroup (PGL2 F v) where
  carrier := {g | ∃ A : GL2 F v,
    Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 = 0 ∧ A 0 1 = 0}
  one_mem' := (KPRankOneInductionRaw.diagonalTorus F v).one_mem
  mul_mem' := (KPRankOneInductionRaw.diagonalTorus F v).mul_mem
  inv_mem' := (KPRankOneInductionRaw.diagonalTorus F v).inv_mem

def borelRatio : upperBorel F v →* (LocalField F v)ˣ where
  toFun b :=
    let A := Classical.choose b.property
    Units.mk0 (A 0 0 / A 1 1) (Units.ne_zero (KPRankOneInductionRaw.borelRatio F v b))
  map_one' := (KPRankOneInductionRaw.borelRatio F v).map_one
  map_mul' := (KPRankOneInductionRaw.borelRatio F v).map_mul

theorem borelRatio_eq (b : upperBorel F v) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = b.val) (hupper : A 1 0 = 0) :
    (borelRatio F v b : LocalField F v) = A 0 0 / A 1 1 :=
  KPRankOneInductionRaw.borelRatio_eq F v b A hA hupper

def localAbs : (LocalField F v)ˣ →* (ℝ≥0)ˣ where
  toFun y := Units.mk0 ‖(y : LocalField F v)‖₊ (Units.ne_zero (KPRankOneInductionRaw.localAbs F v y))
  map_one' := (KPRankOneInductionRaw.localAbs F v).map_one
  map_mul' := (KPRankOneInductionRaw.localAbs F v).map_mul

def ordinaryDelta  :=
  (localAbs F v).comp (borelRatio F v)

def diagonalMatrix (y : (LocalField F v)ˣ) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(y : LocalField F v), 0; 0, 1] (by apply KPRankOneInductionRaw.diagonalMatrix_det_ne_zero)

def upperRootMatrix (x : LocalField F v) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by apply KPRankOneInductionRaw.upperRootMatrix_det_ne_zero)

def diagonalElement (y : (LocalField F v)ˣ)  :=
  Matrix.ProjGenLinGroup.mk (diagonalMatrix F v y)

def upperRootElement (x : LocalField F v) : PGL2 F v :=
  Matrix.ProjGenLinGroup.mk (upperRootMatrix F v x)

theorem diagonalElement_mem (y : (LocalField F v)ˣ) :
    diagonalElement F v y ∈ upperBorel F v :=
  KPRankOneInductionRaw.diagonalElement_mem F v y

theorem upperRootElement_mem (x : LocalField F v) :
    upperRootElement F v x ∈ upperBorel F v :=
  KPRankOneInductionRaw.upperRootElement_mem F v x

def halfModulus {B : Type*} [Group B] (δ : B →* (ℝ≥0)ˣ) : B →* (ℝ≥0)ˣ where
  toFun b := Units.mk0 (NNReal.sqrt (δ b : ℝ≥0)) (Units.ne_zero (KPRankOneInductionRaw.halfModulus δ b))
  map_one' := (KPRankOneInductionRaw.halfModulus δ).map_one
  map_mul' := (KPRankOneInductionRaw.halfModulus δ).map_mul

theorem halfModulus_eq {B : Type*} [Group B] (δ : B →* (ℝ≥0)ˣ) (b : B) :
    ((halfModulus δ b : ℝ≥0) : ℝ) = Real.sqrt ((δ b : ℝ≥0) : ℝ) :=
  KPRankOneInductionRaw.halfModulus_eq δ b

section CoverProjection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (π : G →* PGL2 F v)

def coveredBorel  := (upperBorel F v).comap π

def coveredTorus  := (diagonalTorus F v).comap π

def borelProjection  :=
  (π.comp (coveredBorel F v π).subtype).codRestrict (upperBorel F v) (fun b => b.property)

def deltaB  :=
  (ordinaryDelta F v).comp (borelProjection F v π)

def dB : coveredBorel F v π →* (ℝ≥0)ˣ := halfModulus (deltaB F v π)

theorem deltaB_eq (b : coveredBorel F v π) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = π b.val) (hupper : A 1 0 = 0) :
    ((deltaB F v π b : ℝ≥0) : ℝ) = ‖A 0 0 / A 1 1‖ :=
  KPRankOneInductionRaw.deltaB_eq F v π b A hA hupper

theorem dB_locallyConstant (hπ : Continuous π) :
    IsLocallyConstant (dB F v π) :=
  KPRankOneInductionRaw.dB_locallyConstant F v π hπ

theorem deltaB_upperRoot (x : LocalField F v) (b : coveredBorel F v π)
    (hb : π b.val = upperRootElement F v x) : deltaB F v π b = 1 :=
  KPRankOneInductionRaw.deltaB_upperRoot F v π x b hb

theorem coveredBorel_closed (hπ : Continuous π) :
    IsClosed (coveredBorel F v π : Set G) :=
  KPRankOneInductionRaw.coveredBorel_closed F v π hπ

theorem coveredFlag_compact (hπ : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) :
    IsCompact (Set.univ : Set (SectionCosetSpace (coveredBorel F v π))) :=
  KPRankOneInductionRaw.coveredFlag_compact F v π hπ hopen hsurj

def ordinaryUpperRootHom : Multiplicative (LocalField F v) →* PGL2 F v where
  toFun x := upperRootElement F v (Multiplicative.toAdd x)
  map_one' := (KPRankOneInductionRaw.ordinaryUpperRootHom F v).map_one
  map_mul' := (KPRankOneInductionRaw.ordinaryUpperRootHom F v).map_mul

def coveredUpperRoot (n : Multiplicative (LocalField F v) →* G)  := n.range

theorem coveredTorus_le_Borel : coveredTorus F v π ≤ coveredBorel F v π :=
  KPRankOneInductionRaw.coveredTorus_le_Borel F v π

theorem rootLift_mem_Borel (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (x : Multiplicative (LocalField F v)) : n x ∈ coveredBorel F v π :=
  KPRankOneInductionRaw.rootLift_mem_Borel F v π n hn x

theorem exists_canonicalBorelRetraction [Finite π.ker]
    (hcentral : π.ker ≤ Subgroup.center G)
    (hπ : Function.Surjective π) (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x) :
    ∃ q : coveredBorel F v π →* coveredTorus F v π,
      (∀ h : coveredTorus F v π,
        q ⟨h.val, coveredTorus_le_Borel F v π h.property⟩ = h) ∧
      (∀ x : Multiplicative (LocalField F v),
        q ⟨n x, rootLift_mem_Borel F v π n hn x⟩ = 1) ∧
      (∀ b : coveredBorel F v π,
        b.val * (q b : G)⁻¹ ∈ coveredUpperRoot F v n) :=
  KPRankOneInductionRaw.exists_canonicalBorelRetraction F v π hcentral hπ n hn

end CoverProjection

section PrincipalSeries

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup E] [Module ℂ E] (π : G →* PGL2 F v)
    (q : coveredBorel F v π →* coveredTorus F v π)
    (τ : Representation ℂ (coveredTorus F v π) E)

def inflatedTorusRepresentation  := τ.comp q

end PrincipalSeries

end DedekindZetaZeroFree.KPRankOneInduction

end
