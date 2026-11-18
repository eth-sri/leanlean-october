module

public import DedekindZetaZeroFree.Adeles.Lattices.PGL.SteinitzClassObstruction

@[expose] public section

open scoped Pointwise

namespace DedekindZetaZeroFree

namespace KPFiniteComponents

abbrev FiniteAdeles (F : Type*) [Field F] [NumberField F] :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

abbrev FinitePGL2 (F : Type*) [Field F] [NumberField F] :=
  Matrix.ProjGenLinGroup (Fin 2) (FiniteAdeles F)

noncomputable instance (F : Type*) [Field F] [NumberField F] :
    TopologicalSpace (FinitePGL2 F) := by
  unfold FinitePGL2 Matrix.ProjGenLinGroup
  infer_instance

end KPFiniteComponents

end DedekindZetaZeroFree

section

open scoped Pointwise

namespace DedekindZetaZeroFree
namespace KPFiniteComponents

abbrev RationalPGL2 (F : Type*) [Field F] := Matrix.ProjGenLinGroup (Fin 2) F

noncomputable def diagonal (F : Type*) [Field F] [NumberField F] :
    RationalPGL2 F →* FinitePGL2 F :=
  Matrix.ProjGenLinGroup.map (algebraMap F (FiniteAdeles F))

def integralLattice (F : Type*) [Field F] [NumberField F] :
    Set (Matrix (Fin 2) (Fin 1) (FiniteAdeles F)) :=
  {x | ∀ i j v, x i j v ∈ v.adicCompletionIntegers F}

noncomputable def integralCompact (F : Type*) [Field F] [NumberField F] :
    Subgroup (FinitePGL2 F) :=
  (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeles F))
    (integralLattice F)).map Matrix.ProjGenLinGroup.mk

def idealLattice (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Set (Matrix (Fin 2) (Fin 1) F) :=
  {x | (∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = x 0 0) ∧ x 1 0 ∈ I}

noncomputable def projectiveIdealAut (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Subgroup (RationalPGL2 F) :=
  (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) F)
    (idealLattice F I)).map Matrix.ProjGenLinGroup.mk

noncomputable def arithmeticStabilizer (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (FinitePGL2 F)) (g : FinitePGL2 F) :
    Subgroup (RationalPGL2 F) :=
  (U.map (MulAut.conj g).toMonoidHom).comap (diagonal F)

end KPFiniteComponents

theorem kp_cusp_finite_adelic_components
    (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F))) :
    Finite (DoubleCoset.Quotient
      ((KPFiniteComponents.diagonal F).range : Set (KPFiniteComponents.FinitePGL2 F))
      (U : Set (KPFiniteComponents.FinitePGL2 F))) := by
  letI : IsTopologicalGroup (KPFiniteComponents.FinitePGL2 F) :=
    KPFiniteAdelicLatticeStabilizers.projective_topological_group F
  obtain ⟨hKcompact, hKopen⟩ :=
    (KPFiniteAdelicLatticeStabilizers.bounded_crt_lattice_and_projective_compact F).1
  exact KPFiniteAdelicLatticeStabilizers.finite_doubleCoset_at_open_level
    (KPFiniteComponents.diagonal F).range (KPFiniteComponents.integralCompact F) U
    hKcompact hKopen hUopen (KPFiniteAdelicLatticeStabilizers.projective_class_finiteness F)

theorem kp_cusp_finite_adelic_arithmetic_stabilizers
    (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
      (a : KPFiniteComponents.RationalPGL2 F), I ≠ 0 ∧
      (KPFiniteComponents.arithmeticStabilizer F U g).Commensurable
        ((KPFiniteComponents.projectiveIdealAut F I).map (MulAut.conj a).toMonoidHom) ∧
      (KPFiniteComponents.arithmeticStabilizer F
        (U ⊓ KPFiniteComponents.integralCompact F) g).Commensurable
        ((KPFiniteComponents.projectiveIdealAut F I).map (MulAut.conj a).toMonoidHom) := by
  obtain ⟨I, a, hI, hstandard⟩ :=
    KPFiniteAdelicLatticeStabilizers.standard_stabilizer_class_obstruction F g
  obtain ⟨hlevel, hintersection⟩ :=
    KPFiniteAdelicLatticeStabilizers.level_stabilizers_commensurable_standard F U hUcompact hUopen g
  exact ⟨I, a, hI, hlevel.trans hstandard, hintersection.trans hstandard⟩

namespace KPFiniteComponentCover
variable {C G R : Type*} [Group C] [Group G] [Group R]
variable (π : C →* G) (s : R →* C) (d : R →* G) (hs : π.comp s = d)
variable (U : Subgroup C)

end KPFiniteComponentCover

end DedekindZetaZeroFree

end
