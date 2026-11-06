import RequestProject.InitialComplexFinsupp
import RequestProject.FreeGeneratorPaddingFinsupp


/-! A concrete initial ambient presentation for every acyclic core.
The added alphabet contains a free padding generator, including when the
core alphabet is empty. All core generators and relators retain their
literal `Sum.inl` labels. No ordering or finiteness of the core is assumed
by the final construction. -/

noncomputable section
open scoped Classical

namespace FiniteChains.InitialFS
open RelativeNormalForm

variable {A M : Type}

def chosenOrder (A : Type) :=
  IsWellOrder.linearOrder (@WellOrderingRel A)

abbrev ExtraGen (A : Type) := (A × Bool) ⊕ PUnit

def ExtraCell (A : Type) :=
  letI : LinearOrder A := chosenOrder A
  A ⊕ CrossY A

/-- A canonical genuinely new generator, independent of whether `A` is empty. -/
def fresh A : ExtraGen A := Sum.inr PUnit.unit


def generatorEmbedding : GenY A → A ⊕ ExtraGen A
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (Sum.inl b)

theorem generatorEmbedding_injective :
    Function.Injective (generatorEmbedding (A := A)) := by
  intro x y h
  grind [generatorEmbedding]

def baseRel (core : M → FreeGroup A) : M ⊕ ExtraCell A → FreeGroup (GenY A) :=
  letI : LinearOrder A := chosenOrder A
  relY core


def extra (core : M → FreeGroup A) : ExtraCell A → FreeGroup (A ⊕ ExtraGen A) :=
  fun c => FreeGroup.map generatorEmbedding (baseRel core (Sum.inr c))

theorem generatorEmbedding_map_core w :
    FreeGroup.map generatorEmbedding (FreeGroup.map Sum.inl w) =
      FreeGroup.map (Sum.inl (β := ExtraGen A)) w := by
  have h : (FreeGroup.map generatorEmbedding).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (Sum.inl (β := ExtraGen A)) := by
    aesop
  exact congrArg (· w) h

theorem rawPresentation_eq_padding (core : M → FreeGroup A) :
    rawPresentation core (extra core) = FreePadding.rel (baseRel core) generatorEmbedding := by
  funext c
  cases c with
  | inl m => exact (generatorEmbedding_map_core _).symm
  | inr c => rfl

theorem baseRel_isCockcroft (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) : FSIsCockcroft (baseRel core) := by
  letI : LinearOrder A := chosenOrder A
  letI : DecidableEq A := Classical.decEq A
  exact fsIsCockcroft_relY_of_expMatrix_bijective core hcore

theorem baseRel_core_trivial (core : M → FreeGroup A)
    (hcore : Function.Surjective (expMatrix core)) a :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (baseRel core)) = 1 := by
  letI : LinearOrder A := chosenOrder A
  exact xEl_eq_one (r := core) (expSurjective_of_expMatrix_surjective core hcore) a

/-- The explicit initial pair is Cockcroft for arbitrary supported core
chains. The extra free generator preserves Cockcroftness by the actual
free-padding structural map and its proved generation theorem. -/
theorem isCockcroft (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) :
    FSIsCockcroft (rawPresentation core (extra core)) := by
  rw [rawPresentation_eq_padding]
  exact fsIsCockcroft_of_generates
    _
    (FreePadding.structuralMap_generates _ generatorEmbedding generatorEmbedding_injective)
    (baseRel_isCockcroft core hcore)

/-- The original core maps trivially into the actual padded initial group. -/
theorem core_trivial (core : M → FreeGroup A)
    (hcore : Function.Surjective (expMatrix core)) a :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (extra core))) = 1 := by
  rw [rawPresentation_eq_padding]
  have h := congrArg (FreePadding.groupHom (baseRel core) generatorEmbedding)
    (baseRel_core_trivial core hcore a)
  tauto
