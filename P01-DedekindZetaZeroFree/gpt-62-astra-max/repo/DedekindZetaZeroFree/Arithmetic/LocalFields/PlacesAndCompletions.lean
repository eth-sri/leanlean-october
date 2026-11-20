module

public import DedekindZetaZeroFree.Adeles.Characters.AdditiveQuotient
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped Matrix.Norms.L2Operator

universe u

abbrev KPFinitePlace (F : Type u) [Field F] [NumberField F] :=
  HeightOneSpectrum (RingOfIntegers F)

section

variable (F : Type u) [Field F] [NumberField F]

abbrev KPPlace :=
  KPFinitePlace F ⊕ InfinitePlace F

def KPCompletion : KPPlace F → Type u
  | .inl v => v.adicCompletion F
  | .inr v => v.Completion

end

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    Field (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    TopologicalSpace (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    Algebra F (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

end DedekindZetaZeroFree

end
