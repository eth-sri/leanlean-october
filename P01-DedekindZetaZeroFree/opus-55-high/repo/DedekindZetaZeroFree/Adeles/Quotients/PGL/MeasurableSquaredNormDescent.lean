module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL.DoubleQuotientTopology

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ActualQuotient

open Topology

open scoped NumberField Classical ENNReal

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance : MeasurableSpace (actualCover F ζ hζ) := borel _

instance : BorelSpace (actualCover F ζ hζ) := ⟨rfl⟩
