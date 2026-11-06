module
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.Rectangle

@[expose] public section

open Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E}

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
  DifferentiableOn ℂ f s
