module

public import RequestProject.InitialPairFinsupp
public import RequestProject.RelativeAmbientPresChain

@[expose] public section

/-! The acyclic-core sufficiency construction with its explicit initial
pair, actual genus replacement, actual terminal extension, and actual
topological presentation realization all supplied. Unverified source. -/

noncomputable section
open scoped Classical

namespace FiniteChains

theorem FSIsCockcroft.redecide {A J : Type} [dA : DecidableEq A]
    {ρ : J → FreeGroup A} (h : FSIsCockcroft ρ) (dA' : DecidableEq A) :
    @FSIsCockcroft A J dA' ρ := by
  have hd : dA' = dA := Subsingleton.elim _ _
  subst dA'
  exact h

end FiniteChains

namespace FiniteChains.RelativeNormalForm
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

def actualInitial : AmbientChain core 0 := by
  refine AmbientChain.initial (core := core) (InitialFS.fresh A) (InitialFS.extra core)
    ?_ (InitialFS.core_trivial core hcore.2)
  exact @FSIsCockcroft.redecide _ _ _ _ (InitialFS.isCockcroft core hcore) _

def actualAmbientChain (n : ℕ) : AmbientChain core n :=
  ambientChains core hcore (actualInitial core hcore) n

theorem actualAmbientChain_finite [Finite A] (n : ℕ) :
    Finite (actualAmbientChain core hcore n).extraGen ∧
      Finite (actualAmbientChain core hcore n).extraCell := by
  induction n with
  | zero =>
      change Finite (InitialFS.ExtraGen A) ∧ Finite (InitialFS.ExtraCell A)
      constructor
      · infer_instance
      · unfold InitialFS.ExtraCell
        infer_instance
  | succ n ih =>
      letI := ih.1
      letI := ih.2
      change Finite (NextExtraGen core hcore.2 (actualAmbientChain core hcore n).rel) ∧
        Finite (NextExtraCell core hcore.2 (actualAmbientChain core hcore n).rel)
      constructor <;> infer_instance
