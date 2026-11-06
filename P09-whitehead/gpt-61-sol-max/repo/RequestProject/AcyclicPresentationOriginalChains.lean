import Mathlib.Tactic

import RequestProject.AcyclicPresentationActualChains
import RequestProject.PresWordDiskTopologicalChains
import RequestProject.PresAcyclicExponentMatrix
import RequestProject.TopologicalSingular.MathlibComparison

/-! The actual algebraic acyclic-core construction yields chains in the
literal original CW complex. Acyclicity of the original space and its actual
word-disk homotopy equivalence supply the exponent-boundary isomorphism;
the final theorems have no independent matrix hypothesis. -/

noncomputable section
namespace FiniteChains.RelativeNormalForm
open PresModel


variable {A C : Type} [dA : DecidableEq A] (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

include hcore in
theorem actual_hasOriginalFiniteChain [Finite A] [Finite C]
    (K : Whitehead.TwoComplex) (hK : Whitehead.FiniteCells K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) true := by
  have hd : dA = Classical.decEq A := Subsingleton.elim _ _
  subst dA
  let c := actualAmbientChain core hcore n
  apply (c.toPresChainFS hcore.1).hasOriginalTopologicalChain K a e₀ c.chain_proper true
  intro _
  have h := actualAmbientChain_finite core hcore n
  letI  := h.1
  letI  := h.2
  change Whitehead.FiniteCells K ∧ Finite (A ⊕ c.extraGen) ∧
    Finite (C ⊕ {s // c.stage n s})
  exact ⟨hK, inferInstance, inferInstance⟩

/-- Transport the original singular acyclicity through the actual disk-model
comparison and extract the original presentation's exponent isomorphism. -/
abbrev actual_expMatrix_bijective_of_acyclic
    (K : Whitehead.TwoComplex) (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)  :=
  let e :=
    (FiniteChains.PresModel.presClassicalDiskComparison (FiniteChains.PresModel.presCanonicalWords core a)
          (FiniteChains.PresModel.presCanonicalWords_ne_nil core a)).trans
      e₀;
  have hmodel := (Whitehead.acyclic_iff_of_homotopyEquiv e).mpr hK;
  FiniteChains.PresModel.expMatrix_bijective_of_presRealization_acyclic core
    (FiniteChains.PresModel.presCanonicalWords core a) (FiniteChains.PresModel.mk_presCanonicalWords core a)
    (FiniteChains.PresModel.presCanonicalWords_positive core a) hmodel

/-- The finite original-cell version also derives its matrix premise from
actual singular acyclicity; finiteness is used only for the finite conclusion. -/
abbrev actual_hasOriginalFiniteChain_of_acyclic [Finite A] [Finite C]
    (K : Whitehead.TwoComplex) (hfinite : Whitehead.FiniteCells K)
    (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ)  :=
  FiniteChains.RelativeNormalForm.actual_hasOriginalFiniteChain core
    (FiniteChains.RelativeNormalForm.actual_expMatrix_bijective_of_acyclic core K hK a e₀) K hfinite a e₀ n

end FiniteChains.RelativeNormalForm
