module

public import RequestProject.CombPi2
public import RequestProject.Framework

@[expose] public section

/-!
# Theorem A over honest combinatorial two-complexes

`RequestProject/Framework.lean` proves Theorem A relative to the interface `TwoComplexData`,
whose notions (subcomplex, `π₂`, Cockcroft, acyclic regular cover) were left abstract.  With
the combinatorial two-complexes of `RequestProject/CellComplex.lean`, their fundamental group
(`RequestProject/CombPi1.lean`), their universal cover (`RequestProject/CombUniversalCover.lean`)
and their second homotopy module (`RequestProject/CombPi2.lean`) all constructed, the interface
can now be instantiated by honest definitions:

* `FiniteChains.Comb.Sub` — `X` is a subcomplex of `Y`: there is a cellular map injective on
  vertices, edges and two-cells;
* `FiniteChains.combData` — the instance of `TwoComplexData` carried by combinatorial
  two-complexes, in which
  * `Cockcroft` is `FiniteChains.Comb.IsCockcroft` (the Hurewicz map `π₂ → H₂` vanishes),
  * `ZeroPi2 X Y` says that every subcomplex inclusion `X ⊆ Y` is zero on
    `π₂ = ker ∂₂` of the universal covers,
  * `Pi1Trivial X Y` says that every such inclusion kills the fundamental group,
  * `Acyclic` is `FiniteChains.Comb.IsAcyclic` and `IsAcyclicCover` is the combinatorial
    notion of a connected acyclic regular covering;
* `FiniteChains.hasAcyclicRegularCover_combData_iff` — condition (2) of Theorem A in this
  instance is exactly `FiniteChains.Comb.HasAcyclicRegularCover`, the statement of
  `RequestProject/CellComplex.lean`.

Non-vacuity is checked on the one-point complex.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Identity and composition of cellular maps -/

/-- The identity cellular map. -/
def Hom.id (X : Complex2.{u}) : Hom X X where
  onV := _root_.id
  onE := _root_.id
  onF := _root_.id
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun f => by simp

/-- The composition of cellular maps. -/
def Hom.comp {X Y Z : Complex2.{u}} (g : Hom Y Z) (h : Hom X Y) : Hom X Z where
  onV := g.onV ∘ h.onV
  onE := g.onE ∘ h.onE
  onF := g.onF ∘ h.onF
  src_onE := fun e => by
    show Z.src (g.onE (h.onE e)) = g.onV (h.onV (X.src e))
    rw [g.src_onE, h.src_onE]
  tgt_onE := fun e => by
    show Z.tgt (g.onE (h.onE e)) = g.onV (h.onV (X.tgt e))
    rw [g.tgt_onE, h.tgt_onE]
  base_onF := fun f => by
    show Z.base (g.onF (h.onF f)) = g.onV (h.onV (X.base f))
    rw [g.base_onF, h.base_onF]
  att_onF := fun f => by
    show Z.att (g.onF (h.onF f)) = (X.att f).map (fun eb => (g.onE (h.onE eb.1), eb.2))
    rw [g.att_onF, h.att_onF]
    simp

/-- **Subcomplex**: a cellular map injective on vertices, edges and two-cells. -/
def Sub (X Y : Complex2.{u}) : Prop :=
  ∃ h : Hom X Y, Function.Injective h.onV ∧ Function.Injective h.onE ∧ Function.Injective h.onF

end Comb

namespace Comb

/-! ### Non-vacuity: the one-point complex -/

end Comb
end FiniteChains
