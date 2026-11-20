/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Clopen

@[expose] public section

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

instance {α : Type*} : TopologicalSpace (StructureSpaceOn L α) := Pi.topologicalSpace

/-- `StructureSpace L` inherits the product topology from `RelQuery L → Bool`.
Since `Bool` has the discrete topology, this is the product of discrete spaces. -/
instance : TopologicalSpace (StructureSpace L) := Pi.topologicalSpace

end Language

end FirstOrder
