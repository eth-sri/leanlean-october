/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.Topology
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Architect

@[expose] public section

universe u v

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) [Countable (Σ l, L.Relations l)]

section Generic

variable (α : Type*) [Encodable α]

instance : TopologicalSpace.IsCompletelyMetrizableSpace (StructureSpaceOn L α) := inferInstance

end Generic

instance : TopologicalSpace.IsCompletelyMetrizableSpace (StructureSpace L) := by
  unfold StructureSpace; infer_instance

end Language

end FirstOrder
