module
import Mathlib

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Basic definitions

This module contains the definitions mentioned in the blueprint's Basic notation chapter
(`notation-chapter`).

When a blueprint convention already has a standard Mathlib representation,
prefer using that representation directly, for example:
-the notation `e(θ)` is `𝐞 θ` after `open scoped FourierTransform`;
-for indicator functions, use `Set.indicator`;
-for suprema and infima, including those of empty sets, use Mathlib's `sSup` and `sInf`;
-for finite cardinalities use `Finset.card`;
-/

@[expose] public section

namespace Expdb




