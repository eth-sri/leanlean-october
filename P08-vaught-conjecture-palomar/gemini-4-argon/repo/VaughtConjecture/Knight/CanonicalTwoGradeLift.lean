/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalLowerLift
public import VaughtConjecture.Knight.CanonicalMixedOwnerLift
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice

/-! # Literal restoration without lower-value domination

Choose a maximal prescribed grade-two owner, construct the owner-capped lift,
clip its upper tail, lift the actual grade-one prescription at the owner cap,
then splice. Every lower value is restored, including distinct invisible
values and top. Only old-face lifting is supplied, never output bountifulness.
-/


