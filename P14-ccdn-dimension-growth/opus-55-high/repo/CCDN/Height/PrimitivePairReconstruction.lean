/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A primitive coordinate pair generates the function field over the constant
field. Every finite family of functions then has polynomial reconstruction
identities with one nonzero denominator. No bound on its degree is asserted. -/

namespace CCDN
section
open MvPolynomial

