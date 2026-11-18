module

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar

open scoped BigOperators

namespace AnalyticBridge

variable {Ω : Type*}

structure CRTChoice where
  J : ℕ
  C : ℕ
  e : ℕ
  v : ℕ
  s : ℕ
  J2 : ℕ
  b1 : ℕ
  b2 : ℕ
  A1 : ℕ
  A2 : ℕ
  d : ℕ
  kpp : ℕ
  deriving DecidableEq

end AnalyticBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ExpBound

end ExpBound

namespace ShortDraftMellin

end ShortDraftMellin

end OAI
