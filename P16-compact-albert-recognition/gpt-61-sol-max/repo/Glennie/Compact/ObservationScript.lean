module
public import Glennie.Compact.Affine20.Relabel
public import Mathlib.Tactic
@[expose] public section
namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20
/-- Named Fin indices avoid compiler-generated numeral witnesses in the statement. -/
def f0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def f1 : Fin 3 := ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
def f2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩
def b0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def b1 : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩
/-- Six algebraic readings use an unnormalized input y. -/
def contrast (x y z v : Albert) : ℝ :=
  inner z (U y (U x (U z v)) - U x (U y (U z v)))
def halfAmplitude (x : Albert) : Albert :=
  (1 / (Nat.cast 2 : ℝ)) • ((1 : Albert) + x)
def delta (x y z a rho : Albert) : ℝ := contrast x y z (U a rho)
def score (T : Triple) : ℝ :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  4 * delta x y z (halfAmplitude x) y -
    delta x y z x y - delta x y z 1 y
/-- Six raw algebraic readings, in h+, h-, x+, x-, 1+, 1- order. -/
structure Readouts where
  hPlus : ℝ
  hMinus : ℝ
  xPlus : ℝ
  xMinus : ℝ
  onePlus : ℝ
  oneMinus : ℝ
def weightedScore (r : Readouts) : ℝ :=
  4 * r.hPlus - 4 * r.hMinus - r.xPlus + r.xMinus - r.onePlus + r.oneMinus

/-- The fixed twenty-coordinate affine chart of complete overlap ledgers. -/
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / (Nat.cast 3 : ℝ) + (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.2 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    centred L f0 f0 f0, centred L f0 f0 f1, centred L f0 f1 f0, centred L f0 f1 f1,
    centred L f1 f0 f0, centred L f1 f0 f1, centred L f1 f1 f0, centred L f1 f1 f1]
/-- The chart decoder uses zero-margin 2-by-2 and 2-by-2-by-2 lifts. -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i
def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 0) (v 1) (v 2) (v 3) i j
def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 4) (v 5) (v 6) (v 7) j k
def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 8) (v 9) (v 10) (v 11) k i
def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / (Nat.cast 3 : ℝ) - (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)
def wordValues {E : Type*} (e : E) (a : Fin 3 → E)
    (j : E → E → E) : Fin 27 → E :=
  let x := a f0
  let y := a f1
  let z := a f2
  let xx := j x x
  let xy := j x y
  let xz := j x z
  let yy := j y y
  let yz := j y z
  let zz := j z z
  ![e, x, y, z, xx, xy, xz, yy, yz, zz,
    j x xy, j x xz, j x yy, j x yz, j x zz,
    j y xz, j y yz, j y zz,
    j xx yy, j xx yz, j xx zz, j xy yz, j xy zz, j yy zz,
    j x (j y xz), j x (j y yz), j x (j y zz)]

def rawPlus (x y z a : Albert) : ℝ :=
  inner z (U y (U x (U z (U a y))))
def rawMinus (x y z a : Albert) : ℝ :=
  inner z (U x (U y (U z (U a y))))
def exactReadouts (T : Triple) : Readouts :=
  let x := encoder (T f0)
  let y := encoder (T f1)
  let z := encoder (T f2)
  ⟨rawPlus x y z (halfAmplitude x), rawMinus x y z (halfAmplitude x),
   rawPlus x y z x, rawMinus x y z x, rawPlus x y z 1, rawMinus x y z 1⟩
def ErrorsAtMost (noisy exact : Readouts) (ε : ℝ) : Prop :=
  |noisy.hPlus - exact.hPlus| ≤ ε ∧
  |noisy.hMinus - exact.hMinus| ≤ ε ∧
  |noisy.xPlus - exact.xPlus| ≤ ε ∧
  |noisy.xMinus - exact.xMinus| ≤ ε ∧
  |noisy.onePlus - exact.onePlus| ≤ ε ∧
  |noisy.oneMinus - exact.oneMinus| ≤ ε

def noisyPhi (r : Readouts) : ℝ := weightedScore r / (Nat.cast 2 : ℝ)

end
end Glennie.SubmissionR03

namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Triple (E : Type*) := Fin 3 → Fin 3 → E
abbrev Ledger54 := Glennie.Compact.Affine20.Ledger54
abbrev Chart := Fin 20 → ℝ
structure Frame (e : E) (t : E → ℝ) (j : E → E → E)
    (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, t (p i) = 1
  idempotent : ∀ i, j (p i) (p i) = p i
  orthogonal : ∀ i k, i ≠ k → j (p i) (p k) = 0
  sum_unit : p 0 + p 1 + p 2 = e
def encoder (p : Fin 3 → E) : E := p 2 - p 0
def pairing (t : E → ℝ) (j : E → E → E) (x y : E) : ℝ := t (j x y)
def quad (j : E → E → E) (x z : E) : E :=
  (2 : ℝ) • j x (j x z) - j (j x x) z
def phi (t : E → ℝ) (j : E → E → E) (x y z : E) : ℝ :=
  pairing t j (quad j x (quad j y z) - quad j y (quad j x z))
    (quad j z (j x y))
def ledger (t : E → ℝ) (j : E → E → E) (T : Triple E) : Ledger54 :=
  (fun i k l => t (j (j (T 0 i) (T 1 k)) (T 2 l)),
   fun i k => pairing t j (T 0 i) (T 1 k),
   fun k l => pairing t j (T 1 k) (T 2 l),
   fun l i => pairing t j (T 2 l) (T 0 i))
def power (j : E → E → E) (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then encoder p else j (encoder p) (encoder p)
def qSingle (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  pairing t j (power j (T v) 0) (power j (T v) s)
def qPair (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (v w : Fin 3) (s r : Fin 2) : ℝ :=
  pairing t j (power j (T v) s) (power j (T w) r)
def qTriple (t : E → ℝ) (j : E → E → E)
    (T : Triple E) (s r u : Fin 2) : ℝ :=
  t (j (j (power j (T 0) s) (power j (T 1) r)) (power j (T 2) u))
def q26 (t : E → ℝ) (j : E → E → E) (T : Triple E) : Fin 26 → ℝ := ![
  qSingle t j T 0 0, qSingle t j T 0 1,
  qSingle t j T 1 0, qSingle t j T 1 1,
  qSingle t j T 2 0, qSingle t j T 2 1,
  qPair t j T 0 1 0 0, qPair t j T 0 1 0 1,
  qPair t j T 0 1 1 0, qPair t j T 0 1 1 1,
  qPair t j T 1 2 0 0, qPair t j T 1 2 0 1,
  qPair t j T 1 2 1 0, qPair t j T 1 2 1 1,
  qPair t j T 2 0 0 0, qPair t j T 2 0 0 1,
  qPair t j T 2 0 1 0, qPair t j T 2 0 1 1,
  qTriple t j T 0 0 0, qTriple t j T 0 0 1,
  qTriple t j T 0 1 0, qTriple t j T 0 1 1,
  qTriple t j T 1 0 0, qTriple t j T 1 0 1,
  qTriple t j T 1 1 0, qTriple t j T 1 1 1]
def half (e x : E) : E := (1 / 2 : ℝ) • (e + x)
def contrast (t : E → ℝ) (j : E → E → E) (x y z v : E) : ℝ :=
  pairing t j z
    (quad j y (quad j x (quad j z v)) - quad j x (quad j y (quad j z v)))
def delta (t : E → ℝ) (j : E → E → E) (x y z a rho : E) : ℝ :=
  contrast t j x y z (quad j a rho)
def score (e : E) (t : E → ℝ) (j : E → E → E) (T : Triple E) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta t j x y z (half e x) y - delta t j x y z x y - delta t j x y z e y
structure Automorphism (t : E → ℝ) (j : E → E → E) where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y, equiv (j x y) = j (equiv x) (equiv y)
  map_trace : ∀ x, t (equiv x) = t x
def mapAtoms {t : E → ℝ} {j : E → E → E}
    (g : Automorphism t j) (T : Triple E) : Triple E := fun a i => g.equiv (T a i)
def orbit (t : E → ℝ) (j : E → E → E) (S : Triple E) : Set (Triple E) :=
  {T | ∃ g : Automorphism t j, mapAtoms g S = T}
def fibre54 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ ledger t j T = Glennie.SubmissionR03.decode20 b}
def fibre20 (e : E) (t : E → ℝ) (j : E → E → E) (b : Chart) : Set (Triple E) :=
  {T | (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) = b}
def SameSign (e : E) (t : E → ℝ) (j : E → E → E) (T S : Triple E) : Prop :=
  (score e t j T < 0 ∧ score e t j S < 0) ∨
    (0 < score e t j T ∧ 0 < score e t j S)
def Admitted (e : E) (t : E → ℝ) (j : E → E → E)
    (V : Set Chart) (T : Triple E) : Prop :=
  (∀ a, Frame e t j (T a)) ∧ Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V
def TwoOrbitSections (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∃ secPos secNeg : Chart → Triple E,
    ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secPos b a)) ∧
    (∀ b ∈ V, ∀ a, Frame e t j (secNeg b a)) ∧
    (∀ b ∈ V, ledger t j (secPos b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, ledger t j (secNeg b) = Glennie.SubmissionR03.decode20 b) ∧
    (∀ b ∈ V, 0 < score e t j (secPos b)) ∧
    (∀ b ∈ V, score e t j (secNeg b) < 0) ∧
    (∀ b ∈ V, fibre54 e t j b = orbit t j (secNeg b) ∪ orbit t j (secPos b)) ∧
    (∀ b ∈ V, Disjoint (orbit t j (secNeg b)) (orbit t j (secPos b))) ∧
    (∀ b ∈ V, fibre20 e t j b = fibre54 e t j b)
def ScoreComplete (e : E) (t : E → ℝ) (j : E → E → E) (V : Set Chart) : Prop :=
  ∀ T S : Triple E, (∀ a, Frame e t j (T a)) → (∀ a, Frame e t j (S a)) →
    Glennie.SubmissionR03.encode20 (ledger t j T) ∈ V →
    score e t j T ≠ 0 ∧
      ((T ∈ orbit t j S) ↔ q26 t j T = q26 t j S ∧ SameSign e t j T S)

end
end Glennie.SubmissionR04Intrinsic.Local

attribute [simp] Glennie.SubmissionR03.f0 Glennie.SubmissionR03.f1
  Glennie.SubmissionR03.f2 Glennie.SubmissionR03.b0 Glennie.SubmissionR03.b1
