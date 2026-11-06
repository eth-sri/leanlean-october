/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EndStatement
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Further statements of the paper

Statements of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse
Lopsided Graphs» (Josh Alman, Virginia Vassilevska Williams) beyond the five claims of
`EndStatement.lean`, each as a proposition, with the definitions that they use; and statements that
the notions which this file and `EndStatement.lean` both define agree. The file imports
`EndStatement.lean` and Mathlib. It proves none of the statements: the proofs are in the library,
the folder `ThreeSumApsp/`. The five claims do not depend on this file: it is for a reader who wants
to believe a further lemma, equation, table or theorem of the paper.

`Challenge/PaperStatements.lean` states that the propositions hold: `PaperStatements.lemma_6` says
that `PaperStatements.Lemma_6` holds, and `ThreeSumApsp.wordRam_theorem_5` that the running-time
sentence `ThreeSumApsp.WordRam.Items.Theorem_5` holds.

The parts, in this order:

* Section 2: definitions
* Section 2: statements
* Section 3: definitions
* The reduction of Chan and He: definitions
* Section 3: statements
* Section 4: definitions
* Section 4: statements
* Section 5: definitions
* Section 5: statements
* The word RAM: problems
* Agreement with the definitions of EndStatement.lean
* The word RAM: running times

In a comment, "this part" means the part in which the comment stands.
-/

@[expose] public section

/-!
## Section 2: definitions

Definitions used by the statements of Section 2, "Quickly computing certain entries of a thin matrix
product".  They follow the paper's order and names.  Only what the statements need, directly or
through another definition, is defined here; the other notions of the section, among them the tiling
of Section 2.3.4, are defined with the proofs.

Conventions used throughout.

* The paper numbers indices from 1; Lean's `Fin n` starts at 0.  So the paper's `x₁, x₂, x₃` are
  `LeftVar.x 0, LeftVar.x 1, LeftVar.x 2`, the paper's `p₂₁` is `LeftVar.p 1 0`, and so on.
* A string of length `L` over an alphabet `α` is a function `Fin L → α`.  The paper's level
  `ℓ ∈ {1, …, L}` is the element `ℓ - 1` of `Fin L`; the order of the levels is the order of
  `Fin L`.
* The string `s u'` (the variable `s` followed by the string `u'`) is `Fin.cons s u'`; the first
  variable of `u` is `u 0` and the rest of it is `Fin.tail u`.  The empty string is `Fin.elim0`.
* A linear form is given by the vector of its coefficients: a linear form in the left variables is a
  function `LeftVar → ℤ`.  `Pi.single s 1` is the form consisting of the single variable `s`.
-/

section Sec2Definitions

open Finset

namespace ThreeSumApsp

/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/

/-- Section 2.2: "We call x₁, x₂, x₃, p₁₁, p₁₂, p₂₁, p₂₂ the seven left variables". -/
inductive LeftVar : Type
  | x (i : Fin 3)
  | p (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: "and y₁, y₂, y₃, q₁₁, q₁₂, q₂₁, q₂₂ the seven right variables". -/
inductive RightVar : Type
  | y (j : Fin 3)
  | q (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: "We will also use ten output variables z_ij (for 1 ≤ i, j ≤ 3) and z₀". -/
inductive OutVar : Type
  | z (i j : Fin 3)
  | z0
  deriving DecidableEq, Fintype

/-- Section 2.2: "Schönhage's identity has ten terms, which we name P_ij (for 1 ≤ i, j ≤ 3,
corresponding to the entries of p̂ and q̂) and P₀". -/
inductive Term : Type
  | P (i j : Fin 3)
  | P0
  deriving DecidableEq, Fintype

/-- The linear form consisting of the single left variable `x_i`. -/
def xForm (i : Fin 3) : LeftVar → ℤ := Pi.single (LeftVar.x i) 1
/-- The linear form consisting of the single left variable `p_ij`. -/
def pForm (i j : Fin 2) : LeftVar → ℤ := Pi.single (LeftVar.p i j) 1
/-- The linear form consisting of the single right variable `y_j`. -/
def yForm (j : Fin 3) : RightVar → ℤ := Pi.single (RightVar.y j) 1
/-- The linear form consisting of the single right variable `q_ij`. -/
def qForm (i j : Fin 2) : RightVar → ℤ := Pi.single (RightVar.q i j) 1
/-- The linear form consisting of the single output variable `z_ij`. -/
def zForm (i j : Fin 3) : OutVar → ℤ := Pi.single (OutVar.z i j) 1
/-- The linear form consisting of the single output variable `z₀`. -/
def z0Form : OutVar → ℤ := Pi.single OutVar.z0 1

/-- Section 2.2: the 3 × 3 matrix `p̂` of linear forms,
"p̂ = (p₁₁, p₁₂, 0; p₂₁, p₂₂, 0; -p₁₁-p₂₁, -p₁₂-p₂₂, 0)". -/
def pHat : Matrix (Fin 3) (Fin 3) (LeftVar → ℤ) :=
  !![pForm 0 0, pForm 0 1, 0;
     pForm 1 0, pForm 1 1, 0;
     -pForm 0 0 - pForm 1 0, -pForm 0 1 - pForm 1 1, 0]

/-- Section 2.2: the 3 × 3 matrix `q̂` of linear forms,
"q̂ = (q₁₁, q₁₂, -q₁₁-q₁₂; q₂₁, q₂₂, -q₂₁-q₂₂; 0, 0, 0)". -/
def qHat : Matrix (Fin 3) (Fin 3) (RightVar → ℤ) :=
  !![qForm 0 0, qForm 0 1, -qForm 0 0 - qForm 0 1;
     qForm 1 0, qForm 1 1, -qForm 1 0 - qForm 1 1;
     0, 0, 0]

/-- Section 2.2: the linear form `φ_λ` in the left variables,
"φ_{P_ij} = x_i + p̂_ij" and "φ_{P₀} = -(x₁ + x₂ + x₃)".
Section 2.3.1: "let φ_λ(s) ∈ {0, ±1} denote the coefficient of s in φ_λ"; this is `phi lam s`. -/
def phi : Term → LeftVar → ℤ
  | .P i j => xForm i + pHat i j
  | .P0 => -(xForm 0 + xForm 1 + xForm 2)

/-- Section 2.2: the linear form `ψ_λ` in the right variables,
"ψ_{P_ij} = y_j + q̂_ij" and "ψ_{P₀} = y₁ + y₂ + y₃".
Section 2.3.1: `ψ_λ(t)`, the coefficient of `t` in `ψ_λ`, is `psi lam t`. -/
def psi : Term → RightVar → ℤ
  | .P i j => yForm j + qHat i j
  | .P0 => yForm 0 + yForm 1 + yForm 2

/-- Section 2.2: the linear form `χ_λ` in the output variables,
"χ_{P_ij} = z_ij + z₀" and "χ_{P₀} = z₀". -/
def chi : Term → OutVar → ℤ
  | .P i j => zForm i j + z0Form
  | .P0 => z0Form

/-- Section 2.2: "We call the variables of the inner product, p, q, and z₀, inner". -/
def LeftVar.IsInner : LeftVar → Prop
  | .x _ => False
  | .p _ _ => True
/-- Section 2.2: the right variables `q` are inner, the `y` are outer. -/
def RightVar.IsInner : RightVar → Prop
  | .y _ => False
  | .q _ _ => True
/-- Section 2.2: the output variable `z₀` is inner, the `z_ij` are outer. -/
def OutVar.IsInner : OutVar → Prop
  | .z _ _ => False
  | .z0 => True

instance LeftVar.instDecidablePredIsInner : DecidablePred LeftVar.IsInner
  | .x _ => isFalse fun h => h
  | .p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred RightVar.IsInner
  | .y _ => isFalse fun h => h
  | .q _ _ => isTrue trivial
instance OutVar.instDecidablePredIsInner : DecidablePred OutVar.IsInner
  | .z _ _ => isFalse fun h => h
  | .z0 => isTrue trivial

/-- Section 2.2: "We say that a term λ contributes to an output variable z if z appears in χ_λ." -/
def Term.Contributes (lam : Term) (z : OutVar) : Prop := chi lam z ≠ 0

instance Term.instDecidableContributes (lam : Term) (z : OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (chi lam z ≠ 0))

/-! ### 2.3.1 The recursion -/

/-- Section 2.3.1: "A left string of length L is a string u = u₁ u₂ ⋯ u_L of L left variables, and
we call u_ℓ its variable at level ℓ." -/
abbrev LeftStr (L : ℕ) : Type := Fin L → LeftVar
/-- Section 2.3.1: right strings of length `L`. -/
abbrev RightStr (L : ℕ) : Type := Fin L → RightVar
/-- Section 2.3.1: output strings of length `L`. -/
abbrev OutStr (L : ℕ) : Type := Fin L → OutVar
/-- Section 2.3.1: "We refer to the call reached by choosing the terms τ₁, …, τ_k at levels 1, …, k
as the vertex τ₁ ⋯ τ_k, a string of k terms. It is at depth k". -/
abbrev Vertex (k : ℕ) : Type := Fin k → Term
/-- Section 2.3.1: "the leaves, the vertices τ = τ₁ ⋯ τ_L at depth L". -/
abbrev Leaf (L : ℕ) : Type := Vertex L

/-- Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u
that is a left string of length L."  So such an array is a function `LeftStr L → ℤ`, and likewise
for right strings, output strings and leaves.

"the slice of a at a left variable s is the array a_s on the strings of length L - 1 given by
a_s[u'] := a[s u']"; the same definition is used for every alphabet. -/
def sliceAt {α β : Type} {L : ℕ} (a : (Fin (L + 1) → α) → β) (s : α) : (Fin L → α) → β :=
  fun u' => a (Fin.cons s u')

/-- Section 2.3.1, step (2) of `Full`: "A_λ := ∑_s φ_λ(s) a_s". -/
def encodeStepL {L : ℕ} (lam : Term) (a : LeftStr (L + 1) → ℤ) : LeftStr L → ℤ :=
  fun u' => ∑ s, phi lam s * sliceAt a s u'

/-- Section 2.3.1, step (2) of `Full`: "B_λ := ∑_t ψ_λ(t) b_t". -/
def encodeStepR {L : ℕ} (lam : Term) (b : RightStr (L + 1) → ℤ) : RightStr L → ℤ :=
  fun v' => ∑ t, psi lam t * sliceAt b t v'

/-- Section 2.3.1: "The recursion Full(a, b), for arrays a, b on the left and right strings of
length L, returns an array on the output strings of length L:
(1) If L = 0, return the number ab.
(2) For each term λ of Schönhage's identity, form A_λ := ∑_s φ_λ(s) a_s and B_λ := ∑_t ψ_λ(t) b_t.
(3) For each term λ, recursively compute C_λ := Full(A_λ, B_λ).
(4) Return the array c whose slices are c_{z_ij} := C_{P_ij} and c_{z₀} := ∑_λ C_λ."

`Full.run` is this recursion, and it also keeps a record of the multiplications.  Its first
component is the array that is returned.  Its second component gives, for each leaf `τ`, the two
numbers that step (1) multiplies at `τ`: the leaf `λ τ'` of a call is the leaf `τ'` of its recursive
call for `λ`.

An array on the strings of length 0 has one entry, at the empty string `Fin.elim0`; that entry is
"the number". -/
def Full.run : (L : ℕ) → (LeftStr L → ℤ) → (RightStr L → ℤ) → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ)
  | 0, a, b => (fun _ => a Fin.elim0 * b Fin.elim0, fun _ => (a Fin.elim0, b Fin.elim0))
  | L + 1, a, b =>
    let R : Term → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ) := fun lam =>
      Full.run L (encodeStepL lam a) (encodeStepR lam b)
    (fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w),
      fun τ => (R (τ 0)).2 (Fin.tail τ))

/-- The array that `Full(a, b)` returns. -/
def Full (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ := (Full.run L a b).1

/-! ### 2.3.2 Unraveling the recursion computation -/

/-- Section 2.3.2: "Φ_τ(a) := ∑_u a[u] ∏_{ℓ=1}^{L} φ_{τ_ℓ}(u_ℓ)", the sum over all left strings
`u`. -/
def Phi {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, phi (τ ℓ) (u ℓ)

/-- Section 2.3.2: "Ψ_τ(b) := ∑_v b[v] ∏_{ℓ=1}^{L} ψ_{τ_ℓ}(v_ℓ)", the sum over all right strings
`v`. -/
def Psi {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ := ∑ v, b v * ∏ ℓ, psi (τ ℓ) (v ℓ)

/-- Section 2.3.2: "a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes to w_ℓ at
every level ℓ ≤ k", for a leaf, that is, for `k = L`: the leaf `τ` contributes to `w` if `τ_ℓ`
contributes to `w_ℓ` at every level `ℓ`. -/
def Leaf.Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)

instance Leaf.instDecidableContributes {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Decidable (Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))

/-- Equation (2): "Mult(a, b)[w] := ∑_{τ contributing to w} Φ_τ(a) Ψ_τ(b)". -/
def Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  fun w => ∑ τ : Leaf L with Leaf.Contributes τ w, Phi τ a * Psi τ b

/-- Equation (3): "γ(s, t, z) := ∑_{λ contributing to z} φ_λ(s) ψ_λ(t)". -/
def gamma (s : LeftVar) (t : RightVar) (z : OutVar) : ℤ :=
  ∑ lam : Term with lam.Contributes z, phi lam s * psi lam t

/-! ### 2.3.3 Batch computation of multiple matrix products -/

/-- Section 2.3.3: "The inner set of a left string is the set of levels at which it has a p (as
opposed to an x)." -/
def innerSetL {L : ℕ} (u : LeftStr L) : Finset (Fin L) := univ.filter fun ℓ => (u ℓ).IsInner
/-- Section 2.3.3: "the inner set of a right string is the set of levels at which it has a q (as
opposed to a y)". -/
def innerSetR {L : ℕ} (v : RightStr L) : Finset (Fin L) := univ.filter fun ℓ => (v ℓ).IsInner
/-- Section 2.3.3: "the inner set of an output string is the set of levels at which it has z₀ (as
opposed to a z_ij)". -/
def innerSetO {L : ℕ} (w : OutStr L) : Finset (Fin L) := univ.filter fun ℓ => (w ℓ).IsInner

/-- Section 2.3.3: "N₀ := 3^{L-m}".  Meant for `m ≤ L`; for `m > L` the subtraction of natural
numbers is cut off at 0 and the value is 1. -/
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)
/-- Section 2.3.3: "D := 4^m". -/
def D (m : ℕ) : ℕ := 4 ^ m
/-- Section 2.3.3: "K := binom(L, m)", the number of subsets of `{1, …, L}` of size `m`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- The index `i` of an outer left variable `x_i` (the value at a `p` is never used). -/
def LeftVar.outerIndex : LeftVar → Fin 3
  | .x i => i
  | .p _ _ => 0
/-- The index pair `(i, j)` of an inner left variable `p_ij` (the value at an `x` is never used). -/
def LeftVar.innerIndex : LeftVar → Fin 2 × Fin 2
  | .x _ => (0, 0)
  | .p i j => (i, j)
/-- The index `j` of an outer right variable `y_j` (the value at a `q` is never used). -/
def RightVar.outerIndex : RightVar → Fin 3
  | .y j => j
  | .q _ _ => 0
/-- The index pair `(i, j)` of an inner right variable `q_ij` (the value at a `y` is never used). -/
def RightVar.innerIndex : RightVar → Fin 2 × Fin 2
  | .y _ => (0, 0)
  | .q i j => (i, j)

/-- A string of `L - m` outer left variables `x_{i₁} ⋯ x_{i_{L-m}}`, written as the string of its
indices `i₁ ⋯ i_{L-m}`.  The same type is used for strings `y_{j₁} ⋯ y_{j_{L-m}}` of outer right
variables.  Section 2.3.3: these strings index the `N₀` rows of an `N₀ × D` matrix and the `N₀`
columns of a `D × N₀` matrix. -/
abbrev OuterStr (L m : ℕ) : Type := Fin (L - m) → Fin 3

/-- A string of `m` inner left variables `π = p_{i₁j₁} ⋯ p_{i_m j_m}`, written as the string of its
index pairs.  The same type is used for strings `π' = q_{i₁j₁} ⋯ q_{i_m j_m}` of inner right
variables, so that the paper's `π'`, "with the same indices" as `π`, is the same element of this
type as `π`. Section 2.3.3: these strings index the `D` columns of an `N₀ × D` matrix and the `D`
rows of a `D × N₀` matrix. With this convention the paper's "(AB)[r, c] := ∑_π A[r, π] B[π', c]" is
the usual matrix product. -/
abbrev InnerStr (m : ℕ) : Type := Fin m → Fin 2 × Fin 2

/-- The levels of a set `Q` of `m` levels "in the order of the levels" (Section 2.3.3): the `k`-th
lowest level of `Q`. -/
def innerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin m ↪o Fin L :=
  Q.orderEmbOfFin hQ

/-- The number of levels outside a set of `m` levels is `L - m`. -/
theorem card_compl_of_card_eq {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Qᶜ.card = L - m := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]

/-- The levels outside a set `Q` of `m` levels, in the order of the levels: the `k`-th lowest level
outside `Q`. -/
def outerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin (L - m) ↪o Fin L :=
  Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)

/-- Section 2.3.3: "its outer part is the string of its variables at the other levels", for a left
string whose inner set has `m` elements. -/
def outerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : OuterStr L m :=
  fun k => (u (outerLevel (innerSetL u) h k)).outerIndex
/-- Section 2.3.3: "The inner part of a string is the string of its variables at the levels of its
inner set, in the order of the levels", for a left string whose inner set has `m` elements. -/
def innerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : InnerStr m :=
  fun k => (u (innerLevel (innerSetL u) h k)).innerIndex
/-- The outer part of a right string whose inner set has `m` elements. -/
def outerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : OuterStr L m :=
  fun k => (v (outerLevel (innerSetR v) h k)).outerIndex
/-- The inner part of a right string whose inner set has `m` elements. -/
def innerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : InnerStr m :=
  fun k => (v (innerLevel (innerSetR v) h k)).innerIndex

/-- An `N₀ × D` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev LeftMat (L m : ℕ) : Type := Matrix (OuterStr L m) (InnerStr m) ℤ
/-- A `D × N₀` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev RightMat (L m : ℕ) : Type := Matrix (InnerStr m) (OuterStr L m) ℤ

/-- Section 2.3.3: "a[u] := X_Q[u] […] for all the left strings u […] whose inner set Q has exactly
m elements, and a[u] := 0 […] at every other string", where "X_Q[u]" is the entry of `X_Q` "at the
row and the column of u": the row is the outer part of `u` and the column is its inner part. The
family `X` gives a matrix `X Q` for every set `Q` of levels; only those with `|Q| = m` are used. -/
def arrayL {L : ℕ} (m : ℕ) (X : Finset (Fin L) → LeftMat L m) : LeftStr L → ℤ :=
  fun u =>
    if h : (innerSetL u).card = m then X (innerSetL u) (outerPartL u h) (innerPartL u h) else 0

/-- Section 2.3.3: "b[v] := Y_Q[v]" for the right strings `v` whose inner set `Q` has exactly `m`
elements, "the row given by the inner part of v and the column by the outer part", and `b[v] := 0`
at every other string. -/
def arrayR {L : ℕ} (m : ℕ) (Y : Finset (Fin L) → RightMat L m) : RightStr L → ℤ :=
  fun v =>
    if h : (innerSetR v).card = m then Y (innerSetR v) (innerPartR v h) (outerPartR v h) else 0

/-! ### 2.3.4 Tiling the N × D × N product by products of shape N₀ × D × N₀: the number `M` -/

/-- Section 2.3.4: "M := K N₀²". -/
def M (L m : ℕ) : ℕ := K L m * N0 L m ^ 2

/-! ### 2.4.1 Sharing the encoding -/

/-- Section 2.4.1: "The encoding of a is the array of the 10^L numbers Φ_τ(a), indexed by the leaves
τ." -/
def encodingL {L : ℕ} (a : LeftStr L → ℤ) : Leaf L → ℤ := fun τ => Phi τ a

/-- Section 2.4.1: "The encoding of b, the array of the numbers Ψ_τ(b)". -/
def encodingR {L : ℕ} (b : RightStr L → ℤ) : Leaf L → ℤ := fun τ => Psi τ b

/-! ### 2.4.2 Skipping the calls that are not needed -/

/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/

/-- The term that the private leaf has at a level where the output string has the variable `z`:
`P₀` for `z₀` and `P_ij` for `z_ij`. -/
def OutVar.privateTerm : OutVar → Term
  | .z i j => .P i j
  | .z0 => .P0

/-- Section 2.4.3: "the leaves contributing to an output string with inner set Q are the 10^m leaves
that choose any term at each of the m levels of Q, but P_ij at every level outside Q where the
output string has z_ij. We call the one that chooses P₀ at every level of Q the private leaf of the
output string." -/
def privateLeaf {L : ℕ} (w : OutStr L) : Leaf L := fun ℓ => (w ℓ).privateTerm

/-- The set of levels at which a leaf chooses `P₀`. -/
def P0Levels {L : ℕ} (τ : Leaf L) : Finset (Fin L) := univ.filter fun ℓ => τ ℓ = Term.P0

/-- Section 2.4.3: "we define the order of a leaf as m minus the number of levels at which it
chooses P₀." The order is an integer; it is negative for a leaf that chooses `P₀` at more than `m`
levels. -/
def order {L : ℕ} (m : ℕ) (τ : Leaf L) : ℤ := (m : ℤ) - ((P0Levels τ).card : ℤ)

/-- Section 2.4.3: "α_d := binom(m, d) 9^d". -/
def alpha (m d : ℕ) : ℕ := m.choose d * 9 ^ d

/-- Section 2.4.3: "β_d := binom(L, m-d) 9^{L-m+d}".  Meant for `d ≤ m ≤ L`; outside this range the
subtractions of natural numbers are cut off at 0 and the value has no meaning. -/
def beta (L m d : ℕ) : ℕ := L.choose (m - d) * 9 ^ (L - m + d)

end ThreeSumApsp

end Sec2Definitions

/-!
## Section 2: statements

The numbered lemmas and equations of Section 2 of the paper, and the figures that
assert something of their own.

* Equation (1) is `Eq_1`. Equations (2) and (3) are the definitions `Mult` and `gamma`. Equation (4)
  is the display of `Lemma_9`. Equation (5) is stated in three pieces: `Eq_5_ratio`, `Eq_5_bound`,
  `Eq_5`. Equation (6) is `Eq_6`.
* Lemmas 6 to 11 are `Lemma_6` to `Lemma_11`, each as one statement.
* Of Figure 3 the two worked examples of the caption are stated: `Figure_3`. Of Figure 4 the worked
  example is stated: `Figure_4`. Figure 6 is `Figure_6`; the two counts
  `Sec2_card_contributing_of_order` and `Sec2_card_outStr_of_leaf` say what its numbers count.
* Theorem 5 is a sentence about a machine. It is `Items.Theorem_5`. So of the tiling (Section 2.3.4)
  and of the proof of Theorem 5 (Section 2.4.4) nothing is stated here but the number `M` and
  equation (6): the statements of this part are about a single run of the recursion.
* Remark 12 makes no mathematical claim. Figure 2 recalls Strassen's recursion for intuition; only
  identity (1) is stated. Figure 5 makes no claim of its own. Figure 7 draws the count of Lemma 11;
  two remarks of its caption, that "the bound |U|α_d grows with d up to d ≈ 0.9m" and that the proof
  splits at a point "which is not necessarily where the two bounds cross", are not stated.

`docs/INDEX.md` says for each item of the paper what is stated and what is not.

A hypothesis that is not in the printed text is marked NOTE in the docstring. A hypothesis of the
printed text that is not needed (such as m ≥ 1, Section 2.3.3) is left out without a mark.
-/

/-!
## Section 3: definitions

Definitions used by the statements of Section 3, "Exact Triangle reduces to computing certain
entries of a thin matrix product".  They follow the paper's order and names.  Only what the
statements need, directly or through another definition, is defined here; some of the definitions
are used by the statements about programs and not by those of Section 3.

Conventions used throughout.

* A part of `n` vertices is the type `Fin n`.  A pair `(a, b) ∈ A × B` is an element of
  `Fin n × Fin n`, a triple `(a, b, c) ∈ A × B × C` an element of `Fin n × Fin n × Fin n`.
* The paper numbers the pieces from 1; here pieces and chunks are numbered from 0.
* `√D` is the real square root `Real.sqrt D`, `⌊·⌋` and `⌈·⌉` are `Nat.floor` and `Nat.ceil` of real
  numbers, and `log` is the natural logarithm `Real.log` unless a base is written.
* `x ≡ y (mod p)` is `Int.ModEq`, written `x ≡ y [ZMOD p]`.  A residue or label in `ℤ_p` is an
  element of `Fin p`.
* No definition of this part mentions time.  For the sentences of the paper about running time see
  `docs/REMARKS.md`, "Section 3: running times". -/

section Sec3Definitions

namespace ThreeSumApsp

/-! ### 3.1 The Lopsided All-Edges Sparse Triangle problem -/

/-! #### Cutting a set of pairs into sets of bounded size

Corollary 15 ("splitting W into sets of at most n²/√D query pairs") and the proof of Theorem 17
("cut it into chunks of at most n²/√D query pairs") cut a set of pairs into smaller sets.  The paper
does not say how; we cut along the row-major order of the pairs. -/

/-- The largest number of query pairs that is "at most n²/√D" (Corollary 15 and Theorem 17;
Theorem 5 has "at most N²/√D"): `⌊n²/√D⌋`. -/
noncomputable def queryCap (n D : ℕ) : ℕ := ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊

/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/

/-- Section 3.2: "An instance of Exact Triangle [...] consists of a complete tripartite graph on
vertex parts A, B, C of n vertices each, and an integer weight w(e) on every edge".  The three
fields are the weights `w(a,b)`, `w(b,c)` and `w(a,c)`.  The type `R` of the weights is `ℤ` in
Section 3; Section 5 also uses real weights.  The bound on the weights is a separate predicate
(`WeightsBoundedBy`, `WeightsPolyBounded`). -/
structure TriangleInstance (R : Type) (n : ℕ) where
  /-- `wAB a b` is the weight `w(a,b)` of the edge between `a ∈ A` and `b ∈ B`. -/
  wAB : Fin n → Fin n → R
  /-- `wBC b c` is the weight `w(b,c)` of the edge between `b ∈ B` and `c ∈ C`. -/
  wBC : Fin n → Fin n → R
  /-- `wAC a c` is the weight `w(a,c)` of the edge between `a ∈ A` and `c ∈ C`. -/
  wAC : Fin n → Fin n → R

namespace TriangleInstance

/-- Section 3.2: "Let S(a,b,c) := w(a,b) + w(b,c) + w(a,c)." -/
def S {R : Type} [Add R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) : R :=
  T.wAB a b + T.wBC b c + T.wAC a c

/-- Section 3.2: "A zero triangle is a triangle (a,b,c) ∈ A × B × C with S(a,b,c) = 0". -/
def IsZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) :
    Prop :=
  T.S a b c = 0

/-- Section 3.2: "the task is to decide whether one exists". -/
def HasZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.IsZeroTriangle a b c

/-- Section 3.2: "with |w(e)| ≤ n^ν for some constant ν ≥ 1".  `κ`, the paper's ν, is a real
number. -/
def WeightsPolyBounded {n : ℕ} (T : TriangleInstance ℤ n) (κ : ℝ) : Prop :=
  (∀ a b, ((|T.wAB a b| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧ (∀ b c, ((|T.wBC b c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧
    (∀ a c, ((|T.wAC a c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ)

end TriangleInstance

/-! #### Hashing modulo a prime (proof of Theorem 17) -/

open Classical in
/-- Proof of Theorem 17: the primes "p ∈ [√D/2, √D)", called "the primes in the range". -/
noncomputable def primesInRange (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun p => p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D

namespace TriangleInstance

/-- Proof of Theorem 17: "For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod
p)."  This is that count. -/
def countZeroMod {n : ℕ} (T : TriangleInstance ℤ n) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun ((a, b, c) : Fin n × Fin n × Fin n) => T.S a b c ≡ 0 [ZMOD (p : ℤ)]).card

/-- Proof of Theorem 17: "We select the prime with the smallest count [...] and call it p."  The
paper does not say how ties are broken, so this is a predicate: `p` is a prime in the range whose
count is smallest. -/
def IsSelectedPrime {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : Prop :=
  p ∈ primesInRange D ∧ ∀ q ∈ primesInRange D, T.countZeroMod p ≤ T.countZeroMod q

end TriangleInstance

/-! #### The instances (proof of Theorem 17) -/

/-- Proof of Theorem 17: "let s := ⌊√D⌋". -/
noncomputable def sOf (D : ℕ) : ℕ := ⌊Real.sqrt D⌋₊

/-! ### 3.4 3SUM and APSP reduce to Exact Triangle: the problems -/

/-- **3SUM**, Section 1: "Given n numbers, decide whether three of them sum to 0."  This is the
question that the problem `EndStatement.ThreeSum` asks.

NOTE.  We read "three of them" as three numbers at three different positions of the input. -/
abbrev ThreeSum {n : ℕ} (x : Fin n → ℤ) : Prop := EndStatement.ThreeSum.yes x

/-- **Convolution-3SUM**, Section 1.2: "do x₀, …, x_{n−1} satisfy x_i + x_j = x_{i+j} for some
i, j?" -/
def Convolution3SUM {R : Type} [Add R] {N : ℕ} (x : Fin N → R) : Prop :=
  ∃ (i j : Fin N) (h : i.val + j.val < N), x i + x j = x ⟨i.val + j.val, h⟩

/-- **Negative Triangle**, Section 1.2: "asks whether an edge-weighted graph has a triangle of
negative total weight".  The instances here are those of Exact Triangle. -/
def TriangleInstance.HasNegativeTriangle {R : Type} [Add R] [Zero R] [LT R] {n : ℕ}
    (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.S a b c < 0

/-- The (min,+)-product as a function, for matrices whose entries may be `+∞` (`⊤`): the minimum
over the empty set, and any sum with `+∞`, is `+∞`. -/
def minPlus {R : Type} [Add R] [LinearOrder R] {n m l : ℕ} (A : Matrix (Fin n) (Fin m) (WithTop R))
    (B : Matrix (Fin m) (Fin l) (WithTop R)) : Matrix (Fin n) (Fin l) (WithTop R) :=
  Matrix.of fun i j => Finset.univ.inf fun k => A i k + B k j

/-! A directed graph on the vertices `Fin n` with edge weights in `R` is a function
`w : Fin n → Fin n → WithTop R`: `w i j` is the weight of the edge from `i` to `j`, and `⊤` (that
is, `+∞`) if there is no such edge.  A walk that starts at `i` is given by the list of the vertices
it visits after `i`. -/

/-- The vertex at which the walk that starts at `i` and then visits `rest` ends. -/
def walkEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | i, [] => i
  | _, j :: rest => walkEnd j rest

/-- The total weight of the walk that starts at `i` and then visits `rest`; it is `⊤` if one of its
edges is missing, and the empty walk has weight 0. -/
def walkWeight {R : Type} [Add R] [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Fin n → List (Fin n) → WithTop R
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest

/-- Section 1 and Theorems 21 and 22: "no negative cycles".  Stated for closed walks, which is the
same thing: a closed walk decomposes into cycles. -/
def NoNegativeCycle {R : Type} [Add R] [Zero R] [LE R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Prop :=
  ∀ (i : Fin n) (rest : List (Fin n)), walkEnd i rest = i → 0 ≤ walkWeight w i rest

/-- **APSP**, Section 1: "compute the shortest-path distance between every pair of vertices".  `d i
j` is the least weight of a walk from `i` to `j`, and `⊤` if `j` cannot be reached from `i`. -/
def IsDistanceMatrix {R : Type} [Add R] [Zero R] [Preorder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (d : Fin n → Fin n → WithTop R) : Prop :=
  ∀ i j, IsLeast {x | ∃ rest : List (Fin n), walkEnd i rest = j ∧ walkWeight w i rest = x} (d i j)

/-- Every edge weight of the directed graph has absolute value at most `U`. -/
def EdgeWeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (w : Fin n → Fin n → WithTop R)
    (U : R) : Prop :=
  ∀ (i j : Fin n) (x : R), w i j = (x : WithTop R) → |x| ≤ U

/-- The weight matrix of the graph, for the repeated squaring behind Theorem 21(b).  Its diagonal
entries are 0, without which repeated squaring would compute walks of exactly `2^t` edges. -/
def weightMatrix {R : Type} [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Matrix (Fin n) (Fin n) (WithTop R) :=
  Matrix.of fun i j => if i = j then 0 else w i j

/-- Repeated squaring, for Theorem 21(b): `minPlusSquares w t` is the weight matrix after `t`
squarings in the (min,+)-product. -/
def minPlusSquares {R : Type} [Add R] [Zero R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) : ℕ → Matrix (Fin n) (Fin n) (WithTop R)
  | 0 => weightMatrix w
  | t + 1 => minPlus (minPlusSquares w t) (minPlusSquares w t)

/-! #### The shape of the two reductions of [VW13] that Theorem 21 cites -/

/-- A rule that says where each edge weight of a triangle instance on `t` vertices per part is
copied from, given an input `x₀, …, x_{N−1}`: `some (false, i)` stands for `x_i`, `some (true, i)`
for `−x_i`, and `none` for a filler weight.  The rule does not depend on the numbers `x_i`. -/
structure TriangleTemplate (t N : ℕ) where
  /-- The source of `w(a,b)`. -/
  eAB : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(b,c)`. -/
  eBC : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(a,c)`. -/
  eAC : Fin t → Fin t → Option (Bool × Fin N)

/-- The weight that a source stands for, given the input `x` and the filler weight `fill`. -/
def templateWeight {N : ℕ} (x : Fin N → ℤ) (fill : ℤ) : Option (Bool × Fin N) → ℤ
  | none => fill
  | some (false, i) => x i
  | some (true, i) => -x i

/-- The triangle instance that a template produces from the input `x` and the filler weight
`fill`. -/
def TriangleTemplate.instantiate {t N : ℕ} (τ : TriangleTemplate t N) (x : Fin N → ℤ) (fill : ℤ) :
    TriangleInstance ℤ t where
  wAB a b := templateWeight x fill (τ.eAB a b)
  wBC b c := templateWeight x fill (τ.eBC b c)
  wAC a c := templateWeight x fill (τ.eAC a c)

/-! #### Asymptotic notation of Section 3 -/

def IsBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a

def IsPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → IsBigOPow f (a + η)

def IsPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ e : ℕ, Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e

end ThreeSumApsp

end Sec3Definitions

/-!
## The reduction of Chan and He: definitions

[CH20] is Timothy M. Chan and Qizheng He, *Reducing 3SUM to Convolution-3SUM*, Proc. 3rd SIAM
Symposium on Simplicity in Algorithms (SOSA 2020).  Theorem 21(a) of the paper cites [CH20].  What
is used is the reduction in the proof of its Theorem 5.1, a deterministic reduction from 3SUM to
polylogarithmically many instances of Convolution-3SUM.  The theorem itself is a statement about
running times, for 3SUM on three sets and Convolution-3SUM on three arrays.

This part defines such a reduction, as a function from inputs to lists of instances.  What is proved
about it is stated by `Theorem_21a_threeSum_to_convolution` and `Theorem_21a_threeSum_to_exact`.
The construction follows the proof of Theorem 5.1.  Where it differs from [CH20], and what it adds,
is listed in `docs/REMARKS.md`, "Section 3: cited results".

### Why all these definitions are trusted

The list of instances depends on the input.  A statement of the form "there is a list of instances
such that the input has a solution iff one of them has" would be true for trivial reasons.  So the
statements are about the explicitly defined function `instances`, which is built from `reduction`,
and their worth rests on the definitions of this part.

* `reduction` takes three sets of at most n integers.  It returns the nodes of a recursion tree, and
  each node stands for one instance of Convolution-3SUM on three arrays.  3SUM on three sets (are
  there a, b, c, one from each set, with a + b + c = 0?) and Convolution-3SUM on three arrays (are
  there i, j with X i + Y j = Z (i + j)?) are the problems of Definitions 2.1 and 2.2 of [CH20], for
  which Theorem 5.1 is stated.
* `instances` takes n numbers, for the problem whether three of them, at three different positions,
  sum to 0.  It returns instances of Convolution-3SUM on one array.  These are the problems of the
  paper, 3SUM in the reading fixed at `ThreeSum`.

Evaluated literally, `coll` and `heavy` compare all pairs of elements, and each search tests all its
candidates, so the definitions are a specification and not the algorithm.  Nothing in this part is
about a machine.

Every choice that the two functions make depends only on which elements collide and how many pairs
do, on which sets are empty, on binary digits of the numbers and on how often a number occurs.  None
depends on whether a solution exists, with one exception: the solution 0, 0, 0 exists exactly when 0
occurs at three positions.  So it is detected by counting, and it is reported through the three-set
input (`zeroSet x`, {0}, {0}), which has a solution exactly in that case.

In this part `ν` is a node of the recursion tree.  It is not the exponent ν of Theorem 21, which
the statements call `κ`.
-/

section ChanHeDefinitions

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ### Collisions and heavy elements -/

/-- The number of ordered pairs of distinct elements of `S` that are congruent modulo `M`. -/
def coll (S : Finset ℤ) (M : ℕ) : ℕ := #{p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}

/-- The elements of `S` that share their residue modulo `M` with another element of `S`.  They play
the role of the bad elements of [CH20].  The other elements of `S`, those that are alone in their
residue class modulo `M`, are called light below; they play the role of the good elements of [CH20].
-/
def heavy (S : Finset ℤ) (M : ℕ) : Finset ℤ := {x ∈ S | ∃ y ∈ S, y ≠ x ∧ (M : ℤ) ∣ x - y}

/-! ### The arrays of one node -/

/-- The elements of `S` with remainder `r` modulo `M`. -/
def bucket (S : Finset ℤ) (M : ℕ) (r : ℤ) : Finset ℤ := {x ∈ S | x % (M : ℤ) = r}

/-- The array of the light elements of `S`.  Cell `i` holds the element of the bucket of `i` if that
bucket has exactly one element, and the padding value `pad` otherwise. -/
def arr (S : Finset ℤ) (M : ℕ) (pad : ℤ) (i : ℕ) : ℤ :=
  if #(bucket S M i) = 1 then ∑ x ∈ bucket S M i, x else pad

/-- The padding value `2U + 1`.  It is too large to take part in a solution among numbers of
absolute value at most `U`. -/
def pad (U : ℕ) : ℤ := 2 * U + 1

/-- The array made from the first or the second set of a node. -/
def arrXY (S : Finset ℤ) (M U : ℕ) : ℕ → ℤ := arr S M (pad U)

/-- The third array of a node.  A light element `c` of `S` is written as `-c` into the two cells `r`
and `r + M`, where `r` is the remainder of `-c`.  All other cells, and all cells from `2M` on, hold
`-pad U`. -/
def arrZ (S : Finset ℤ) (M U : ℕ) (k : ℕ) : ℤ :=
  if k < 2 * M then arr (S.image fun c => -c) M (-pad U) (k % M) else -pad U

/-! ### The choice of the modulus -/

/-- The least element of a finite set of natural numbers, and 1 if the set is empty. -/
def pick (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.min' h else 1

/-- The first prime: the least `p` in `Q` modulo which each of the three sets has at most
`3Λ|S|²/|Q|` colliding pairs.  Here and below, `Q` is the set of candidate primes, and `Λ` bounds
how many of them divide a nonzero difference of two elements.  `reduction` takes the primes up to
`mPar n U` for `Q`, and `Lam U` for `Λ`. -/
def firstP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  pick {p ∈ Q | coll S₁ p * #Q ≤ 3 * Λ * #S₁ ^ 2 ∧ coll S₂ p * #Q ≤ 3 * Λ * #S₂ ^ 2 ∧
    coll S₃ p * #Q ≤ 3 * Λ * #S₃ ^ 2}

/-- The second prime, given the first: the least `q` in `Q` such that, in each of the three sets, at
most the fraction `3Λ/|Q|` of the pairs that collide modulo `p` still collide modulo `pq`. -/
def secondP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) (p : ℕ) : ℕ :=
  pick {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Λ * coll S₁ p ∧
    coll S₂ (p * q) * #Q ≤ 3 * Λ * coll S₂ p ∧ coll S₃ (p * q) * #Q ≤ 3 * Λ * coll S₃ p}

/-- The modulus of a node: the product of the two primes. -/
def modulus (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  firstP Q Λ S₁ S₂ S₃ * secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃)

/-! ### The recursion tree -/

/-- A node of the recursion tree: three sets and the modulus chosen for them. -/
structure Node where
  /-- The first set. -/
  S₁ : Finset ℤ
  /-- The second set. -/
  S₂ : Finset ℤ
  /-- The third set. -/
  S₃ : Finset ℤ
  /-- The modulus. -/
  M : ℕ

/-- The nodes on the first `f` levels of the recursion tree with root `(S₁, S₂, S₃)`; for `f = 0`
there are none.  A triple with an empty set is not a node and has no children.  Any other triple is
a node, and each of its three children replaces one of the sets by its heavy elements. -/
def nodes (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → List Node
  | 0, _, _, _ => []
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then [] else
      let M := modulus Q Λ S₁ S₂ S₃
      ⟨S₁, S₂, S₃, M⟩ ::
        (nodes Q Λ f (heavy S₁ M) S₂ S₃ ++ nodes Q Λ f S₁ (heavy S₂ M) S₃ ++
          nodes Q Λ f S₁ S₂ (heavy S₃ M))

/-! ### The parameters -/

/-- `⌊log₂(2U)⌋ + 1`.  A nonzero difference of two numbers in `[-U, U]` has fewer prime divisors
than this, and this many binary digits are enough for every number in `[0, 2U]`. -/
def Lam (U : ℕ) : ℕ := Nat.log 2 (2 * U) + 1

/-- `⌈log₂(⌊log₂ n⌋ + 2)⌉`.  In the recursion tree of `reduction n U`, for three sets of at most
`n ≥ 1` elements each, all of absolute value at most `U` (the hypotheses of the library's lemma
`ChanHe.reduction_correct`), a set is empty after this many replacements by its heavy elements. -/
def height (n : ℕ) : ℕ := Nat.clog 2 (Nat.log 2 n + 2)

/-- The number of levels of the recursion tree that are built.  Under the hypotheses named at
`height`, each of the three sets of a node has been replaced at most `height n - 1` times, because
it is not empty.  So a node has at most `3 (height n - 1)` nodes above it. -/
def fuel (n : ℕ) : ℕ := 3 * height n - 2

/-- The number of primes that we want to choose from. -/
def wPar (n U : ℕ) : ℕ := 5 * Lam U * (Nat.sqrt n + 1)

/-- The bound `m` on the primes.  There are at least `wPar n U` primes up to `m` (the library's
lemma `ChanHe.wPar_le_card_primesLE`). -/
def mPar (n U : ℕ) : ℕ := (wPar n U + 1) * (2 * Nat.log 2 (wPar n U + 1) + 4)

/-! ### The reduction for three sets -/

/-- **The reduction for three sets.**  Here `n` is an upper bound on the sizes of the three sets and
`U` on the absolute values of their elements; both stay fixed through the recursion.  The result is
a list of nodes.  The Convolution-3SUM instance of a node `ν` consists of the arrays
`arrXY ν.S₁ ν.M U`, `arrXY ν.S₂ ν.M U` and `arrZ ν.S₃ ν.M U`, read at any length
`N ≥ 2 * mPar n U ^ 2`. -/
def reduction (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : List Node :=
  nodes (Nat.primesLE (mPar n U)) (Lam U) (fuel n) S₁ S₂ S₃

/-! ### From n numbers to three sets -/

/-- The label of an element of `[-U, U]`: its value shifted into `[0, 2U]`. -/
def lab (U : ℕ) (x : ℤ) : ℕ := (x + U).toNat

/-- The elements of `S` whose label has the binary digit `v` at position `β`. -/
def splitA (U β : ℕ) (v : Bool) (S : Finset ℤ) : Finset ℤ := {x ∈ S | (lab U x).testBit β = v}

/-- The elements of `S` whose label has the other digit, `!v`, at position `β`, and the digit `w` at
position `β'`. For fixed `β`, `β'` and `v` the three sets `splitA U β v S`,
`splitB U β β' v false S` and `splitB U β β' v true S` are pairwise disjoint. -/
def splitB (U β β' : ℕ) (v w : Bool) (S : Finset ℤ) : Finset ℤ :=
  {x ∈ S | (lab U x).testBit β = !v ∧ (lab U x).testBit β' = w}

/-- The numbers `2a`, for the values `a ≠ 0` that occur at two positions or more. -/
def twiceSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ :=
  ({a ∈ univ.image x | a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a}}).image fun a => 2 * a

/-- The set `{0}` if 0 occurs at three positions or more, and the empty set otherwise.  This is the
one place where the reduction decides a case by itself: 0 occurs at three positions exactly when
`0, 0, 0` is a solution. -/
def zeroSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ := if 3 ≤ #{i : Fin n | x i = 0} then {0} else ∅

/-! ### Three arrays in one -/

/-- **Three arrays in one.**  With `G = 3W + 1`, where `W` bounds the entries of the three arrays,
cell `4i + 1` holds `X i + G`, cell `4i + 2` holds `Y i + 3G`, cell `4i + 3` holds `Z i + 4G`, and
cell `4i` holds `10G`.  In an equation `y_u + y_v = y_{u+v}` the multiples of `G` have to cancel,
and they do so only when `u` and `v` have the remainders 1 and 2 modulo 4. -/
def oneArray (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) : ℤ :=
  let G : ℤ := 3 * W + 1
  if u % 4 = 1 then X (u / 4) + G else if u % 4 = 2 then Y (u / 4) + 3 * G
  else if u % 4 = 3 then Z (u / 4) + 4 * G else 10 * G

/-- The one-array instance of a node. -/
def Node.oneArray (ν : Node) (U : ℕ) : ℕ → ℤ :=
  ChanHe.oneArray (2 * U + 1) (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)

/-! ### The whole reduction -/

/-- All nodes that the reduction makes from `n` numbers of absolute value at most `U`.  The set of
values is split in all `2 (Lam (2U))²` ways by two binary digits, for the solutions with three
distinct values.  Two further three-set inputs are for the solutions that repeat a value.  The bound
on absolute values is `2U` throughout, because `twiceSet x` needs it. -/
def allNodes (n U : ℕ) (x : Fin n → ℤ) : List Node :=
  ((List.range (Lam (2 * U))).flatMap fun β => (List.range (Lam (2 * U))).flatMap fun β' =>
    [false, true].flatMap fun v =>
      reduction n (2 * U) (splitA (2 * U) β v (univ.image x))
        (splitB (2 * U) β β' v false (univ.image x))
        (splitB (2 * U) β β' v true (univ.image x))) ++
  (reduction n (2 * U) (twiceSet x) {0} (univ.image x) ++ reduction n (2 * U) (zeroSet x) {0} {0})

/-- **The whole reduction**: the list of one-array Convolution-3SUM instances made from `n` numbers
of absolute value at most `U`.  Each is read at length `8 * mPar n (2 * U) ^ 2`. -/
def instances (n U : ℕ) (x : Fin n → ℤ) : List (ℕ → ℤ) :=
  (allNodes n U x).map fun ν => ν.oneArray (2 * U)

/-! ### Sizes for inputs of absolute value at most n ^ κ -/

/-- The common length of the instances made from `n` numbers of absolute value at most `n ^ κ`. -/
def lenOf (κ n : ℕ) : ℕ := 8 * mPar n (2 * n ^ κ) ^ 2

end ChanHe

end ThreeSumApsp

end ChanHeDefinitions

/-!
## Section 4: definitions

Definitions used by the statements of Section 4, "The matrix theorem in general: a data structure".
They follow the paper's order and names, with three exceptions: `Cube.starsToP0`, from the proof of
Lemma 29, stands with the cubes of Section 4.2; `epsStar`, from Section 4.1, stands with `Rc`; and
the definitions for Table 2, which is printed in Section 4.1, come last. Every notion of Section 2
(terms, leaves, output strings, inner sets, private leaf, order, `α_d`, `β_d`, `Φ_τ`, `Ψ_τ`) is the
one defined for Section 2 and is not redefined.

Conventions, in addition to those of the definitions of Section 2.

* Table 1: `m` and `L` are natural-number variables, and `D = 4^m`, `N₀ = 3^{L-m}`,
  `K = binom(L, m)`, `M = K N₀²`, `α_d`, `β_d` are `D m`, `N0 L m`, `K L m`, `M L m`, `alpha m d`,
  `beta L m d` of Section 2. The remaining rows of Table 1: `ρ` is `rho L m`, and `γ`, `q`, `R_c(γ)`
  are `gammaOf c θ`, `qOf θ`, `Rc c γ`, all defined below; the switching order is a natural number
  `t`, and the ratio `c`, `ε` and `κ` are real numbers.
* "we say that level ℓ is lower than level ℓ' if ℓ < ℓ'" (Section 4): levels are compared in the
  order of `Fin L`.
* An output string is `η` in the Lean text; the paper writes w.
* The paper fixes `0 ≤ t ≤ m` (Section 4.2) and `L ≥ 10m` (Section 4). The definitions below make
  sense for all natural numbers; the statements carry `t ≤ m` and `10 * m ≤ L` as explicit
  hypotheses where they are needed. `m - t` is subtraction of natural numbers, which is the ordinary
  difference because `t ≤ m`.
-/

section Sec4Definitions

open Finset

namespace ThreeSumApsp

/-! ### Notions from Section 2 -/

/-- Section 4: "For a leaf τ of a tile with input arrays a and b, we call Φ_τ(a) Ψ_τ(b) the product
at τ." -/
def productAt {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ := Phi τ a * Psi τ b

/-! ### 4.2 Boxes -/

/-- Section 4.2: the symbols of a cube, "each of which is one of the ten terms of Schönhage's
identity or a star ∗". -/
inductive CubeSymbol : Type
  | term (lam : Term)
  | star
  deriving DecidableEq, Fintype

/-- Section 4.2: "A cube is a string π = π₁ ⋯ π_L of L symbols, each of which is one of the ten
terms of Schönhage's identity or a star ∗." -/
abbrev Cube (L : ℕ) : Type := Fin L → CubeSymbol

/-- Section 4.2: "Its leaves are the leaves obtained by replacing each star by any of the ten
terms". So `τ` is a leaf of `π` if at every level `π` has a star or has the term of `τ`. -/
def Cube.HasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) : Prop :=
  ∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)

instance Cube.instDecidableHasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) :
    Decidable (Cube.HasLeaf π τ) :=
  inferInstanceAs (Decidable (∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)))

/-- Section 4.2: the set of the leaves of a cube. -/
def Cube.leaves {L : ℕ} (π : Cube L) : Finset (Leaf L) := univ.filter fun τ => Cube.HasLeaf π τ

/-- The set of levels at which a cube has a star. -/
def Cube.starLevels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.star

/-- The set of levels at which a cube has the symbol `P₀`. -/
def Cube.P0Levels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.term Term.P0

/-- Section 4.2: "The value of a cube π is the sum of the products at its leaves,
val(π) := ∑_{τ a leaf of π} Φ_τ(a) Ψ_τ(b)." -/
def Cube.val {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L) : ℤ :=
  ∑ τ ∈ Cube.leaves π, productAt a b τ

/-- Section 4.2: "A box is a cube π = π₁ ⋯ π_L such that (i) at most m - t of its symbols are P₀ or
stars, and (ii) every star is at a lower level than every P₀." -/
def IsBox {L : ℕ} (m t : ℕ) (π : Cube L) : Prop :=
  (Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'

instance IsBox.instDecidable {L : ℕ} (m t : ℕ) (π : Cube L) : Decidable (IsBox m t π) :=
  inferInstanceAs (Decidable ((Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'))

/-- The `k` lowest levels of `S` (Section 4.2 and Lemma 27: "the m - t - |Z| lowest levels of Q ∖
Z"): the levels of `S` with fewer than `k` levels of `S` below them. (All of `S` if `S` has at most
`k` levels.) -/
def lowest {L : ℕ} (k : ℕ) (S : Finset (Fin L)) : Finset (Fin L) :=
  S.filter fun ℓ => (S.filter fun ℓ' => ℓ' < ℓ).card < k

/-- Proof of Lemma 29: "the leaf we get by replacing its stars with P₀". -/
def Cube.starsToP0 {L : ℕ} (π : Cube L) : Leaf L :=
  fun ℓ =>
    match π ℓ with
    | .term lam => lam
    | .star => Term.P0

/-- Section 4.2: "V := Z ∪ {the m - t - |Z| lowest levels of Q ∖ Z} (Z padded from the bottom)". -/
def Vof {L : ℕ} (m t : ℕ) (Q Z : Finset (Fin L)) : Finset (Fin L) :=
  Z ∪ lowest (m - t - Z.card) (Q \ Z)

/-- Section 4.2: "F_V := {ℓ ∈ Q : ℓ < min(Q ∖ V)} (the levels that we have not reached)", and "We
define F_V by the same formula for every V ⊆ Q, with F_V := Q if V = Q." The condition "ℓ < min(Q ∖
V)" is written as "ℓ is below every level of Q ∖ V", which also gives the convention `F_V = Q` when
`Q ∖ V` is empty. (That this agrees with the paper's formula in both cases is the library's lemma
`FV_eq`.) -/
def FV {L : ℕ} (Q V : Finset (Fin L)) : Finset (Fin L) := Q.filter fun ℓ => ∀ ℓ' ∈ Q \ V, ℓ < ℓ'

/-- Section 4.2: "For V ⊆ Q with |V| = m - t, let 𝓑_V be the set of the 9^t cubes π with π_ℓ = ∗ if
ℓ ∈ F_V, P₀ if ℓ ∈ V ∖ F_V, one of the nine terms P_ij if ℓ ∈ Q ∖ V, the term P_ij with w_ℓ = z_ij
if ℓ ∉ Q", where `Q` is the inner set of the output string w, here `η`. The term of the last case is
the term of the private leaf of `η` (so the caption of Figure 10: "at every other level, they have
the term of the private leaf of w"). The boxes in these sets are "the boxes of w". -/
def BV {L : ℕ} (η : OutStr L) (V : Finset (Fin L)) : Finset (Cube L) :=
  univ.filter fun π => ∀ ℓ,
    (ℓ ∈ FV (innerSetO η) V → π ℓ = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → π ℓ = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, π ℓ = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → π ℓ = CubeSymbol.term (privateLeaf η ℓ))

/-- Lemma 28: the index set of the union and of the sum, "all V ⊆ Q with |V| = m - t". -/
def Vsets {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Finset (Fin L)) :=
  (innerSetO η).powersetCard (m - t)

/-- Lemma 28: the leaves "τ contributing to w of order < t". -/
def lowLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ < (t : ℤ)

/-- The right-hand side of the equation of Lemma 28: "∑_{τ contributing to w, of order < t} Φ_τ(a)
Ψ_τ(b) + ∑_{V ⊆ Q, |V| = m - t} ∑_{π ∈ 𝓑_V} val(π)". It is what a query computes in its steps (2)
and (3) (Section 4.3): "Add up the products at the leaves of order below t contributing to w", "Add
to this the values of the α_t boxes of w". -/
def querySum {L : ℕ} (m t : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, productAt a b τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, Cube.val a b π

/-! ### 4.3 The data structure, in terms of the parameters -/

/-- The set of all boxes (of a tile), for the parameters `L`, `m`, `t`. -/
def boxes (L m t : ℕ) : Finset (Cube L) := univ.filter fun π => IsBox m t π

/-- "the boxes with e stars" (proof of Lemma 29, which computes "the values of the boxes in
increasing order of their number of stars"). -/
def boxesWithStars (L m t e : ℕ) : Finset (Cube L) :=
  (boxes L m t).filter fun π => (Cube.starLevels π).card = e

/-- Proof of Lemma 29: "the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ". -/
def Cube.replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) : Cube L :=
  Function.update π ℓ (CubeSymbol.term lam)

/-- The dynamic program of Lemma 29 (proof, "The values"), which computes the value of a box with
`e` stars from the two encodings of the tile, `encA τ = Φ_τ(a)` and `encB τ = Ψ_τ(b)`: "The boxes
without stars are the leaves with at most m - t symbols P₀, and the value of each of them is the
product of its two numbers in the encodings. For a box π with e ≥ 1 stars, let ℓ be the highest
level at which π has a star. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with ten lookups in the
trie". A cube without stars is the leaf `Cube.starsToP0 π`. (The last case, a cube without stars
when `e ≥ 1`, does not occur for a box with `e` stars.) `dpValue` is the recurrence of this dynamic
program, not a program with a trie: where the paper looks a value up, `dpValue` computes it
again. -/
def dpValue {L : ℕ} (encA encB : Leaf L → ℤ) : ℕ → Cube L → ℤ
  | 0, π => encA (Cube.starsToP0 π) * encB (Cube.starsToP0 π)
  | e + 1, π =>
    if h : (Cube.starLevels π).Nonempty then
      ∑ lam : Term, dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)
    else 0

/-- The decay rate of the `β_d` (Table 1, and Section 4.3): "ρ := 9m / (L - m + 1)". -/
noncomputable def rho (L m : ℕ) : ℝ := 9 * (m : ℝ) / ((L : ℝ) - (m : ℝ) + 1)

/-- The expression inside the `O(·)` of the query time of Theorem 30:
"L ∑_{d=0}^{t} α_d". -/
noncomputable def costQuery (L m t : ℕ) : ℝ := (L : ℝ) * ∑ d ∈ range (t + 1), (alpha m d : ℝ)

/-! ### 4.4 Choosing the parameters -/

/-- Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". The padded
matrix has `D'` columns. This is a padding if `D₀ ≤ D'`; for `D' < D₀` the function drops the last
columns. -/
def padInnerCols {N D₀ : ℕ} (D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) : Matrix (Fin N) (Fin D') ℤ :=
  fun I k => if h : (k : ℕ) < D₀ then X I ⟨k, h⟩ else 0

/-- Proof of Corollary 26: "and zero rows of Y".  The padded matrix has `D'` rows.  This is a
padding if `D₀ ≤ D'`; for `D' < D₀` the function drops the last rows. -/
def padInnerRows {N D₀ : ℕ} (D' : ℕ) (Y : Matrix (Fin D₀) (Fin N) ℤ) : Matrix (Fin D') (Fin N) ℤ :=
  fun k J => if h : (k : ℕ) < D₀ then Y ⟨k, h⟩ J else 0

/-- Section 4.4: "let H(x) := -x ln x - (1 - x) ln(1 - x) be the entropy function (with natural
logarithms)". (Lean's `Real.log 0 = 0` gives `H(0) = H(1) = 0`, the usual convention.) -/
noncomputable def entropy (θ : ℝ) : ℝ := -θ * Real.log θ - (1 - θ) * Real.log (1 - θ)

/-- Corollary 31: "ρ_c := 9/(c - 1)". -/
noncomputable def rhoC (c : ℝ) : ℝ := 9 / (c - 1)

/-- Corollary 31: "q := (H(θ) + θ ln 9) / ln 4". -/
noncomputable def qOf (θ : ℝ) : ℝ := (entropy θ + θ * Real.log 9) / Real.log 4

/-- Table 1: "L and t are cm and θm rounded up to integers"; the proof of Corollary 31: "L := ⌈cm⌉".
(Only `L` gets a name here.) -/
noncomputable def levelsOf (c : ℝ) (m : ℕ) : ℕ := ⌈c * (m : ℝ)⌉₊

end ThreeSumApsp

end Sec4Definitions

section WordRamProblems

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

def Admissible (b : Nat) (params : List Nat) (W : Nat) : Prop :=
  b * ((params.map Nat.log2).sum + 1) ≤ W

def output {W : Nat} (c : Int → BitVec W) (len : Nat) (i : Nat) : Int :=
  (c ((len : Int) + (i : Int))).toInt

structure Problem where
  Inst : Type
  params : Inst → List ℕ
  input : Inst → List ℤ
  IsAnswer : Inst → Bool → (ℕ → ℤ) → Prop

def Solves (prob : Problem) (P : List Instr) (b : ℕ) (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) :
    Prop :=
  ∀ x : prob.Inst, dom x → ∀ bits : ℕ, Admissible b (prob.params x) bits →
    ∃ (t : ℕ) (verdict : Bool) (c : ℤ → BitVec bits), (t : ℝ) ≤ T x ∧
      exec P t 0 (loadWords bits (prob.input x)) = some (verdict, c) ∧
      prob.IsAnswer x verdict (output c (prob.input x).length)

def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

end ThreeSumApsp.WordRam

end WordRamProblems
