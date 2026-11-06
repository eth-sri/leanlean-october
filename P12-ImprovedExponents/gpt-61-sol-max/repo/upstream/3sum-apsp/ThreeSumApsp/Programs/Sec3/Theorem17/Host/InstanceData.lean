/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.ScanPairs
public import ThreeSumApsp.Spec.Sec3.Theorem17.Chunks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing

/-!
# The host of Theorem 17: the list of its instances, as pure data

Proof of Theorem 17, "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k form the instance".  After the prime
has been chosen, the host runs one loop over all instances: instance number `t` belongs to the piece
number `t / chunkCount` of `C` and to the chunk number `t % chunkCount` of the table of chunks.
This file defines what the host writes (`matX`, `matY`, `WI`, `WJ`), what the solver answers
(`ans`), which query pairs are accepted and which scans succeed (`acc`, `hit`), and whether a zero
triangle has been found before instance `t` (`found`).  The class of a residue `ϱ < p` is the
paper's `W_ϱ`: the pairs `(a, b)` whose weight is congruent to `ϱ` modulo `p`.  The pairs are listed
class after class, in the order of the residues, and a chunk is a segment of a class.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- The hypotheses of Theorem 17 on its parameters, in natural numbers: "Let 16 ≤ D ≤ n, and let
1 ≤ g ≤ √D be an integer." -/
structure BigCase (n D g : ℕ) : Prop where
  sixteen_le : 16 ≤ D
  le_n : D ≤ n
  one_le_g : 1 ≤ g
  g_le_sqrt : g ≤ Nat.sqrt D

/-- The data on which the loop over the instances depends. -/
structure HostData where
  /-- The number of vertices of each part. -/
  (n D p q cap : ℕ)
  /-- The weights of the edges `(a, b)`, row by row. -/
  (AB BC AC : List ℤ)

namespace HostData

variable (X : HostData)

/-- The residues modulo `p` of the weights of the edges `(a, b)`. -/
def RAB := residList X.p X.AB
/-- The residues modulo `p` of the weights of the edges `(b, c)`. -/
def RBC := residList X.p X.BC
/-- The residues modulo `p` of the weights of the edges `(a, c)`. -/
def RAC := residList X.p X.AC
/-- The rows `a` of all pairs `(a, b)`, class after class. -/
def QI := queryRows X.n X.p X.RAB
/-- The columns `b` of all pairs `(a, b)`, class after class. -/
def QJ := queryCols X.n X.p X.RAB
/-- The table of the chunks. -/
def CT := chunkTab X.n X.p X.cap X.RAB
/-- The number of chunks. -/
def chunkCount := X.CT.length
/-- The number of pieces. -/
def h := X.n ⌈/⌉ X.q
/-- The number of instances. -/
def m := X.h * X.chunkCount

/-- The first vertex of the piece of instance t. -/
def c0 t := t / X.chunkCount * X.q
/-- The number of vertices of the piece of instance t. -/
def len t := min X.q (X.n - X.c0 t)
/-- The chunk of instance t. -/
def chunk t := X.CT.getD (t % X.chunkCount) ⟨0, 0, 0⟩
/-- The residue `ϱ` of the chunk of instance t. -/
def rho t := (X.chunk t).residue
/-- The first place of the chunk of instance t in the list of all pairs. -/
def lo t := (X.chunk t).start
/-- The number of query pairs of instance t. -/
def w t := (X.chunk t).len

/-- The matrix `X` of instance t. -/
def matX t := xList X.n X.D X.p (X.c0 t) (X.len t) (X.rho t) X.RAC
/-- The matrix `Y` of instance t. -/
def matY t := yList X.n X.D X.p (X.c0 t) (X.len t) X.RBC
/-- The rows of the query pairs of instance t. -/
def WI t := (X.QI.drop (X.lo t)).take (X.w t)
/-- The columns of the query pairs of instance t. -/
def WJ t := (X.QJ.drop (X.lo t)).take (X.w t)

/-- The answers of a solver of Lop-AE-SparseTri to instance t. -/
def ans (t : ℕ) : List ℤ :=
  (thinOut X.n X.D (X.matX t) (X.matY t) (X.WI t) (X.WJ t)).map fun v => if v = 0 then 0 else 1

/-- The query pair number i of instance t is accepted. -/
def acc t i := decide ((X.ans t).getD i 0 ≠ 0)
/-- The scan for the query pair number i of instance t succeeds. -/
def hit t i :=
  scanHit X.n X.AB X.BC X.AC ((X.WI t).getD i 0) ((X.WJ t).getD i 0) (X.c0 t) (X.len t)

/-- A zero triangle has been found before instance t. -/
def found
  | 0 => false
  | t + 1 => foundAt (X.acc t) (X.hit t) (found t) (X.w t)

/-- The number of scans made for instance t. -/
def execs t := execsUpto (X.acc t) (X.hit t) (X.found t) (X.w t)
/-- The number of accepted query pairs of instance t whose scan fails or would fail. -/
def fails t := failsUpto (X.acc t) (X.hit t) (X.w t)

end HostData

end Light.Sec3
