module
public import ADR11.Types

/-! Executable finite-support calculus. A query consumes a forest and
returns weighted observations. At each population we interpolate in the
merge rates; the continuations compose populations and independent unions.
Monomials are multisets of length variables (multiplication is addition). -/
@[expose] public section
namespace ADR11.Computation
open Finset
variable {n : ℕ}
abbrev Clade (n : ℕ) := Finset (Fin n)
abbrev Family (n : ℕ) := Clusters (Fin n)
def decC (n c : ℕ) := univ.filter fun i : Fin n => i.val ∈ equivBitIndices c
def code (A : Clade n) := equivBitIndices.symm (A.map Fin.valEmbedding)
def decF (n : ℕ) (s : List ℕ) := (s.map (decC n)).toFinset

def clades (n : ℕ) := (List.finRange n).sublists.map List.toFinset
/-- A reproducible order for the independent child populations. -/
def schedule (C : Family n) : List (Clade n) := ((clades n).filter (· ∈ C)).dedup

namespace Sparse
/-- Rational polynomials in the branch coordinates. -/
abbrev Key := Multiset ℕ
abbrev Poly := Multiset (ℚ × Key)
abbrev Query (n : ℕ) := Family n → Poly

def shift (q : ℚ) (k : Key) (P : Poly) := P.map fun (r,l) => (q*r,k+l)
def weight (P Q : Poly) := P.bind fun (q,k) => shift q k Q

def paths (K F : Family n) : (k : ℕ) → (Fin (k+1) → Poly) → Query n → Poly
  | 0,v,u => weight (v 0) (u F)
  | k+1,v,u => if F ⊆ K then weight (v (Fin.last _)) (u F) + ∑ G ∈ merges F, paths K G k (fun i =>
      shift ((rate (k+1) : ℚ) - rate i)⁻¹ 0 (v i.castSucc + shift (-1) 0 (v (Fin.last _)))) u else 0

def value (A : Clade n) (i : ℕ) : Poly := if A = univ then (if i = 0 then {(1,0)} else 0) else {(1,Multiset.replicate (rate i) (code A))}
def advance (K : Family n) (A : Clade n) (F : Family n) := paths (if A = univ then K else univ) F (#(roots F)-1) (fun i => value A i)

def gather (μ : Clade n → Query n → Poly) : List (Clade n) → Family n → Query n → Poly
  | [],S,u => u S
  | b::bs,S,u => μ b fun F => gather μ bs (F ∪ S) u

def evalTree (H K : Family n) : ℕ → Clade n → Query n → Poly
  | 0,_,_ => 0
  | k+1,A,u => gather (evalTree H K k) (schedule (childClusters H A)) (sampledForest id A) fun F => advance K A F u

def observed (H T : Family n) := evalTree H (insert univ T) (n+1) univ fun F => if unroot F = T then {(1,0)} else 0

def coeff (P : Poly) (k : Key) := ((P.filter (·.2 = k)).map Prod.fst).sum
def agrees (P Q : Poly) := decide (∀ k ∈ ((P+Q).map Prod.snd).toFinset, coeff P k = coeff Q k)
def trim (H : Family n) (P : Poly) := P.map fun (q,k) => (q,k.filter fun c => decC n c ∈ H.erase univ)
def verifies (H T : Family n) (P : Poly) := agrees (observed H T) (trim H P)
end Sparse
end ADR11.Computation

namespace ADR11.Skeleton
open _root_.ADR11.Computation
abbrev hierarchy (n : ℕ) (s : List ℕ) := hierarchyOf (decF n s)
/-- Grow laminar presentations, pruning incompatible choices before enumeration. -/
def admissible (n : ℕ) : List ℕ → List (List ℕ)
  | [] => [[]]
  | a::cs => let r := admissible n cs; r ++ (r.filter fun s => s.all fun b => decide (Compatible (decC n a) (decC n b))).map (a::·)
def catalogue (n : ℕ) (C : List ℕ) := (admissible n C).map (hierarchy n)
def inner (n : ℕ) := ((clades n).filter fun A => 2 ≤ A.card ∧ A ≠ Finset.univ).map code
abbrev full (n : ℕ) := catalogue n (inner n)
/-- Split before reducing the certificates to bound kernel memory. -/
macro "check_forms" n:term:max cs:term:max : tactic => `(tactic| (
  intro H h
  change H ∈ (admissible $n $cs).map (hierarchy $n) at h
  obtain ⟨s,hs,e⟩ := List.mem_map.mp h
  subst H
  rw [show admissible $n $cs = (eval% admissible $n $cs) by decide +kernel] at hs
  fin_cases hs <;> decide +kernel))
end ADR11.Skeleton
