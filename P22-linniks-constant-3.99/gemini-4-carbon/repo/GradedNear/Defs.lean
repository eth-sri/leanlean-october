module

public import Mathlib

@[expose] public section

open MeasureTheory Set Finset Real DirichletCharacter
open Complex (I)
open List (zipWith zipWith3)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius Complex

noncomputable section

namespace GradedNear

open Classical in
def sameCharOthers {ι : Type*} [Fintype ι] {α : Type*} (χ : ι → α) (j : ι) :=
  univ.filter fun k => k ≠ j ∧ χ k = χ j

structure Condition1 (f : ℝ → ℝ) (x₀ B : ℝ) : Prop where
  pos : 0 < x₀
  cont : ContinuousOn f (Ici 0)
  vanish : ∀ t, x₀ ≤ t → f t = 0
  smooth : ContDiffOn ℝ 2 f (Ioo 0 x₀)
  bound : ∀ t ∈ Ioo 0 x₀, |deriv (deriv f) t| ≤ B

def laplace (f : ℝ → ℝ) z :=
  ∫ t in Ioi 0, f t * cexp (-(z * t))

structure Condition2 (f : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  re_nonneg : ∀ z, 0 ≤ z.re → 0 ≤ (laplace f z).re

section
variable {q : ℕ}

def primeSum (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (s : ℂ) :=
  ∑' n, Λ n * χ n * (n : ℂ) ^ (-s) * f (log n / log q)

def zeroSum [NeZero q] (χ : DirichletCharacter ℂ q) f (s : ℂ) δ :=
  ∑ᶠ ρ ∈ {ρ | ‖1 + s.im * I - ρ‖ ≤ δ ∧ LFunction χ ρ = 0},
    analyticOrderNatAt (LFunction χ) ρ * (laplace f ((s - ρ) * log q)).re

def LemmaRegion (q : ℕ) (s : ℂ) :=
  |s.re - 1| ≤ √(log (log q)) / log q ∧ |s.im| ≤ log q

def XylourisLemma31 :=
  ∀ f x₀ B, Condition1 f x₀ B →
    ∃ C q₀, ∀ q, q₀ ≤ q → ∀ s, LemmaRegion q s →
      ‖primeSum (q := q) 1 f s - log q * laplace f ((s - 1) * log q)‖ ≤
        C * log q / log (log q)

def XylourisLemma32 :=
  ∀ f x₀ B, Condition1 f x₀ B → 0 ≤ f 0 →
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ q₀, ∀ q, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ s, LemmaRegion q s →
        (primeSum χ f s).re ≤ -(log q * zeroSum χ f s δ) + f 0 / 6 * log q + ε * log q

def BurgessBound :=
  ∀ ε, 0 < ε → ∃ C, ∀ q (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ N H, 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Ioc N (N + H), χ n‖ ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3)

def BurgessPrimitive :=
  ∀ ε, 0 < ε → ∃ C, ∀ q, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ N H, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Ioc N (N + H), χ n‖ ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3)

def grahamWeight (V : ℝ) (d : ℕ) :=
  if (d : ℝ) ≤ V then μ d * log (V / d) / log V else 0

def GrahamEstimate :=
  ∃ C V₀, ∀ V N, V₀ ≤ V → V ≤ N →
    |∑ n ∈ Icc 1 ⌊N⌋₊, (∑ d ∈ n.divisors, grahamWeight V d) ^ 2 - N / log V| ≤ C * N / log V ^ 2

structure NearData where
  f : ℝ → ℝ
  (xf Bf : ℝ)
  g : ℝ → ℝ
  (xg Bg s₁ s : ℝ)
  m : ℕ
  (t h : ℕ → ℝ)
  ε' : ℝ
  Δ : Finset ℝ

namespace NearData

variable (D : NearData)

def sieveH u :=
  ∑ k ∈ range D.m, if D.t k ≤ u ∧ u < D.t (k + 1) then D.h k else 0

def omega u := D.g u * exp (D.s₁ * u) + D.sieveH u

def IB := ∫ u in Ioi 0, exp (2 * D.s * u) * D.f u ^ 2 / D.omega u

def level k := (D.t k - 1 / 3) / 2 - D.ε'

def Dδ δ :=
  (∫ u in Ioi 0, D.g u * exp ((D.s₁ - 2 * δ) * u)) +
    ∑ k ∈ range D.m, D.h k * exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

def d₁ := D.g 0 / 6

structure Valid : Prop where
  f_cond : Condition1 D.f D.xf D.Bf
  g_cond1 : Condition1 D.g D.xg D.Bg
  g_cond2 : Condition2 D.g
  ε'_pos : 0 < D.ε'
  t_lt : ∀ k < D.m, D.t k < D.t (k + 1)
  t_zero : 1 / 3 + 2 * D.ε' < D.t 0
  h_nonneg : ∀ k < D.m, 0 ≤ D.h k
  Δ_nonneg : ∀ δ ∈ D.Δ, 0 ≤ δ
  omega_lb : ∃ c, 0 < c ∧ ∀ u, 0 ≤ u → D.f u ≠ 0 → c ≤ D.omega u
  IB_pos : 0 < D.IB

end NearData

structure Entries (q : ℕ) (ι : Type*) where
  χ : ι → DirichletCharacter ℂ q
  (γ δ : ι → ℝ)

variable {ι : Type*}

def response (D : NearData) (E : Entries q ι) j :=
  -(primeSum (E.χ j) D.f (↑(1 - (D.s - E.δ j) / log q) + E.γ j * I)).re / log q

def pairExcess [Fintype ι] (D : NearData) (E : Entries q ι) j :=
  ∑ k ∈ sameCharOthers E.χ j,
    max 0 ((laplace D.g (↑(-(D.s₁ - E.δ j - E.δ k)) + ↑((E.γ j - E.γ k) * log q) * I)).re - D.d₁)

def SafeAnchor (q : ℕ) [NeZero q] s₁ T' :=
  ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ ρ, LFunction ψ ρ = 0 →
    |ρ.im| ≤ T' → ρ.re ≤ 1 - s₁ / log q

def responseAt (χ : DirichletCharacter ℂ q) f (σ γ : ℝ) :=
  -(primeSum χ f (↑(1 - σ / log q) + γ * I)).re / log q

def zeroTerm f (q : ℕ) σ γ (ρ : ℂ) :=
  (laplace f (↑((1 - ρ.re) * log q - σ) + ↑((γ - ρ.im) * log q) * I)).re

abbrev zmult [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℝ :=
  analyticOrderNatAt (LFunction χ) ρ

def keptBound [NeZero q] (D : NearData) (E : Entries q ι) (Sz : ι → Finset _) η j :=
  ∑ ρ ∈ Sz j, zmult (E.χ j) ρ * zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η

end

namespace Cert

def S : ℤ := 10 ^ 16
def TS : ℤ := 10 ^ 6
def DS : ℤ := 10 ^ 12
def HS : ℤ := 5 * 10 ^ 9

structure Col where
  (G W C NH E : ℤ)
  (v D : List ℤ)

structure RowHead where
  d : ℤ
  fam : List (ℤ × ℤ × ℤ)

structure Leaf where
  cols : List Col
  rows : List RowHead
  (F ng n2 first final : ℤ)

def isqrtUp (n : ℕ) := if n.sqrt * n.sqrt = n then n.sqrt else n.sqrt + 1

def rootEnd (d : ℤ) : ℤ := isqrtUp ((d * TS * TS / S).toNat + 1)

def ceilDiv (a b : ℤ) := -(-a / b)

def tangentCost v m2 h2 (c : ℕ) :=
  let x := v - m2 * HS
  if x ≤ 0 then 0 else
    let hS := h2 * HS
    (if c = 0 then x * (x + 2 * hS) else x * (x - 2 * hS)) / S

def tangentExact (v m h : ℚ) (c : ℕ) :=
  let x := max (v - m) 0
  if c = 0 then (x + h) ^ 2 - h ^ 2 else if 0 < x then (x - h) ^ 2 - h ^ 2 else 0

def colCost v D a b c :=
  if c = 2 then max (v - b * (S / TS)) 0 ^ 2 / D
  else tangentCost v (a + b) (b - a) c * S / D

def rowBudget (r : RowHead) a b c :=
  if c = 2 then
    S - S * S * a * a / (TS * TS * r.d) -
      (r.fam.map fun t => t.1 * max (t.2.1 - b * (S / TS)) 0 ^ 2 / t.2.2).sum
  else
    let p := (if c = 0 then (a : ℚ) else b) / TS
    let hq : ℚ := ↑(b - a) / (2 * TS)
    let bq : ℚ := 1 - (p ^ 2 - hq ^ 2) / (r.d / S) -
      (r.fam.map fun t => t.1 * tangentExact (t.2.1 / S)
        (↑(a + b) / (2 * TS)) hq c / (t.2.2 / S)).sum
    ⌈bq * S⌉

def colCosts (col : Col) (box : List (_ × _)) cs :=
  zipWith3 (fun ab vD c => colCost vD.1 vD.2 ab.1 ab.2 c) box (col.v.zip col.D) cs

def budgets (L : Leaf) (box : List (_ × _)) cs :=
  zipWith3 (fun r ab c => rowBudget r ab.1 ab.2 c) L.rows box cs

structure Duals where
  (Y V U P M : ℕ)
  Z : List ℕ

inductive CaseCert where
  | excluded
  | duals (du : Duals)

def caseValue (L : Leaf) box cs (du : Duals) :=
  if du.Z.length = L.rows.length ∧
      L.cols.all fun col => decide (DS * col.G ≤
        du.Y * col.W + du.V * col.C + du.U * col.NH + (↑du.P - ↑du.M) * col.E +
          (zipWith (fun z c => (z : ℤ) * c) du.Z (colCosts col box cs)).sum) then
    some (ceilDiv (du.Y * L.F + du.V * (2 * S) + du.U * (L.ng * S) + (↑du.P - ↑du.M) * (L.n2 * S) +
      (zipWith (fun z b => (z : ℤ) * b) du.Z (budgets L box cs)).sum) DS + L.first + L.final)
  else none

def excludable (L : Leaf) box cs :=
  (List.range L.rows.length).any fun k =>
    decide ((budgets L box cs).getD k 0 < 0) &&
      L.cols.all fun col => decide (0 ≤ (colCosts col box cs).getD k 0)

def caseVectors : List ℕ → List (List ℕ)
  | [] => [[]]
  | o :: os =>
    let rest := caseVectors os
    if o = 1 then rest.map (0 :: ·) ++ rest.map (1 :: ·) else rest.map (2 :: ·)

def checkBox (L : Leaf) box orders certs :=
  let cvs := caseVectors orders
  if orders.length = L.rows.length ∧ certs.length = cvs.length ∧
      orders.all fun o => o = 1 ∨ o = 2 then
    (cvs.zip certs).foldl (fun acc cc =>
      acc.bind fun m =>
        match cc.2 with
        | CaseCert.excluded => if excludable L box cc.1 then some m else none
        | .duals du => (caseValue L box cc.1 du).map (max m)) (some (-1))
  else none

inductive Tree where
  | split (k : ℕ) (mid : ℤ) (left right : Tree)
  | node (orders : List ℕ) (certs : List CaseCert)

def verifyTree (L : Leaf) : Tree → List (ℤ × ℤ) → Option ℤ
  | .split k mid l r, box =>
    match box[k]? with
    | some (a, b) =>
      if a < mid ∧ mid < b then
        (verifyTree L l (box.set k (a, mid))).bind fun m₁ =>
          (verifyTree L r (box.set k (mid, b))).map (max m₁)
      else none
    | none => none
  | .node orders certs, box =>
    (checkBox L box orders certs).bind fun v => if v < S then some v else none

def wellFormed (L : Leaf) :=
  L.cols.all (fun col => col.v.length = L.rows.length && col.D.length = L.rows.length &&
    col.D.all fun x => decide (0 < x)) &&
  L.rows.all fun r => decide (0 < r.d) &&
    r.fam.all fun t => decide (0 ≤ t.1) && decide (0 < t.2.2)

def rootBox (L : Leaf) := L.rows.map fun r => ((0 : ℤ), rootEnd r.d)

def checkLeaf (L : Leaf) T :=
  if wellFormed L then verifyTree L T (rootBox L) else none

def rowLHS (L : Leaf) (x : _ → ℝ) k (τ : ℝ) :=
  ∑ j, x j * max 0 ((L.cols.get j).v.getD k 0 / S - τ) ^ 2 /
      ((L.cols.get j).D.getD k 1 / S) +
    ((L.rows.getD k ⟨1, []⟩).fam.map fun t =>
      t.1 * max 0 (t.2.1 / S - τ) ^ 2 / (t.2.2 / S)).sum

def Feasible (L : Leaf) (x : _ → ℝ) (τ : _ → ℝ) :=
  (∀ j, 0 ≤ x j) ∧
  (∑ j, (L.cols.get j).W * x j ≤ L.F) ∧
  (∑ j, (L.cols.get j).C * x j ≤ 2 * S) ∧
  (∑ j, (L.cols.get j).NH * x j ≤ L.ng * S) ∧
  (∑ j, (L.cols.get j).E * x j = L.n2 * S) ∧
  ∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ (L.rows.getD k ⟨1, []⟩).d / S ∧
    rowLHS L x k (τ k) ≤ 1 - τ k ^ 2 / ((L.rows.getD k ⟨1, []⟩).d / S)

def objective (L : Leaf) (x : _ → ℝ) :=
  L.first + L.final + ∑ j, (L.cols.get j).G * x j

end Cert

end GradedNear
