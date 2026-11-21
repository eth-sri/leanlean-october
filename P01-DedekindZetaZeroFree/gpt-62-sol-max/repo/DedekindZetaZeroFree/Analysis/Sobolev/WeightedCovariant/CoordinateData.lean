module

public import DedekindZetaZeroFree.Analysis.EquivariantSections.WeightedL2.SmoothDensity
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace

abbrev E (n : ℕ) := KPContLocalNorm.Space n

abbrev V (r : ℕ) := EuclideanSpace ℂ (Fin r)

def coordinateDirection {n : ℕ} (j : Fin n) : E n :=
  EuclideanSpace.single j 1

def coordinatePartial {n : ℕ} (j : Fin n) (ψ : E n → ℂ) (x : E n) : ℂ :=
  fderiv ℝ ψ x (coordinateDirection j)

def LocallyL2 {n r : ℕ} (Ω : Opens (E n)) (f : E n → V r) : Prop :=
  AEStronglyMeasurable f (volume.restrict (Ω : Set (E n))) ∧
    ∀ L : Set (E n), IsCompact L → L ⊆ (Ω : Set (E n)) →
      MemLp f 2 (volume.restrict L)

structure WeakFirst {n r : ℕ} (Ω : Opens (E n))
    (f : E n → V r) (g : Fin n → E n → V r) : Prop where
  section_locallyL2 : LocallyL2 Ω f
  derivative_locallyL2 : ∀ j, LocallyL2 Ω (g j)
  weak_identity : ∀ (j : Fin n) (ψ : TestFunction Ω ℂ ⊤) (a : Fin r),
    (∫ x in (Ω : Set (E n)), (f x) a * coordinatePartial j (fun y => ψ y) x) =
      -(∫ x in (Ω : Set (E n)), (g j x) a * ψ x)

structure InverseMetric {n : ℕ} (Ω : Opens (E n)) where
  Q : E n → Matrix (Fin n) (Fin n) ℝ
  smooth : ∀ j k, ContDiffOn ℝ ∞ (fun x => Q x j k) (Ω : Set (E n))
  symmetric : ∀ x ∈ (Ω : Set (E n)), ∀ j k, Q x j k = Q x k j
  positive_definite : ∀ x ∈ (Ω : Set (E n)), (Q x).PosDef

structure Connection {n r : ℕ} (Ω : Opens (E n)) where
  A : Fin n → E n → (V r →L[ℂ] V r)
  smooth : ∀ j, ContDiffOn ℝ ∞ (A j) (Ω : Set (E n))

def Connection.IsUnitary {n r : ℕ} {Ω : Opens (E n)}
    (A : Connection (r := r) Ω) : Prop :=
  ∀ x ∈ (Ω : Set (E n)), ∀ j,
    ContinuousLinearMap.adjoint (A.A j x) = -A.A j x

def covariantFirst {n r : ℕ} {Ω : Opens (E n)}
    (A : Connection (r := r) Ω) (f : E n → V r)
    (g : Fin n → E n → V r) (j : Fin n) (x : E n) : V r :=
  g j x + A.A j x (f x)

def InverseMetric.quadratic {n r : ℕ} {Ω : Opens (E n)}
    (Q : InverseMetric Ω) (x : E n) (d : Fin n → V r) : ℝ :=
  ∑ j, ∑ k, Q.Q x j k * Complex.re ⟪d j, d k⟫_ℂ


def FiniteH0 {n r : ℕ} (S : Set (E n)) (f : E n → V r)
    (g : Fin n → E n → V r) : Prop :=
  MemLp f 2 (volume.restrict S) ∧ ∀ j, MemLp (g j) 2 (volume.restrict S)

def l2Norm {n r : ℕ} (μ : Measure (E n)) (f : E n → V r)
    (_hf : MemLp f 2 μ) : ℝ :=
  Real.sqrt (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ)

def H0 {n r : ℕ} (S : Set (E n)) (f : E n → V r)
    (g : Fin n → E n → V r) (h : FiniteH0 S f g) : ℝ :=
  l2Norm (volume.restrict S) f h.1 +
    Real.sqrt (∑ j, (l2Norm (volume.restrict S) (g j) (h.2 j)) ^ 2)



def chartOpens {n r : ℕ} {Γ : Type*} [Group Γ] (D : KPChartL2.Data n r Γ) :
    Opens (E n) :=
  ⟨D.chart, D.open_chart⟩

def InverseMetric.IsInvariant {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (Q : InverseMetric (chartOpens D)) : Prop :=
  ∀ (γ : Γ) (x : E n), x ∈ D.chart → ∀ T : E n →L[ℝ] V r,
    Q.quadratic x (fun j => T (fderiv ℝ (D.act γ) x (coordinateDirection j))) =
      Q.quadratic (D.act γ x) (fun j => T (coordinateDirection j))


end DedekindZetaZeroFree.KPCompactInteriorH1

end
