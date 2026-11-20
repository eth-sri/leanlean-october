module
public import LaterPairs.Native.HuxleyProfileGeometry

@[expose] public section

noncomputable section
namespace TaoTrudgianYang2025.HuxleyRationalPhase

/-- Anisotropic radii for the two arithmetic and two real completion coordinates. -/
abbrev cubicCompletionRadius (K : ℝ) : Fin 4 → ℝ :=
  ![1/(12*K),1/(12*K^2),(1/K^2)/12,(1/K)/12]

/-- Dual coefficient of the completed cubic phase. -/
abbrev cubicDualPhase (m q : ℝ) : ℝ :=
  -2*m*(Real.sqrt (2/(3*m*q)))^3

/-- The normalized four-dimensional frequency cloud for a completed cubic sum. -/
abbrev cubicCompletion (v b q d τ K : ℝ) : Fin 4 → ℝ :=
  ![Int.fract (-v*b/q),Int.fract (-v/q),d/Real.sqrt K,(3*d*τ/2)/Real.sqrt K]

/-- The corresponding unnormalized phase coordinates. -/
abbrev cubicCoordinates (v b q d τ : ℝ) : Fin 4 → ℝ :=
  ![-v*b/q,-v/q,d,3*d*τ/2]

/-- A rectangular bin in reduced denominator and numerator for the source rational. -/
abbrev rationalSourceBin (Q slope θ : ℝ) (r : ℚ) : ℤ × ℤ :=
  (⌊(r.den:ℝ)/(θ*(Q/2))⌋,⌊(r.num:ℝ)/(θ*(slope*Q/2))⌋)

/-- Chart bin of the shift, rational slope and reciprocal slope. -/
abbrev phaseChartBin (a T M y r : ℝ) : ℤ × ℤ × ℤ :=
  (⌊y/a⌋,⌊((2*M^2/T)*r)/a⌋,⌊((T/(2*M^2))*r⁻¹)/a⌋)

/-- First difference normalized to the model-phase scale. -/
abbrev firstDifferenceModel (F : ℝ → ℝ) (Tsrc T σ η y u : ℝ) : ℝ :=
  (Tsrc/T)*(F u-F (u+η*y))/(σ*η)

/-- The first difference on the physical interval. -/
abbrev physicalFirstDifference (F : ℝ → ℝ) (T M σ η y w : ℝ) : ℝ :=
  T*(F (w/M)-F (w/M+η*y))/(σ*η)

/-- A common upper constant for cubic scales and their reciprocals. -/
abbrev cubicScaleMajorant (J c : ℝ) : ℝ :=
  max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))

/-- Taylor error constant from the rational chart change. -/
abbrev quarticTaylorSlack (B Cc Ct : ℝ) : ℝ :=
  37*B/2+16*B*Cc+2*Ct+2*Cc

/-- The full quartic remainder budget, including the nonlinear residual. -/
abbrev quarticResidualBudget (σ δ B Cc Ct : ℝ) : ℝ :=
  quarticTaylorSlack B Cc Ct+2*quarticNonlinearResidualConstant σ δ

/-- Packing constant in the cubic coordinate comparison. -/
abbrev quarticPackingMoment (C G K J κ : ℝ) : ℝ :=
  64*C*(G^2*K+G*J/κ)/κ

/-- Uniform Taylor, residual, and packing constants for a quartic chart.
The only dependence on the two mesh sizes is in `delta` and `error`. -/
structure QuarticChartBudget where
  (C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird : ℝ)
  (Cpack Cfirst Cgap Cmain Ctail slack nonlinear : ℝ)

abbrev QuarticChartBudget.make (σ δ κ C B : ℝ) : QuarticChartBudget :=
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  let recip := quarticReciprocalConstant σ δ
  let nonlin := quarticNonlinearResidualConstant σ δ
  let slack := quarticTaylorSlack B Cc Ct
  let Dbase := quarticResidualBudget σ δ B Cc Ct
  let Kres := 4*Dbase/κ
  let Lunit := 2*κ/C
  let Gamma := C/κ
  let Cthird := Gamma*(32*Kres+9*recip)
  let Cpack := quarticPackingMoment C Gamma Cthird C₃ κ
  let Cfirst := 128*C*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
  let Cgap := quarticPackingMoment C Gamma B C₃ κ
  ⟨C₂,C₃,Ct,Cc,(4/κ)*(B+2*recip),Kres,κ/(16*(C+2)),Dbase,(2/κ)*(B+2*recip),
    Lunit,Gamma,Cthird,Cpack,Cfirst,Cgap,4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2,
    4*Cpack/Lunit^2+Cgap,slack,nonlin⟩

abbrev QuarticChartBudget.delta (b : QuarticChartBudget) (Q N : ℝ) : ℝ := b.slack*Q/N

abbrev QuarticChartBudget.error (b : QuarticChartBudget) (Q N : ℝ) : ℝ :=
  b.delta Q N+b.nonlinear*(2*Q)/N

/-- The oriented unimodular bases of the reference gaps, with separated endpoint set. -/
abbrev WithReferenceBasis
    (Gaps : Finset (ℝ × ℝ)) (Refs : Finset ℝ)
    (e r v s : ℝ × ℝ → ℤ) (Uref : ℕ) (R Bcut : ℝ) (P : Prop) : Prop :=
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    P

/-- Scale inequalities for the long-gap selection from a reference sector. -/
abbrev WithReferenceScale
    (Gaps : Finset (ℝ × ℝ)) (r : ℝ × ℝ → ℤ) (Uref Q : ℕ)
    (κ Bcut Bselect M N R : ℝ) (P : Prop) : Prop :=
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) →
    (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    P

/-- Numerator and denominator bounds for the matrices of the reference chart. -/
abbrev WithReferenceCoefficientBounds
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ)
    (Uref : ℕ) (Jref T σ M R : ℝ) (P : Prop) : Prop :=
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    P

/-- Rounded jets of a pair of model phases at the rational sample points. -/
abbrev WithRoundedSourceJets {ι : Type*} (S : Finset ι)
    (F : Fin 2 → ℝ → ℝ) (A : Fin 2 → ℝ) (T M : ℝ)
    (x : ι → Fin 2 → ℝ) (rat : ι → Fin 2 → ℚ)
    (P : (Fin 2 → ℝ → ℝ) → (ι → Fin 2 → ℕ) → (ι → Fin 2 → ℝ) → (ι → Fin 2 → ℝ) → Prop) : Prop :=
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    P f q mu ell

/-- The two compatible completions, with the coordinates in the same small box. -/
abbrev WithCompletionCloud
    {ι : Type*} (S : Finset ι) (q : ι → Fin 2 → ℕ) (mu ell : ι → Fin 2 → ℝ)
    (parity : ι → Fin 2 → Fin 2) (vinv : ι → Fin 2 → ℤ) (K₀ : ℕ)
    (P : (ι → Fin 2 → ℤ) → (ι → Fin 2 → ℤ) → (ι → Fin 2 → ℝ) →
      (ι → Fin 2 → ℝ) → (ι → Fin 2 → Fin 4 → ℝ) → (Fin 4 → ℝ) → Prop) : Prop :=
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => cubicDualPhase (mu j i) (q j i)
    let cloud := fun j i => cubicCompletion (vinv j i) (b j i) (q j i) (dual j i) (tau j i) K₀
    let radius : Fin 4 → ℝ := cubicCompletionRadius K₀
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    P b cround tau dual cloud radius

/-- Scale restrictions used for the cubic completion. -/
abbrev WithCubicScales
    (σ M N R : ℝ) (Q : ℕ) (P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := cubicScaleMajorant J c
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    P κ Cphys c J B

/-- The unimodular action on the two rationals, with a bound on its lower entry. -/
abbrev WithCompletionMatrices
    {ι ι' : Type*} [DecidableEq ι'] (S : Finset ι) (entry : ι → ι') (Mat : ι' → Fin 4 → ℤ)
    (rat : ι → Fin 2 → ℚ) (q : ι → Fin 2 → ℕ) (Q K₀ : ℕ) (P : Prop) : Prop :=
    (∀ t∈S.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ j∈S, (Mat (entry j) 2:ℝ)*(rat j 0:ℝ)+Mat (entry j) 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat (entry j) 0:ℝ)*(rat j 0:ℝ)+Mat (entry j) 1)/
      ((Mat (entry j) 2:ℝ)*(rat j 0:ℝ)+Mat (entry j) 3)=(rat j 1:ℝ)) →
    (∀ t∈S.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    P

/-- The endpoints of rational selection windows and their denominator constraints. -/
abbrev WithRationalAnchors
    {ι : Type*} (S : Finset ι) (rat : ι → Fin 2 → ℚ) (anchor : ι → ℚ)
    (ε : ℝ) (Q : ℕ) (P : Prop) : Prop :=
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    P

/-- The source intervals contain the two shifted points around each sample. -/
abbrev WithCompletionMargins
    {ι : Type*} (S : Finset ι) (x : ι → Fin 2 → ℝ) (W : Fin 2 → ℝ)
    (N Cphys : ℝ) (P : ℝ → Prop) : Prop :=
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Set.Ioo (1/2:ℝ) (W i-1/2)) →
    P H

end TaoTrudgianYang2025.HuxleyRationalPhase
