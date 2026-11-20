module
public import OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint

@[expose] public section

namespace OAI.SevenEighths.ProbeHighRowFamily
noncomputable section
open scoped BigOperators ContDiff
open Set HeckeFamily ProbeRaySlots
local notation "O" => HeckeFamily.O

/-- Positivity and ranges of the smoothing, detector and row scales. -/
abbrev WithProbeScales (e eps c b A R dmin dmax rmin τ ε κ cost mesh : ℝ) (P : (0<mesh) → Prop) : Prop :=
  ∀ (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh), P hmesh

/-- The spacing, height and loss allowances for the detector. -/
abbrev WithProbeScaleMargins (e R dmin rmin τ ε κ cost mesh margin eps loss : ℝ) (P : Prop) : Prop :=
  ∀ (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss), P

/-- Admissible real test weights and the exponents of their slot heights. -/
abbrev WithPositiveProbeSlots (N : ℕ) (dmin dmax rmin R c b A : ℝ) (P : (Fin N → ℝ) → (Fin N → ℝ → ℝ) → Prop) : Prop :=
  ∀ (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6), P ell W

/-- Admissible complex test weights and the exponents of their slot heights. -/
abbrev WithComplexProbeSlots (N : ℕ) (dmin dmax rmin R c b A : ℝ) (P : (Fin N → ℝ) → (Fin N → ℝ → ℂ) → Prop) : Prop :=
  ∀ (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6), P ell W

/-- Two positive test profiles in the pole-normalizing integral. -/
abbrev WithPositiveResidueTests (P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0), P W0 W1 a0 b0 a1 b1

/-- Additional range and window inequalities at final assembly. -/
abbrev WithAssemblyMargins (dmin dmax τ ε e κ cost : ℝ) (P : Prop) : Prop :=
  ∀ (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2), P

variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem rayPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end
end OAI.SevenEighths.ProbeHighRowFamily
