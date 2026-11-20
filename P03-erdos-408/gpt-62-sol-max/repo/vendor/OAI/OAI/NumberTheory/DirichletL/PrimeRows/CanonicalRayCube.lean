module

public import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
public import OAI.NumberTheory.DirichletL.Detector.RayCharacterFamily
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def rayCubeFamily (u : FreeRow) : RayQuotient.Characters M H→Character :=
  HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse

theorem canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (mw : MellinWindows) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∃idx grid : FreeRow→ℕ,
      (∀ u, CubeBin (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (Z^τ) e n (idx u) (grid u)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) mw.left mw.right
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) mw.left mw.right (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          mw.left mw.right (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_probe_minus_cube (ι:=RayQuotient.Characters M H) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    mw
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ] with Z hZ η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨hZ,hZT⟩ := hZ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he n hn hwidth S hS.prime η (rayCubeFamily M H hH)
  refine ⟨idx, grid, hbins, ?_⟩
  apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
    (fun u=>51/100+e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx (rayCubeFamily M H hH)
  intro u _
  refine ⟨by linarith [mul_nonneg he.le (Nat.cast_nonneg (α:=ℝ) (grid u))], (hbins u).alpha_le_one, hZT, ?_, ?_, (hbins u).next⟩
  · push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (idx u)]
  · push_cast
    linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
