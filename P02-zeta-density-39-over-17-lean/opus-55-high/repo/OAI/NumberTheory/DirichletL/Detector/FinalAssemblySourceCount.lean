module
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

section
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (_hH : RayOrthogonality.globalUnits M≤H) (_S : Finset (Ideal O)) (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ) (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0) (a₀ b₀ B₀ : ℝ) (_ha₀ : 0<a₀) (_hab₀ : a₀≤b₀) (_hB₀ : 0<B₀) (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤B₀) (εm : ℝ) (_hεm : 0<εm) (Label : Type) [Fintype Label] (N n : ℕ) (dmin dmax τ logCost heightCost momentCost binWidth : ℝ) (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ) (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm)
include M H _hH _S φ _hφ _hφc _hφp _hφ0 _hφne a₀ b₀ B₀ _ha₀ _hab₀ _hB₀ _hφs _hφB εm _hεm Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb counts
theorem balanced_source_count_from_raw_moments :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z ^d) a ε
        (cutoff (2*a-1) q) (Z ^τ) ((Z ^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z ^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z ^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cB counts.kB (C*Z ^momentCost) (Z ^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z ^(logCost+heightCost+momentCost)*(Z ^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.balanced
  pm_3863
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z ^τ) ((Z ^d)^(τ/(2*dmax))) Δ ν
    (C*Z ^momentCost) (Z ^heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z ^τ) ((Z ^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ C q : ℝ) (i : ℕ),i≤n → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z ^d) a ε
        (cutoff (2*a-1) q) (Z ^τ) ((Z ^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cH counts.kH (C*Z ^momentCost) (Z ^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z ^(logCost+heightCost+momentCost)*(Z ^d)^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.high
  pm_3863
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z ^τ) ((Z ^d)^(τ/(2*dmax))) Δ
    (C*Z ^momentCost) (Z ^heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z ^τ) ((Z ^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)
end

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z ^d) a ε
        (cutoff (2*a-1) q) (Z ^τ) ((Z ^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z ^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z ^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*Z ^momentCost) (Z ^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z ^(logCost+heightCost+momentCost)*(Z ^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  pm_5032 KB hKB hbalanced balanced_source_count_from_raw_moments
  pm_5032 KH hKH hhigh high_source_count_from_raw_moments
  pm_6548 KB KH hKB
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [ite_eq_left hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    pm_7943 ite_eq_left le_max_left
  · simp only [ite_eq_right hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    pm_7943 ite_eq_right le_max_right

end SevenEighths.ProbeFinalAssembly


end OAI
