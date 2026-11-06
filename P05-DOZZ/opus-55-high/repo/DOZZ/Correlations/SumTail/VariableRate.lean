/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Recover a point-dependent error ceiling from uniform strict-exponent estimates. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

/-- Compact localization keeps the variable ceiling, losing only the prescribed slack. -/
theorem sumtail_uniform_variable_rate
    {A S : Type*} [TopologicalSpace A] (K : Set A) (hK : IsCompact K)
    (e p : A → ℝ) (he : ContinuousOn e K) (hepos : ∀ a ∈ K, 0 < e a)
    (err : A → S → ℝ → ℝ)
    (hfixed : ∀ L : Set A, IsCompact L → L ⊆ K →
      ∀ η : ℝ, 0 < η → (∀ a ∈ L, η < e a) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ L, ∀ s : S, ∀ x : ℝ, 1 ≤ x →
          err a s x ≤ C*x^(-p a-η))
    (d : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ s : S, ∀ x : ℝ, 1 ≤ x →
      err a s x ≤ C*x^(-p a-e a+d) := by
  let _ := isCompact_iff_compactSpace.mp hK
  have hec : Continuous (fun a : K => e a) := continuousOn_iff_continuous_domRestrict.mp he
  let δ (i : K) := min (d/4) (e i/4)
  have hδ (i : K) : 0 < δ i := by aesop
  let η (i : K) := e i-2*δ i
  have hη (i : K) : 0 < η i := by
    grind
  let V (i : K) : Set K := {a | |e a-e i| ≤ δ i}
  let L (i : K) : Set A := Subtype.val '' V i
  have hLc (i : K) : IsCompact (L i) := by
    have hv : IsClosed (V i) := isClosed_le (hec.sub continuous_const).abs continuous_const
    exact hv.isCompact.image continuous_subtype_val
  have hLs (i : K) : L i ⊆ K := by grind
  have hηe (i : K) a (ha : a ∈ L i) : η i < e a := by
    obtain ⟨b,hb,rfl⟩ := ha
    change |e b-e i| ≤ δ i at hb
    dsimp [η]
    linarith only [((abs_le.mp hb).1),(hδ i)]
  have hlocal (i : K) := hfixed (L i) (hLc i) (hLs i) (η i) (hη i) (hηe i)
  choose C hC hCb using hlocal
  let U (i : K) : Set K := {a | |e a-e i| < δ i}
  have hU (i : K) : IsOpen (U i) := isOpen_lt (hec.sub continuous_const).abs continuous_const
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro a _
    exact mem_iUnion.mpr ⟨a,by grind⟩)
  refine ⟨∑ i ∈ I, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro a ha s x hx
  let aa : K := ⟨a,ha⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hI (mem_univ aa))
  obtain ⟨hiI,hui⟩ := mem_iUnion.mp hi
  change |e aa-e i| < δ i at hui
  have hla : a ∈ L i := ⟨aa,hui.le,rfl⟩
  have hrate : -p a-η i ≤ -p a-e a+d := by
    linarith only [((abs_le.mp hui.le).2),(min_le_left (d/4) (e i/4)),hd]
  exact (hCb i a hla s x hx).trans (mul_le_mul
    (Finset.single_le_sum (fun j _ => hC j) hiI) (Real.rpow_le_rpow_of_exponent_le hx hrate)
    (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg (fun j _ => hC j)))

end DOZZ.Proofs
