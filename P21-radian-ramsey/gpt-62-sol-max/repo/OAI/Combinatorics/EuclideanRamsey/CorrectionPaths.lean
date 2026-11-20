/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.OrbitAveraging

@[expose] public section

namespace OAI.EuclideanRamsey
open Finset
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma bounded_tuple (a : ι → Hilbert) (g : ι → LetterGroup) (c : ℝ)
    (h : ∀ i, PartialBound a Finset.univ (Pi.mulSingle i (g i)) c) :
    PartialBound a univ g (Fintype.card ι * c) := by
  suffices ∀ s : Finset ι, PartialBound a univ (s.piecewise g 1) (s.card * c) by simpa using this univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (PartialBound.one (a:=a) (s:=univ))
  | @insert i s hi ih =>
    have he : (insert i s).piecewise g 1 = s.piecewise g 1 * Pi.mulSingle i (g i) := by
      ext j
      by_cases hj : j = i <;> simp_all
    simpa [he,card_insert_of_notMem hi,add_mul] using ih.mul_single (h i)

private abbrev permute {σ : Type*} [Fintype σ] (e : Equiv.Perm σ) : EuclideanSpace ℝ σ ≃ₗᵢ[ℝ] EuclideanSpace ℝ σ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

theorem permutation_equal_endpoints {s d : ℕ} {τ : Type*} [Fintype τ] (a : Fin s → Space d)
    (ha : Function.Injective a) (f g : Fin s → EuclideanSpace ℝ τ)
    (Q q δ : ℝ) (hQ : 0 < Q) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hf : ∀ i j, ‖f i-f j‖^2=Q*‖a i-a j‖^2)
    (hg : ∀ i j, ‖g i-g j‖^2=q*‖a i-a j‖^2)
    (hperm : ∀ i, ∃ σ : Equiv.Perm τ, ∀ x, g i (σ x)=f i x) :
    ∃ w lmb μ, Path (fun i => Hilbert.embed (Fin d) (a i)) w lmb ∧
      Path (fun i => Hilbert.embed (Fin d) (a i)) w μ ∧ 0 < lmb ∧ μ/lmb ≤ (q+s*δ)/Q := by
  classical
  choose σ hσ using hperm
  let z (h : Equiv.Perm τ) (i : Fin s) := Hilbert.embed τ (permute h (f i))
  have he (h : Equiv.Perm τ) (i : Fin s) : z (h*σ i) i = Hilbert.embed τ (permute h (g i)) := by
    change Hilbert.embed τ (permute (h*σ i) (f i)) = Hilbert.embed τ (permute h (g i))
    apply congrArg (Hilbert.embed τ)
    ext j
    change f i ((σ i).symm (h.symm j)) = g i (h.symm j)
    grind
  let A i := Hilbert.embed (Fin d) (a i)
  have hf' (h) : CopyPath A Q (z h) := ⟨hQ.le,fun i j => by simp [A,z,← map_sub,hf]⟩
  have hg' (h) : CopyPath A q (fun i => z (h*σ i) i) := ⟨hq,fun i j => by simp [A,he,← map_sub,hg]⟩
  let N := LetterDifferences Hilbert
  let L := Derived N (s-2)
  have hL (i : Fin s) : L ≤ Correctable A Finset.univ i :=
    by simpa [A,L,N,Function.comp_def] using derived_subset_single ((Hilbert.embed (Fin d)).injective.comp ha) (Finset.mem_univ i)
  let c := normalBound A univ
  obtain ⟨w,m,hw,hm,hwm⟩ := averaging N (s-2)
    c (fun i _ h => hL i h) (fun h i => FreeGroup.of (z h i)) (fun i h k => letter_difference_mem _ _) δ hδ
  let p i := w 1 i
  let n i := w (σ i) i
  have hp : Path A p (Q*m) := by
    simpa using hw.path (fun _ => 1) Q (fun h => by simpa using Path.copy _ (hf' h)) 1
  have hn : Path A n (q*m) := by simpa using hw.path σ q (fun h => by simpa using Path.copy _ (hg' h)) 1
  let r := p⁻¹*n
  have hr (i : Fin s) : (c i).Holds (δ*m) (r i) := by
    simpa [r,p,n,mul_assoc] using (c i).conj (hwm i (σ i) 1) (w 1 i)⁻¹
  obtain ⟨u,v,b,e,hu,hv,he,hbe⟩ := bounded_tuple A r (δ*m) hr
  have he' : r = u*v⁻¹ := funext (fun i => he i (Finset.mem_univ i))
  have heq : p*u=n*v := by
    simpa [r,mul_assoc] using congrArg (fun t => p*t*v) he'.symm
  have hm' : 0 < Q*m+b := add_pos_of_pos_of_nonneg (mul_pos hQ hm) hu.nonneg
  refine ⟨_,_,_,hp.mul hu,heq ▸ hn.mul hv,hm',(div_le_iff₀ hm').mpr ?_⟩
  rw [div_mul_eq_mul_div,le_div_iff₀ hQ]
  rw [Fintype.card_fin] at hbe
  have hb := hu.nonneg
  nlinarith only [mul_le_mul_of_nonneg_right hbe hQ.le,
    mul_nonneg hQ.le hb, mul_nonneg (show 0 ≤ q+s*δ by positivity) hb]

end
end OAI.EuclideanRamsey
