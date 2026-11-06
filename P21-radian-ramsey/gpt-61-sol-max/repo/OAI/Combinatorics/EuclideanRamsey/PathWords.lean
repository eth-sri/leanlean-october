/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.DerivedFractions

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section




abbrev LetterGroup := FreeGroup FiniteEuclidean
variable {ι : Type*}

def CopyPath (a : ι → FiniteEuclidean) (u : ℝ) (b : ι → FiniteEuclidean) : Prop :=
  0≤u ∧ ∀ i j,‖b i-b j‖^2=u*‖a i-a j‖^2

inductive Path (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u*v) (lmb+μ)
def unitGraded (a : ι → FiniteEuclidean) : GradedPaths ι LetterGroup where
  Holds w n := Path a w n
  diag g := by simpa using Path.diag (a:=a) g
  mul h h' := by simpa using h.mul h'

lemma extend_pair_E (a : ι → FiniteEuclidean) (i j : ι) (z z' : FiniteEuclidean)
    (h : ‖z'-z‖=‖a j-a i‖) :
    ∃ b : ι → FiniteEuclidean,b i=z ∧ b j=z' ∧ ∀ k l,‖b k-b l‖=‖a k-a l‖ := by
  let v := a j-a i
  let w := z'-z
  let R := (ℝ ∙ (v-w))ᗮ.reflection
  refine ⟨fun k => z+R (a k-a i),by simp,?_,?_⟩
  · have he  := Submodule.reflection_sub h.symm
    aesop
  · intro k l
    simp [← map_sub]

lemma unit_pair_inverse (a : ι → FiniteEuclidean) : PairInverse (unitGraded a).monoid := by
  intro i j u ⟨m, hm⟩
  have aux {u lmb} (h : Path a u lmb) :
      ∃ v, Path a v lmb ∧ v i=(u i)⁻¹ ∧ v j=(u j)⁻¹ := by
    induction h with
    | diag g => exact ⟨_,.diag g⁻¹,rfl,rfl⟩
    | @copy lmb b hb =>
      obtain ⟨c,hci,hcj,hc⟩ := extend_pair_E b i j (b j) (b i) (norm_sub_rev _ _)
      let x := FreeGroup.of (b i)
      let y := FreeGroup.of (b j)
      refine ⟨(fun _ => x⁻¹)*(fun k => FreeGroup.of (c k))*(fun _ => y⁻¹),?_,?_,?_⟩
      · simpa using ((Path.diag x⁻¹).mul (.copy c ⟨hb.1,by simp [hc, hb.2]⟩)).mul (.diag y⁻¹)
      · simp [x,y,hci]
      · simp [x,y,hcj]
    | mul _ _ ihu ihv =>
      obtain ⟨u',hu',hui,huj⟩ := ihu
      obtain ⟨v',hv',hvi,hvj⟩ := ihv
      exact ⟨v'*u',by simpa [add_comm] using hv'.mul hu',by simp [hui,hvi],by simp [huj,hvj]⟩
  obtain ⟨v, hv, hi, hj⟩ := aux hm
  exact ⟨v,⟨m,hv⟩,hi,hj⟩

lemma unit_pair_coverage (a : ι → FiniteEuclidean) (ha : Function.Injective a) :
    PairCoverage (unitGraded a).monoid (AugKernel FiniteEuclidean) := by
  classical
  intro i j hij g hg h hh
  let Q : Subgroup (LetterGroup×LetterGroup) := {
    toSubmonoid := (unitGraded a).monoid.map ((Pi.evalMonoidHom _ i).prod (Pi.evalMonoidHom _ j))
    inv_mem' := by
      rintro _ ⟨u,hu,rfl⟩
      obtain ⟨v,hv,hi,hj⟩ := unit_pair_inverse a i j u hu
      exact ⟨v,hv,Prod.ext hi hj⟩ }
  have diag g : (g,g)∈Q :=
    ⟨_,(unitGraded a).diagonal g,rfl⟩
  let L := Q.comap (MonoidHom.inl LetterGroup LetterGroup)
  have : L.Normal := by
    constructor
    intro g hg k
    change (k*g*k⁻¹,1)∈Q
    simpa using Q.mul_mem (Q.mul_mem (diag k) hg) (diag k⁻¹)
  have edge x y (hxy : ‖x-y‖=‖a i-a j‖) :
      FreeGroup.of x*(FreeGroup.of y)⁻¹∈L := by
    obtain ⟨b,hbi,hbj,hb⟩ := extend_pair_E a i j x y (by
      simpa [norm_sub_rev y x, norm_sub_rev (a j) (a i)] using hxy)
    have hcopy : (FreeGroup.of x,FreeGroup.of y)∈Q := by
      refine ⟨(fun k => FreeGroup.of (b k)),⟨1,Path.copy b ⟨(by norm_num),by simp [hb]⟩⟩,?_⟩
      exact Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)
    have h := Q.mul_mem hcopy (diag (FreeGroup.of y)⁻¹)
    simpa [L] using h
  have hr := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hij (ha he)))
  have hle : AugKernel FiniteEuclidean≤L := by
    apply augmentation_kernel_le 0
    intro x y
    apply FiniteEuclidean.unit_distance_constant _ hr
      (fun z => (QuotientGroup.mk' (L)) (FreeGroup.of z))
    intro x y hxy
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv] using edge x y hxy
  have hleft := hle hg
  have hright : (1,h)∈Q := by
    have h := (Q).mul_mem (diag h)
      (hle ((AugKernel FiniteEuclidean).inv_mem hh))
    simpa using h
  have hp := (Q).mul_mem hleft hright
  simp_all [unitGraded, Q]


abbrev Strings := FreeMonoid FiniteEuclidean

def stringEnergy (l k : List FiniteEuclidean) : ℝ :=
  (List.zipWith (fun x y => ‖x-y‖^2) l k).sum
open FiniteEuclidean in
lemma flatten_energy (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖FiniteEuclidean.flatten l-FiniteEuclidean.flatten k‖^2=stringEnergy l k  := by
  trans ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2
  ·
    have he : flatten l-flatten k = ∑ i : Fin l.length,block i (l.get i-k.get (i.cast h)) := by
      unfold flatten
      have hk : (∑ i : Fin k.length,block i (k.get i))=
          ∑ i : Fin l.length,block i (k.get (i.cast h)) :=
        Fintype.sum_equiv (finCongr h).symm _ _ (by intro i; rfl)
      rw [hk,← Finset.sum_sub_distrib]
      congr! 1 with i _
      exact (map_sub (block i) _ _).symm
    rw [he]
    apply OrthogonalFamily.norm_sum (𝕜 := ℝ)
    intro i j hij x y
    exact inner_block_ne _ _ (Fin.val_injective.ne hij) x y
  · symm
    rw [stringEnergy, ← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp [h]
    · intro i hi hj
      simp

def StringFamily (a : ι → FiniteEuclidean) (u : ℝ) (x : ι → Strings) : Prop :=
  (∀ i j,(x i).toList.length=(x j).toList.length) ∧
  ∀ i j,stringEnergy (x i).toList (x j).toList=u*‖a i-a j‖^2
lemma StringFamily.common (a : ι → FiniteEuclidean) (x : Strings) :
    StringFamily a 0 (fun _ => x) := by constructor <;> intros <;> simp [stringEnergy]
lemma StringFamily.single {a : ι → FiniteEuclidean} {u : ℝ} {b : ι → FiniteEuclidean}
    (h : CopyPath a u b) : StringFamily a u (fun i => FreeMonoid.of (b i)) := by
  simpa [StringFamily, stringEnergy] using h.2

lemma StringFamily.mul {a : ι → FiniteEuclidean} {u v : ℝ} {x y : ι → Strings}
    (hx : StringFamily a u x) (hy : StringFamily a v y) : StringFamily a (u+v) (x*y) := by
  refine ⟨?_,?_⟩
  · intro i j
    change ((x i).toList++(y i).toList).length=((x j).toList++(y j).toList).length
    simp [hx.1 i j, hy.1 i j]
  · intro i j
    simpa [stringEnergy, List.zipWith_append (hx.1 i j), add_mul] using
      congrArg₂ (· + ·) (hx.2 i j) (hy.2 i j)
lemma StringFamily.congruent {a : ι → FiniteEuclidean} {x : ι → Strings}
    (h : StringFamily a 1 x) :
    ∀ i j,‖FiniteEuclidean.flatten (x i).toList-FiniteEuclidean.flatten (x j).toList‖=‖a i-a j‖ := by
  intro i j
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [flatten_energy _ _ (h.1 i j),h.2,one_mul]
end

end OAI.EuclideanRamsey
