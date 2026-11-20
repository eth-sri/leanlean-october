/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Hilbert

@[expose] public section

namespace OAI.EuclideanRamsey

universe uIndex

noncomputable section

abbrev LetterGroup := FreeGroup Hilbert
variable {ι : Type uIndex}

def CopyPath (a : ι → Hilbert) (u : ℝ) (b : ι → Hilbert) : Prop :=
  0≤u ∧ ∀ i j,‖b i-b j‖^2=u*‖a i-a j‖^2

inductive Path (a : ι → Hilbert) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → Hilbert) (h : CopyPath a u b) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u*v) (lmb+μ)
lemma Path.mul_diag {a : ι → Hilbert} {u m} (h : Path a u m) (g : LetterGroup) :
    Path a (fun i => u i * g) m := by simpa only [Pi.mul_def,add_zero] using h.mul (.diag g)

lemma Path.diag_mul {a : ι → Hilbert} {u m} (h : Path a u m) (g : LetterGroup) :
    Path a (fun i => g * u i) m := by simpa only [Pi.mul_def,zero_add] using (Path.diag g).mul h

lemma Path.nonneg {a : ι → Hilbert} {w u} (h : Path a w u) : 0 ≤ u := by
  induction h with
  | diag => exact le_rfl
  | copy _ h => exact h.1
  | mul _ _ h h' => exact add_nonneg h h'

lemma Path.pair_inverse {a : ι → Hilbert} {u : ι → LetterGroup} {lmb : ℝ}
    (h : Path a u lmb) (i j : ι) : ∃ v, Path a v lmb ∧ v i=(u i)⁻¹ ∧ v j=(u j)⁻¹ := by
  induction h with
  | diag g => exact ⟨_,.diag g⁻¹,rfl,rfl⟩
  | copy b hb =>
    let c (k : ι) := b i + b j - b k
    have hc : CopyPath a _ c := ⟨hb.1, fun k l => by
      simpa [c, sub_sub_sub_cancel_left, norm_sub_rev] using hb.2 k l⟩
    refine ⟨_,((Path.copy c hc).diag_mul (FreeGroup.of (b i))⁻¹).mul_diag (FreeGroup.of (b j))⁻¹, ?_, ?_⟩ <;> simp [c]
  | mul _ _ ihu ihv =>
    obtain ⟨u',hu',hui,huj⟩ := ihu
    obtain ⟨v',hv',hvi,hvj⟩ := ihv
    exact ⟨v'*u',by simpa only [add_comm] using hv'.mul hu',by simp [hui,hvi],by simp [huj,hvj]⟩

def LetterDifferences (X : Type*) : Subgroup (FreeGroup X) :=
  Subgroup.normalClosure (Set.range fun p : X × X => FreeGroup.of p.1 * (FreeGroup.of p.2)⁻¹)
instance (X : Type*) : (LetterDifferences X).Normal := Subgroup.normalClosure_normal
lemma letter_difference_mem {X : Type*} (x y : X) : FreeGroup.of x * (FreeGroup.of y)⁻¹ ∈ LetterDifferences X :=
  Subgroup.subset_normalClosure ⟨(x,y),rfl⟩

/-- A scaled copy can realize any letter difference at one endpoint and fix the other. -/
lemma pair_difference (a : ι → Hilbert) (ha : Function.Injective a)
    {i j : ι} (hij : i ≠ j) (x y : Hilbert) :
    ∃ v m, Path a v m ∧ v i = FreeGroup.of x * (FreeGroup.of y)⁻¹ ∧ v j = 1 := by
  let t := ‖y-x‖/‖a j-a i‖
  let v := t • (a j-a i)
  let R := (ℝ ∙ (v-(y-x)))ᗮ.reflection
  have he : ‖y-x‖ = ‖v‖ := by
    simp [v,t,norm_smul,sub_ne_zero.mpr (ha.ne hij.symm)]
  have hR : R v = y-x := Submodule.reflection_sub he.symm
  let b (l : ι) := x + R (t • (a l-a i))
  have hc : CopyPath a (t^2) b := ⟨sq_nonneg _,fun k l => by
    simp only [b,add_sub_add_left_eq_sub,← map_sub,LinearIsometryEquiv.norm_map,← smul_sub,sub_sub_sub_cancel_right,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]⟩
  exact ⟨_,t^2,(Path.copy b hc).mul_diag (FreeGroup.of y)⁻¹,by simp [b],by change FreeGroup.of (x+R v) * _ = _; simp [hR]⟩

abbrev Strings := FreeMonoid Hilbert

variable {ι : Type uIndex}
def StringFamily (a : ι → Hilbert) (u : ℝ) (x : ι → Strings) : Prop :=
  (∀ i j,(x i).toList.length=(x j).toList.length) ∧
  ∀ i j,‖Hilbert.flatten (x i).toList - Hilbert.flatten (x j).toList‖^2=u*‖a i-a j‖^2
lemma StringFamily.mul {a : ι → Hilbert} {u v : ℝ} {x y : ι → Strings}
    (hx : StringFamily a u x) (hy : StringFamily a v y) : StringFamily a (u+v) (x*y) := by
  refine ⟨fun i j => ?_,fun i j => ?_⟩
  · simp [Pi.mul_apply,hx.1 i j,hy.1 i j]
  · simp [Pi.mul_apply,Hilbert.flatten_append_dist _ _ _ _ (hx.1 i j),hx.2 i j,hy.2 i j,add_mul]

end
end OAI.EuclideanRamsey
