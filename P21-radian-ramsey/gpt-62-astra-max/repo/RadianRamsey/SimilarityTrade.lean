module
public import OAI.Combinatorics.EuclideanRamsey.PathWords
public import OAI.Combinatorics.EuclideanRamsey.SignedRows

@[expose] public noncomputable section
namespace RadianRamsey
open scoped TensorProduct ComplexConjugate

open OAI.EuclideanRamsey
def Trade {s} (z : Fin s → ℂ) (P Q : Rows) := ∀ i, P.map (value (z i)) = Q.map (value (z i))

structure AlgebraicCircle (z : Fin 9 → ℂ) : Prop where
  inj : Function.Injective z
  unit : ∀ i, Complex.normSq (z i) = 1
  alg : ∀ i, IsIntegral ℚ (z i)

/-! A sum of functions of distinct complex affine forms cannot be quadratic
by accident. Finite differences first bound their degrees (over ℚ); dilation
then extracts just the quadratic part. No regularity of the functions is assumed. -/

private def Degree : ℕ → (ℂ → ℝ) → Prop
  | 0, f => f = 0
  | n+1, f => ∀ u, Degree n (fwdDiff u f)

private lemma combine {n f g} (hf : Degree n f) (hg : Degree n g) (r : ℝ) : Degree n (f+r • g) := by
  induction n generalizing f g with
  | zero => simp_all [Degree]
  | succ n ih => intro u; aesop

private lemma lower {n f} (hf : Degree (n+1) f) (r : ℝ) :
    Degree n (fun x => r*(f (2*x) - 2^n * f x)) := by
  induction n generalizing f r with
  | zero =>
    funext x
    have h := congrFun (show fwdDiff x f = 0 from hf x) x
    simp [fwdDiff] at h; simp [two_mul,h]
  | succ n ih =>
    intro u
    have h := combine (ih (hf (2*u)) r) (hf u u) (r*2^n)
    convert h using 1
    ext x
    simp [fwdDiff]; ring_nf

variable {z : Fin 9 → ℂ}

private def Represents (z : Fin 9 → ℂ) (f : Fin 9 → ℂ → ℝ) :=
  ∀ a b, ∑ i, f i (b+a*z i) = Complex.normSq a

private lemma degree_of_rep {f} (rep : Represents z f) (hz : Function.Injective z) (i) : Degree 9 (f i) := by
  classical
  have elim (S : Finset (Fin 9)) (hi : i ∉ S) (g : Fin 9 → ℂ → ℝ) (p : ℂ → ℝ)
      (h : ∀ a b, ∑ k ∈ insert i S, g k (b+a*z k) = p a) : Degree (S.card+1) (g i) := by
    induction S using Finset.induction_on generalizing p g with
    | empty =>
      intro u; ext x
      have he x : g i x = p 0 := by simpa using h 0 x
      simp [fwdDiff,he]
    | @insert j S hj ih =>
      have hne : i ≠ j := by grind
      simp [hj]; intro u
      obtain ⟨v,rfl⟩ := mul_right_surjective₀ (sub_ne_zero.mpr (hz.ne hne)) u
      apply ih (by grind) (fun k => fwdDiff (v*(z k-z j)) (g k)) (fwdDiff v p)
      intro a b
      have he (c : ℂ) : b-v*z j+(a+v)*c = b+a*c+v*(c-z j) := by ring
      rw [Finset.insert_comm] at h
      simp [show j ∉ insert i S by grind] at h
      simp [fwdDiff,←h (a+v) (b-v*z j),←h a b,he]
  simpa using elim (Finset.univ.erase i) (by simp) f _ (by simpa [Represents] using rep)

private lemma truncate {n f} (h : Represents z f) (hf : ∀ i, Degree (n+1) (f i))
    (hc : (4-2^n:ℝ) ≠ 0) : ∃ g, Represents z g ∧ ∀ i, Degree n (g i) := by
  refine ⟨_,?_,fun i => lower (hf i) (4-2^n)⁻¹⟩
  intro a b
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, mul_add, ← mul_assoc,h _ _]
  simp; grind

/-- The polarization of a degree-at-most-two function is ℚ-bilinear. -/
private def polar (f : ℂ → ℝ) (x y : ℂ) := fwdDiff x (fwdDiff y f) 0

private def bilinear (f : ℂ → ℝ) (hf : Degree 3 f) : ℂ →ₗ[ℚ] ℂ →ₗ[ℚ] ℝ := by
  have hadd (x y t : ℂ) : polar f (x+y) t = polar f x t + polar f y t := by
    have h := congrFun (hf t x y) 0
    simp [polar, fwdDiff, add_comm x y] at *
    linarith
  have symm (x y) : polar f x y = polar f y x := by simp [polar, fwdDiff, add_comm]; ring
  exact (AddMonoidHom.mk' (fun x => (AddMonoidHom.mk' (polar f x) (by
    simp_all)).toRatLinearMap) (by
    aesop)).toRatLinearMap

@[simp] private lemma apply_bilinear (f hf x y) : bilinear f hf x y = polar f x y := rfl

/-- No coordinate potentials can recover the energy: after polarizing, apply
that identity to the separability idempotent of the coordinate field. -/
theorem exists_trade {z : Fin 9 → ℂ} (hz : AlgebraicCircle z) :
    ∃ P Q, Trade z P Q ∧ energy Q < energy P := by
  by_contra! hn
  have H (P Q) (h : Trade z P Q) := le_antisymm (hn P Q h) (hn Q P (fun i => (h i).symm))
  obtain ⟨f,hf⟩ := represents_of_trades (fun i => value (z i)) weight H
  have h : Represents z f := fun a b => hf (a,b)
  have hdeg := degree_of_rep h hz.inj
  iterate 6 obtain ⟨f,h,hdeg⟩ := truncate h hdeg (by norm_num)
  have h₁ x : ∑ i, f i x = 0 := by simpa using h 0 x
  have h₂ x : ∑ i, f i (x*z i) = Complex.normSq x := by simpa using h x 0
  let F := IntermediateField.adjoin ℚ (Set.range z)
  let : Finite (Set.range z) := Set.finite_range _
  let : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨i,rfl⟩; exact hz.alg i)
  obtain ⟨t,ht,ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R:=ℚ) (S:=F)).mp
    (Algebra.FormallyUnramified.of_isSeparable ..)
  let x (i) : F := ⟨z i, IntermediateField.subset_adjoin _ _ ⟨i,rfl⟩⟩
  let inc := F.val.toLinearMap
  let cj := (Complex.conjAe.toLinearEquiv.toLinearMap.restrictScalars ℚ).comp inc
  let L i := TensorProduct.lift ((bilinear _ (hdeg i)).compl₁₂ inc ((LinearMap.mul ℚ ℂ (z i)).comp cj))
  let q (i) := 1 ⊗ₜ[ℚ] x i - x i ⊗ₜ[ℚ] 1
  have H (u : F ⊗[ℚ] F) : ∑ i, L i (q i*u) = -(2*((Algebra.TensorProduct.lmul' ℚ u : F) : ℂ).re) := by
    induction u using TensorProduct.inductionOn with
    | add a b ha hb => simp [mul_add, Finset.sum_add_distrib, ha, hb]; abel
    | tmul a b =>
      simp [q,sub_mul,L,inc,cj,x,Algebra.TensorProduct.tmul_mul_tmul,←mul_assoc,Complex.mul_conj,hz.unit]
      simp_rw [mul_comm (z _)]
      simp [polar,fwdDiff,←add_mul,h₁,h₂,Complex.normSq_add]; ring
  have he := H t
  simp [q,ht,ht1] at he

end RadianRamsey
