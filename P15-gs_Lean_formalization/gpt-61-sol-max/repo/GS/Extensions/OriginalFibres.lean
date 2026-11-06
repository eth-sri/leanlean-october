import Mathlib.Tactic

import Mathlib.Tactic.Module
import GS.Extensions.OriginalCompact
import GS.Extensions.TransportedProjection




/-!
# Missing algebra and angle recovery in the ORIGINAL f/g fibre proof

The central result gives actual equality of f/g
fibres under explicit local analytic hypotheses: bounded angles, scalar sign
normalization, and injectivity of originalPsi on a set containing c ± z.
Those hypotheses are NOT claimed established uniformly on some K_eta here.
In particular no smoothness of the singular matrix family is assumed.
-/

namespace GS.Extensions

/-- Explicit local analytic input. No statement of equal fibres is hidden here.
The set V is a matrix-exponential chart domain supplied by a later analytic
lemma. The angles and signs are the ones in the original manuscript. -/
 def NormalizedOriginal {q : ℕ} (Q₀ : Mat q) (V : Set (Mat q))
    (p : OriginalParameters q) : Prop :=
  let (ell,r,c,z,u) := p
  OnCircle u ∧
    (∀ j : Fin q, j.val=0 → r j=0) ∧
    (∀ i j, ell i+r j ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) ∧
    (∀ i j, 0 < (originalPsi Q₀ (c+z) i j+originalPsi Q₀ (c-z) i j)*Q₀ i j) ∧
    c+z ∈ V ∧ c-z ∈ V

 theorem original_same_fibres_normalized {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (V : Set (Mat q)) (hinj : Set.InjOn (originalPsi Q₀) V)
    (p p' : OriginalParameters q)
    (hp : NormalizedOriginal Q₀ V p) (hp' : NormalizedOriginal Q₀ V p') :
    originalF Q₀ p=originalF Q₀ p' ↔ originalG p=originalG p' := by
  rcases p with ⟨ell,r,c,z,u⟩
  rcases p' with ⟨ell',r',c',w,v⟩
  rcases hp with ⟨hu,hr₀,ht,hpos,hplus,hminus⟩
  rcases hp' with ⟨hv,hr₀',ht',hpos',hplus',hminus'⟩
  constructor
  · intro hF
    have hblocks (i j : Fin q) := congrArg
      (fun M : Mat (q*2) => fun s t : Fin 2 =>
        M (finProdFinEquiv (i,s)) (finProdFinEquiv (j,t))) hF
    simp only [originalF, Equiv.symm_apply_apply] at hblocks
    have hangles : ∀ i j, ell i+r j=ell' i+r' j := by
      intro i j
      let s := originalPsi Q₀ (c+z) i j+originalPsi Q₀ (c-z) i j
      let s' := originalPsi Q₀ (c'+w) i j+originalPsi Q₀ (c'-w) i j
      have hc : s*Real.cos (ell i+r j)=s'*Real.cos (ell' i+r' j) := by
        convert congrArg (fun X : Mat 2 => X 0 0+X 1 1) (hblocks i j) using 1 <;>
          simp only [Matrix.mul_apply,Fin.sum_univ_two] <;>
          simp [s,s',rotation,middleBlock,T,Real.cos_add] <;> ring
      have hs : s*Real.sin (ell i+r j)=s'*Real.sin (ell' i+r' j) := by
        convert congrArg (fun X : Mat 2 => X 1 0-X 0 1) (hblocks i j) using 1 <;>
          simp only [Matrix.mul_apply,Fin.sum_univ_two] <;>
          simp [s,s',rotation,middleBlock,T,Real.sin_add] <;> ring
      have hnorm (a t : ℝ) : (a*Real.cos t)^2+(a*Real.sin t)^2=a^2 := by grind [Real.sin_sq_add_cos_sq]
      have he : s^2=s'^2 := by rw [← hnorm s (ell i+r j),hc,hs,hnorm]
      have hS : 0<s*Q₀ i j := hpos i j
      have hS' := hpos' i j
      have heq : s=s' := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
        · exact h
        · nlinarith
      rw [← heq] at hs
      exact Real.injOn_sin (ht i j) (ht' i j)
        (mul_left_cancel₀ (left_ne_zero_of_mul hS.ne') hs)
    let j₀ : Fin q := ⟨0,hq⟩
    have hell : ell=ell' := by
      funext i
      have hh := hangles i j₀
      rw [hr₀ j₀ rfl,hr₀' j₀ rfl] at hh
      simpa only [add_zero] using hh
    have hright : r=r' := by aesop
    subst ell'
    subst r'
    have hm : ∀ i j,
        middleBlock (originalPsi Q₀ (c+z) i j) (originalPsi Q₀ (c-z) i j) u =
        middleBlock (originalPsi Q₀ (c'+w) i j) (originalPsi Q₀ (c'-w) i j) v := by
      intro i j
      exact (_root_.Unitary.mul_right_inj ⟨rotation (ell i),rotation_orthogonal _⟩).mp
        ((_root_.Unitary.mul_left_inj ⟨rotation (r j),rotation_orthogonal _⟩).mp (hblocks i j))
    let a := originalPsi Q₀ (c+z)
    let b := originalPsi Q₀ (c-z)
    let a' := originalPsi Q₀ (c'+w)
    let b' := originalPsi Q₀ (c'-w)
    have hs : ∀ i j, a i j+b i j=a' i j+b' i j :=
      fun i j => (middleBlock_eq_sum_and_difference _ _ _ _ u v (hm i j)).1
    have hout : outer u (fun ij : Fin q × Fin q => a ij.1 ij.2-b ij.1 ij.2) =
        outer v (fun ij : Fin q × Fin q => a' ij.1 ij.2-b' ij.1 ij.2) := by
      ext r ij
      have he := (middleBlock_eq_sum_and_difference _ _ _ _ u v (hm ij.1 ij.2)).2
      fin_cases r
      · have hh := congrFun (congrFun he 0) 0
        simpa [outer,T,mul_comm] using hh
      · have hh := congrFun (congrFun he 0) 1
        simpa [outer,T,mul_comm] using hh
    have hf := (outer_fibres hu hv).mp hout
    
    apply (originalG_fibres ell r ell r c z c' w u v hu hv).mpr
    have h₁ := hinj hplus hplus'
    have h₂ := hinj hminus hminus'
    have h₄ := hinj hplus hminus'
    have h₅ := hinj hminus hplus'
    simp only [← Matrix.ext_iff, funext_iff, Prod.forall, Pi.zero_apply, Pi.neg_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.zero_apply] at *
    grind
  · intro hG
    rcases (originalG_fibres _ _ _ _ _ _ _ _ _ _ hu hv).mp hG with ⟨rfl,rfl,rfl,h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      (simp [originalF, middleBlock_equal, middleBlock_swap, sub_eq_add_neg]; rfl)

end GS.Extensions
