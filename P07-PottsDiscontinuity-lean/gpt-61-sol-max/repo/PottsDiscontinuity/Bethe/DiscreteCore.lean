module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theta

/-!
# Discrete Bethe map and its symmetric domain

This file formalizes the finite dimensional definitions in Section 2.2 of
arXiv:1611.09877v2.  The map is defined on all vectors; `S_n` records the
strictly ordered, symmetric configurations used by the source.
-/

@[expose] public section



namespace PottsDiscontinuity.Bethe

/-- The centered quantum number `I_j = j - (n+1)/2`, with Lean's `Fin n`
index corresponding to the source's one-based index `j+1`. -/
noncomputable def discreteBetheIndex (n : ℕ) (j : Fin n) : ℝ :=
  (j.val : ℝ) + 1 - ((n : ℝ) + 1) / 2

/-- Reflection of the source index `j` to `n+1-j`. -/
theorem discreteBetheIndex_rev (n : ℕ) (j : Fin n) :
    discreteBetheIndex n (Fin.rev j) = -discreteBetheIndex n j := by
  unfold discreteBetheIndex
  
  have hv' :  (Fin.rev j).val  +  j.val  + 1 = (n : ℝ) := by
    simp_all <;> nlinarith
  linarith

/-- The symmetric subspace `R^n_sym = {q : q_(n+1-j) = -q_j}`. -/
def R_n_sym (n : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {p | ∀ j, p (Fin.rev j) = -p j}
  zero_mem' := by
    intro j
    simp
  add_mem' := by
    simp_all <;> grind
  smul_mem' := by
    simp_all

/-- The ordered symmetric configuration space `S_n`. -/
def S_n (n : ℕ)  :=
  {p | (∀ j, -Real.pi < p j ∧ p j < Real.pi) ∧ StrictMono p ∧ p ∈ R_n_sym n}

/-- The Bethe fixed point map, defined on every vector in `R^n`. -/
noncomputable def discreteBetheMap (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / (N : ℝ) -
    (∑ k : Fin n, theta Δ (p j) (p k)) / (N : ℝ)

/-- The discrete Bethe equations with the source's centered choice of `I_j`. -/
def DiscreteBetheEquation (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)  :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * discreteBetheIndex n j - ∑ k : Fin n, theta Δ (p j) (p k)

/-- The equation `T(p)=p` is exactly (BE_Δ), provided `N` is positive. -/
theorem discreteBetheMap_fixed_iff_equation {Δ : ℝ} {N n : ℕ}
    (hN : 0 < N) (p : Fin n → ℝ) :
    discreteBetheMap Δ N n p = p ↔ DiscreteBetheEquation Δ N n p := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast  Nat.ne_of_gt hN 
  constructor
  · intro h j
    have hj := congrFun h j
    dsimp [discreteBetheMap] at hj
    grind
  · grind +locals

/-- The inverse-parameter version of the Bethe map, defined using `thetaInv`.
At `ε=0` this is the extension of the source's map to `Δ=-∞`. -/
noncomputable def discreteBetheMapInv (ε : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / (N : ℝ) -
    (∑ k : Fin n, thetaInv ε (p j) (p k)) / (N : ℝ)

/-- The finite-`Δ` map preserves the symmetric subspace, as required for the
implicit-function argument in the source. -/
theorem discreteBetheMap_mem_R_n_sym (Δ : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) :
    discreteBetheMap Δ N n p ∈ R_n_sym n := by
  
  intro j
  have hsum :
       ∑ k : Fin n, theta Δ (p (Fin.rev j)) (p k)  =
        - ∑ k : Fin n, theta Δ (p j) (p k)  := by
    calc
       ∑ k : Fin n, theta Δ (p (Fin.rev j)) (p k) 
          = ∑ k : Fin n, theta Δ (-p j) (p k) := by rw [hp j]
      _ = ∑ k : Fin n, theta Δ (-p j) (p (Fin.rev k)) :=
        (Equiv.sum_comp Fin.revPerm _).symm
      _ = ∑ k : Fin n, -theta Δ (p j) (p k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hp k, theta_neg_neg]
      _ = - ∑ k : Fin n, theta Δ (p j) (p k)  := by rw [Finset.sum_neg_distrib]
  rw [discreteBetheMap, discreteBetheMap, discreteBetheIndex_rev, hsum]
  ring

/-- Joint real analyticity of the inverse-parameter map for `|ε|<1`; this
includes a neighbourhood of `ε=0` and therefore analyticity at `Δ=-∞`. -/
theorem analyticAt_discreteBetheMapInv {ε : ℝ} (hε : |ε| < 1) (N n : ℕ)
    (p : Fin n → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin n → ℝ) => discreteBetheMapInv z.1 N n z.2) (ε, p) := by
  apply AnalyticAt.pi
  intro j
  
  
  have hEval (k : Fin n) : AnalyticAt ℝ (fun z  => z.2 k) (ε, p) :=
    (analyticAt_pi_iff.mp  analyticAt_snd ) k
  have hsum : @AnalyticAt ℝ (ℝ × (Fin n → ℝ)) ℝ
      DenselyNormedField.toNontriviallyNormedField Prod.normedAddCommGroup Prod.normedSpace
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      (fun z  => ∑ k : Fin n, thetaInv z.1 (z.2 j) (z.2 k)) (ε, p) := by
    apply Finset.univ.analyticAt_fun_sum
    intro k hk
    
    exact AnalyticAt.comp
      (g := fun q  => thetaInv q.1 q.2.1 q.2.2)
      (f := fun z : ℝ × (Fin n → ℝ) =>  (z.1, z.2 j, z.2 k) )
      (analyticAt_thetaInv hε (p j) (p k)) ((analyticAt_fst).prod ((hEval j).prod (hEval k)))
  
  
  
  have hfinal := (analyticAt_const : @AnalyticAt ℝ (ℝ × (Fin n → ℝ)) ℝ
      DenselyNormedField.toNontriviallyNormedField Prod.normedAddCommGroup Prod.normedSpace
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      (fun _  => 2 * Real.pi * discreteBetheIndex n j / (N ))
      (ε, p)).sub (by
                                 fun_prop : @AnalyticAt ℝ (ℝ × (Fin n → ℝ)) ℝ
      DenselyNormedField.toNontriviallyNormedField Prod.normedAddCommGroup Prod.normedSpace
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      (fun z : ℝ × (Fin n → ℝ) => (N : ℝ)⁻¹ •
         ∑ k : Fin n, thetaInv z.1 (z.2 j) (z.2 k) ) (ε, p))
  
  rw [(by
         funext z
         simp only [Pi.sub_apply, discreteBetheMapInv]
         ring :
       (fun _  =>
          2 * Real.pi * discreteBetheIndex n j / (N )) -
        (fun z  => (N : ℝ)⁻¹ •
           ∑ k : Fin n, thetaInv z.1 (z.2 j) (z.2 k) )  =
         fun z : ℝ × (Fin n → ℝ) => discreteBetheMapInv z.1 N n z.2 j)] at hfinal
  exact hfinal

/-- On `Δ<-1`, the inverse-parameter map at `ε=1/Δ` agrees with the source's
finite-parameter map. -/
theorem discreteBetheMap_eq_inv {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ)
    (p : Fin n → ℝ) :
    discreteBetheMap Δ N n p = discreteBetheMapInv (1 / Δ) N n p := by
  grind [discreteBetheMap, discreteBetheMapInv, theta, thetaInv]

end PottsDiscontinuity.Bethe
