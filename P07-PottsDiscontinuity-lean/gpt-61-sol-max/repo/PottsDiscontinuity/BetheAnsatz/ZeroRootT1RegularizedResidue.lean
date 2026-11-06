module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1FinitePairs
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperStep

/-!
# The T₁ residue is the regularized word coefficient

For a word with a unique cyclic ML edge, the pole residue at that edge is the
product of the L/M weights with the zero-root slot omitted. This is the precise
bridge between the analytic pair limit and the zipper invariant.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The residue factor at a unique ML edge is the product of all nonsingular
letter weights, with the zero-root slot omitted. -/
theorem wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a b : Fin (n + 1))
    (hrot : b = finRotate (n + 1) a) (hσ : σ b = l)
    (hleft : w a = false) (hright : w b = true)
    (hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true → k = a) :
    M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a =
      zeroRootRegularizedProduct c p l σ w := by
  let τ := finRotate (n + 1)
  let E  := univ.filter
     fun k => w k = true ∧ w (τ k) = true 
  let F  := univ.filter  fun k => w k = false 
  let J  := univ.filter  fun j => w j = true ∧ j ≠ b 
  let qL (j : Fin (n + 1)) := L c (z (p (σ j)))
  let qM (j : Fin (n + 1)) := M c (z (p (σ j)))
  
  have hroot : σ.symm l = b := by
    apply σ.injective
    simpa using hσ.symm
  have hJimage : E.image τ = J := by
    ext j
    constructor
    · aesop
    · intro hj
      have hjw := (Finset.mem_filter.mp hj).2.1
      
      let k := τ.symm j
      have hkτ : τ k = j := τ.apply_symm_apply j
      
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,  by
                                                              grind , ?_⟩, hkτ⟩
      simpa [hkτ] using hjw
  let G (k : Fin (n + 1))  :=
    if w k then  if w (τ k) then qL (τ k) else 1  else qM k
  let H (k : Fin (n + 1))  :=
    if k = a then qM a else wordEdgeFactor c p σ w k
  have hlocal (k : Fin (n + 1)) : H k = G k := by
    by_cases hka : k = a
    · aesop
    · by_cases hwk : w k = true <;> by_cases hwn : w (τ k) = true
      · simp [H, G, hwk, wordEdgeFactor, qL, τ, hka]
      · simp [H, G, hwk, wordEdgeFactor, qL, τ, hka]
      · 
        aesop
      · 
        
        change (if k = a then qM a else wordEdgeFactor c p σ w k) =
           if w k then  if w (τ k) then qL (τ k) else 1  else qM k 
        simp [hwk, (by
                                                        aesop : w (k + 1) = false), wordEdgeFactor, qM, hka]
  have hprodH :  ∏ k, H k  =
      M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a := by
    rw [← Finset.mul_prod_erase  univ  H (mem_univ a)]
    have hHa : H a = M c (z (p (σ a))) := by simp [H, qM]
    have hrest :  ∏ k ∈ univ.erase a, H k  =
        wordCoefficientEraseEdge c p σ w a := by
      
      apply Finset.prod_congr rfl
      intro k hk
      have hka  := (Finset.mem_erase.mp hk).1
      simp [H, hka]
    rw [hHa, hrest]
  have hprodG :  ∏ k, G k  = (∏ k ∈ E, qL (τ k)) * ∏ k ∈ F, qM k := by
    
    have hL : (∏ k, if w k then  if w (τ k) then qL (τ k) else 1  else 1) =
        ∏ k ∈ E, qL (τ k) := by
      have hpoint (k : Fin (n + 1)) :
          (if w k then  if w (τ k) then qL (τ k) else 1  else 1) =
            if w k = true ∧ w (τ k) = true then qL (τ k) else 1 := by
        grind
      simp_rw [hpoint]
      simpa [E] using (Finset.prod_filter (s := univ)
        (fun k => w k = true ∧ w (τ k) = true)  fun k => qL (τ k) ).symm
    have hM : (∏ k, if w k then 1 else qM k) = ∏ k ∈ F, qM k := by
      have hpoint (k : Fin (n + 1)) :
          (if w k then 1 else qM k) = if w k = false then qM k else 1 := by
        cases hw : w k <;> simp
      simp_rw [hpoint]
      simpa  using (Finset.prod_filter (s := univ)
        (fun k => w k = false) qM).symm
    calc
       ∏ k, G k  = ∏ k, (if w k then  if w (τ k) then qL (τ k) else 1  else 1) *
           if w k then 1 else qM k  := prod_congr rfl fun k hk => (fun (k : Fin (n + 1)) => by
                                                                     grind) k
      _ = (∏ k, if w k then  if w (τ k) then qL (τ k) else 1  else 1) *
          ∏ k, if w k then 1 else qM k := Finset.prod_mul_distrib
      _ = (∏ k ∈ E, qL (τ k)) * ∏ k ∈ F, qM k := by rw [hL, hM]
  have htarget : zeroRootRegularizedProduct c p l σ w =
      (∏ j ∈ J, qL j) * ∏ j ∈ F, qM j := by
    have hletter : ∀ j, (if j = b then  1  else
          zeroRootLetterWeight c p σ w j) =
        (if w j then  if j = b then 1 else qL j  else 1) *
           if w j then 1 else qM j  := by
      intro j
      by_cases hj : j = b
      · simp_all
      · cases hw : w j <;> simp [zeroRootLetterWeight, qL, qM, hj, hw]
    have hprodErase :
        (∏ j, if j = b then  1  else zeroRootLetterWeight c p σ w j) =
          zeroRootRegularizedProduct c p l σ w := by
      unfold zeroRootRegularizedProduct
      rw [hroot]
      calc
        (∏ j, if j = b then  1  else zeroRootLetterWeight c p σ w j) =
            (if b = b then  1  else zeroRootLetterWeight c p σ w b) *
              ∏ j ∈ univ.erase b,
                 if j = b then  1  else zeroRootLetterWeight c p σ w j  :=
          (Finset.mul_prod_erase  univ 
            (fun j => if j = b then  1  else zeroRootLetterWeight c p σ w j)
            (mem_univ b)).symm
        _ = ∏ j ∈ univ.erase b, zeroRootLetterWeight c p σ w j := by
          simp only [ite_true, one_mul]
          apply Finset.prod_congr rfl
          intro j hj
          have hjb  := (Finset.mem_erase.mp hj).1
          simp [hjb]
    rw [← hprodErase]
    simp_rw [hletter]
    rw [Finset.prod_mul_distrib]
    have hL : (∏ j, if w j then  if j = b then 1 else qL j  else 1) =
        ∏ j ∈ J, qL j := by
      have hpoint (j : Fin (n + 1)) :
          (if w j then  if j = b then 1 else qL j  else 1) =
            if w j = true ∧ j ≠ b then qL j else 1 := by
        grind
      simp_rw [hpoint]
      simpa [J] using (Finset.prod_filter (s := univ)
        (fun j => w j = true ∧ j ≠ b) qL).symm
    have hM : (∏ j, if w j then 1 else qM j) = ∏ j ∈ F, qM j := by
      have hpoint (j : Fin (n + 1)) :
          (if w j then 1 else qM j) = if w j = false then qM j else 1 := by
        cases hw : w j <;> simp
      simp_rw [hpoint]
      simpa  using (Finset.prod_filter (s := univ)
        (fun j => w j = false) qM).symm
    rw [hL, hM]
  
  calc
    M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a
        = ∏ k, H k := hprodH.symm
    _ = ∏ k, G k := prod_congr rfl fun k a => hlocal k
    _ = (∏ k ∈ E, qL (τ k)) * ∏ k ∈ F, qM k := hprodG
    _ = zeroRootRegularizedProduct c p l σ w := by rw [ Trans.trans (Eq.symm (prod_image (Function.Injective.injOn (Equiv.injective τ))))
                                                                                                               (Eq.mpr (congrArg (fun _a => _a.prod qL = J.prod qL) hJimage) (Eq.refl (J.prod qL))) , htarget]

/-- For `T1PairIndex`, the pole residue coefficient is exactly its zipper
regularized product. -/
theorem t1Pair_residue_eq_regularizedProduct {n : ℕ} {l : Fin (n + 1)}
    (c : ℝ) (p : Fin (n + 1) → ℝ)
    (i : T1PairIndex n l) :
    M c (z (p (i.σ (t1EdgeLeft i.edge)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w
          (t1EdgeLeft i.edge) =
      zeroRootRegularizedProduct c p l i.σ i.w := by
  have hpert : perturbedMomenta p l 0 = p := by
    simp_all [perturbedMomenta]
  
  rw [hpert]
  exact wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct c p l i.σ i.w
    (t1EdgeLeft i.edge) (t1EdgeRight i.edge) (by
                                                cases i.edge with
                                                | none => exact finRotate_last.symm
                                                | some a => exact (finRotate_of_lt a.isLt).symm) i.hσ i.hleft i.hright i.hunique

/-- The finite pair limit is the regularized word term times its corrected
phase derivative. -/
theorem t1PairLimit_eq_regularizedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w *
         match i.edge with
        | some a => (zeroRootPhaseDerivative (N := N) (anisotropy c)
            (p (i.σ a.castSucc)) False : ℂ)
        | none => (zeroRootPhaseDerivative (N := N) (anisotropy c)
            (p (i.σ (Fin.last n))) True : ℂ)  := by
  have hres := t1Pair_residue_eq_regularizedProduct (c := c) p
    (l := l) i
  cases hEdge : i.edge with
  | none =>
      grind [t1EdgeLeft, t1PairLimit, zeroRootRegularizedWordTerm]
  | some a =>
      grind [t1EdgeLeft, t1PairLimit, zeroRootRegularizedWordTerm]

end PottsDiscontinuity.BetheAnsatz
