module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteAnalysis
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# Finite matrices in the discrete Bethe argument

The entries below are the source's displayed symmetric-coordinate matrix and its
gap rescaling.  The estimates here concern only the off-diagonal sign; the later
comparison of its diagonal entries with `2π` uses the excluded `ρ` estimates.
-/

@[expose] public section


open Set

namespace PottsDiscontinuity.Bethe

/-- First partial derivative of the Bethe phase. -/
noncomputable def thetaPartialFirst (Δ x y : ℝ)  :=
  deriv (fun s => theta Δ s y) x

/-- Second partial derivative of the Bethe phase. -/
noncomputable def thetaPartialSecond (Δ x y : ℝ)  :=
  deriv  (theta Δ x)  y

/-- Chain rule for the phase along an affine path in both variables. -/
theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hF  :=
    (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  
  
  
  
  have h₁eq : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) := ((analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt).unique (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ =>  (s, y) )
                                                                x hF ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  have h₂eq : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) := HasDerivAt.unique  (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt  (HasFDerivAt.comp_hasDerivAt y hF ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  have hvec : (a, b) = a • (1, 0) + b • (0, 1) := by
    ext <;> simp
  have hfd : fderiv ℝ F (x, y) (a, b) =
      a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
    calc
      fderiv ℝ F (x, y) (a, b) =
          fderiv ℝ F (x, y) (a • (1, 0) + b • (0, 1)) := by rw [hvec]
      _ = a • fderiv ℝ F (x, y) (1, 0) + b • fderiv ℝ F (x, y) (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
        simp_all
  
  
  
  
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t  =>
       (x + t * a, y + t * b) ) 0 (by
                                      simpa using hF) ((by
                                                          have hm := (hasDerivAt_id 0).mul_const a
                                                          simp_all : HasDerivAt (fun t  => x + t * a) a 0).prodMk (by
                                                                     have hm := (hasDerivAt_id 0).mul_const b
                                                                     simp_all : HasDerivAt (fun t  => y + t * b) b 0))
  rw [hfd] at hcomp
  
  rw [(by
         
         rfl : (fun t  => theta Δ (x + t * a) (y + t * b)) =
      F ∘  fun t  =>  (x + t * a, y + t * b))]
  exact hcomp

/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

/-- The next full index after a first-half coordinate. -/
def discreteHalfNextIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val + 1, by  omega⟩

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  grind +locals

/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1
  else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul {n : ℕ} (j : Fin (n / 2)) (f : Fin n → ℝ) :
     ∑ ell : Fin n, discreteSymBasis n j ell * f ell  =
      f (discreteHalfIndex n j) - f (Fin.rev (discreteHalfIndex n j)) := by
  
  let a := discreteHalfIndex n j
  let b := Fin.rev a
   
  
  calc
    _ = ∑ ell : Fin n,
          ((if ell = a then f a else 0) +  if ell = b then -f b else 0 ) :=
      Finset.sum_congr rfl  fun ell _ =>  fun ell => by
                                            grind +locals  ell 
    _ = (∑ ell : Fin n, if ell = a then f a else 0) +
          ∑ ell : Fin n, if ell = b then -f b else 0 := Finset.sum_add_distrib
    _ = f a - f b := by aesop

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half {n : ℕ} (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  grind +locals

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym {n : ℕ} (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  
  let a := discreteHalfIndex n k
  
  
  intro j
  have hvalA : discreteSymBasis n k a = 1 := by
    simp [discreteSymBasis, a]
  have hvalRev : discreteSymBasis n k (Fin.rev a) = -1 := by
    grind +locals
  by_cases h₁ : j = a
  · subst j
    rw [hvalRev, hvalA]
  · grind +locals

/-- The source's explicit symmetric-coordinate matrix `A` for `d(I-T)`. -/
noncomputable def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  if i = k then
    1 + (∑ ell ∈ Finset.univ.erase (discreteHalfIndex n i),
      thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell)) / (N : ℝ) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n i))) / (N : ℝ)
  else
    (thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n k)) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n k)))) / (N : ℝ)

/-- The source's gap matrix `B`, with diagonal entries `N (p_(j+1)-p_j)`. -/
noncomputable def discreteBetheMatrixB (N n : ℕ) (p : Fin n → ℝ)  := Matrix.diagonal fun j =>
      (N : ℝ) * (p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j))

/-- The rescaled matrix `Ã = A B` from the source. -/
noncomputable def discreteBetheMatrixATilde (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)  :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
noncomputable def discreteBetheResidual (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Fin n → ℝ := fun j => p j - discreteBetheMap Δ N n p j

/-- Affine path through `p` in direction `v`. -/
def discreteBetheAffinePath {n : ℕ} (p v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => p j + t * v j

/-- Directional derivative formula for the residual `I-T`. -/
theorem hasDerivAt_discreteBetheResidual_path {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i)
      (v i + (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) / (N : ℝ)) 0 := by
  have hcoord (j : Fin n) : HasDerivAt (fun t  => p j + t * v j) (v j) 0 := by
    have hm := (hasDerivAt_id 0).mul_const (v j)
    simp_all
  have hterm (ell : Fin n)  :=
    hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)
  
  let c  := 2 * Real.pi * discreteBetheIndex n i /  N 
  
  
  have hres := (by
                  simp_all : HasDerivAt (fun t  => p i + t * v i - c) (v i) 0).add ((HasDerivAt.fun_sum fun i a => hterm i : HasDerivAt
      (fun t  => ∑ ell : Fin n,
        theta Δ (p i + t * v i) (p ell + t * v ell))
      (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) 0).div_const N)
  
  rw [(by
         funext t
         simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap, c]
         ring : (fun t  =>
      discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i) =
      (fun t => p i + t * v i - c) +
         fun t => (∑ ell : Fin n,
          theta Δ (p i + t * v i) (p ell + t * v ell)) / (N ))]
  exact hres

/-- On the diagonal, the two partial derivatives of `Θ` cancel. -/
theorem thetaPartial_diag_sum {Δ x : ℝ} (hΔ : Δ < -1) :
    thetaPartialFirst Δ x x + thetaPartialSecond Δ x x = 0 := deriv_theta_diag hΔ x

/-- The explicit source matrix `A` is the derivative of `I-T` in symmetric
coordinates: its `k`th column is the directional derivative along
`e_k-e_(n+1-k)`, read at the `i`th first-half coordinate. -/
theorem hasDerivAt_discreteBetheResidual_basis {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (i k : Fin (n / 2)) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath p (discreteSymBasis n k) t)
        (discreteHalfIndex n i))
      (discreteBetheMatrixA Δ N n p i k) 0 := by
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  let v := discreteSymBasis n k
  have hgeneral := hasDerivAt_discreteBetheResidual_path (N := N) (n := n) hΔ p v ri
  have hv : v ri = if i = k then 1 else 0 := discreteSymBasis_at_half i k
  have hsum1 :  ∑ ell : Fin n,
      v ri * thetaPartialFirst Δ (p ri) (p ell)  =
      v ri * ∑ ell : Fin n, thetaPartialFirst Δ (p ri) (p ell) := by
    rw [Finset.mul_sum]
  have hsum2 :  ∑ ell : Fin n,
      v ell * thetaPartialSecond Δ (p ri) (p ell)  =
      thetaPartialSecond Δ (p ri) (p rk) -
        thetaPartialSecond Δ (p ri) (p (Fin.rev rk)) := sum_discreteSymBasis_mul k fun ell => thetaPartialSecond Δ (p ri) (p ell)
  
  rw [(by
         rw [Finset.sum_add_distrib, hsum1, hsum2, hv]
         by_cases hik : i = k
         · subst k
           
           rw [discreteBetheMatrixA, ite_eq_left rfl]
           have hsplit :
                ∑ ell : Fin n, thetaPartialFirst Δ (p ri) (p ell)  =
                 thetaPartialFirst Δ (p ri) (p ri) +
                   ∑ ell ∈ Finset.univ.erase ri,
                     thetaPartialFirst Δ (p ri) (p ell) := by
             simp_all
           rw [hsplit]
           have hdiag := thetaPartial_diag_sum (Δ := Δ) (x := p ri) hΔ
           have hnum :
                thetaPartialFirst Δ (p ri) (p ri) +
                   ∑ ell ∈ Finset.univ.erase ri,
                     thetaPartialFirst Δ (p ri) (p ell)  +
                 (thetaPartialSecond Δ (p ri) (p ri) -
                   thetaPartialSecond Δ (p ri) (p (Fin.rev ri))) =
                ∑ ell ∈ Finset.univ.erase ri,
                     thetaPartialFirst Δ (p ri) (p ell)  -
                   thetaPartialSecond Δ (p ri) (p (Fin.rev ri)) := by
             linear_combination hdiag
           simp only [ite_true, one_mul]
           rw [hnum]
           ring
         · grind +locals : v ri +
      (∑ ell : Fin n,
        (v ri * thetaPartialFirst Δ (p ri) (p ell) +
          v ell * thetaPartialSecond Δ (p ri) (p ell))) / (N ) =
      discreteBetheMatrixA Δ N n p i k)] at hgeneral
  simpa [v, ri, discreteBetheAffinePath] using hgeneral

/-- The second derivative of the phase difference is the difference of the two
second partial derivatives. -/
theorem deriv_discreteBetheG_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    deriv  (discreteBetheG Δ x)  y =
      thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y := by
  
  
  change deriv (fun t => theta Δ x t - theta Δ (-x) t) y = _
  rw [deriv_fun_sub  (analyticAt_theta_right hΔ x y).differentiableAt   (analyticAt_theta_right hΔ (-x) y).differentiableAt ]
  rfl

/-- The derivative of `G` in the second coordinate is nonnegative on the
negative square. -/
theorem discreteBetheG_deriv_nonneg_neg {Δ x y : ℝ} (hΔ : Δ < -1)
    (hx : x ∈ Icc (-Real.pi) 0) (hy : y ∈ Icc (-Real.pi) 0) :
    0 ≤ deriv  (discreteBetheG Δ x)  y := by
  let lam := lamOf Δ
  have hlam  := lamOf_pos hΔ
  
  
  obtain ⟨α, hα, hkx⟩ := (bijOn_kMap hlam).2.2  ⟨hx.1, le_trans hx.2 Real.pi_pos.le⟩ 
  obtain ⟨β, hβ, hky⟩ := (bijOn_kMap hlam).2.2  ⟨hy.1, le_trans hy.2 Real.pi_pos.le⟩ 
  have hαneg : α ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hα.1
    · by_contra h
      
      have hka  := (strictMono_kMap hlam) (lt_of_not_ge h)
      rw [hkx, kMap_zero] at hka
      exact (not_lt_of_ge hx.2) hka
  have hβneg : β ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hβ.1
    · by_contra h
      
      have hkb  := (strictMono_kMap hlam) (lt_of_not_ge h)
      rw [hky, kMap_zero] at hkb
      exact (not_lt_of_ge hy.2) hkb
  have hsα  := Real.sin_nonpos_of_nonpos_of_neg_pi_le hαneg.2 hαneg.1
  have hsβ  := Real.sin_nonpos_of_nonpos_of_neg_pi_le hβneg.2 hβneg.1
  
  have hkernel := Xi_le_of_cos_le (by linarith : 0 < 2 * lam) (by
                                                                 have htrig : Real.cos (α - β) - Real.cos (-α - β) =
                                                                     2 * Real.sin α * Real.sin β := by
                                                                   rw [Real.cos_sub, Real.cos_sub]
                                                                   simp only [Real.cos_neg, Real.sin_neg]
                                                                   ring
                                                                 nlinarith : Real.cos (-α - β) ≤ Real.cos (α - β))
  
  
  
  
  have hpos  := Xi_pos hlam β
  
  rw [← hkx, ← hky]
  nlinarith [ by
                                                                      exact  (HasDerivAt.comp β
                                                                                                                                                                    (Eq.mpr
                                                                                                                                                                      (congrArg (fun _a => HasDerivAt (discreteBetheG Δ (kMap lam α)) _a (kMap lam β))
                                                                                                                                                                        (deriv_discreteBetheG_right hΔ (kMap lam α) (kMap lam β)))
                                                                                                                                                                      (HasDerivAt.sub
                                                                                                                                                                        (DifferentiableAt.hasDerivAt (AnalyticAt.differentiableAt (analyticAt_theta_right hΔ (kMap lam α) (kMap lam β))))
                                                                                                                                                                        (DifferentiableAt.hasDerivAt
                                                                                                                                                                          (AnalyticAt.differentiableAt (analyticAt_theta_right hΔ (-kMap lam α) (kMap lam β))))))
                                                                                                                                                                    (hasDerivAt_kMap hlam β)).unique (hasDerivAt_discreteBetheG_kMap hΔ α β)  ]

/-- When `p∈S_n`, its first-half coordinates are negative. -/
theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex n j) < 0 := by
  rcases hp with ⟨_, hmono, hsym⟩
  have hlt := hmono (discreteHalfIndex_lt_rev j)
  rw [hsym (discreteHalfIndex n j)] at hlt
  linarith

/-- Off-diagonal entries of `Ã=AB` telescope to the derivative of `G`. -/
theorem discreteBetheMatrixATilde_offdiag_eq {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k)) *
        deriv  (discreteBetheG Δ (p (discreteHalfIndex n i))) 
          (p (discreteHalfIndex n k)) := by
  
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik]
  
  rw [ hp (discreteHalfIndex n k) ]
  simp only [thetaPartialSecond]
  rw [deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]
  simp only [thetaPartialSecond]
  field_simp [ by exact_mod_cast  Nat.ne_of_gt hN  ]

/-- The off-diagonal entries of `Ã` are nonnegative at every configuration in `S_n`. -/
theorem discreteBetheMatrixATilde_offdiag_nonneg {Δ : ℝ} {N n : ℕ}
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  have hsym  := hp.2.2
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hsym hN i k hik]
  
  
  
  
  
  
  exact mul_nonneg (le_of_lt (sub_pos.mpr (hp.2.1 (by
                                                     grind +locals)))) (discreteBetheG_deriv_nonneg_neg hΔ ⟨le_of_lt  (hp.1 (discreteHalfIndex n i)).1 , le_of_lt (discreteS_n_half_coord_neg hp i)⟩
                                                                                    ⟨le_of_lt  (hp.1 (discreteHalfIndex n k)).1 , le_of_lt (discreteS_n_half_coord_neg hp k)⟩)

end PottsDiscontinuity.Bethe
