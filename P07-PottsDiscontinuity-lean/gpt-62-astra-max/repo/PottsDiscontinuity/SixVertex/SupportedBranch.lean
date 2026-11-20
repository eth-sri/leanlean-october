module
public import Mathlib

/-! # Identifying a Perron branch by the limiting sign of its eigenvector

A continuous eigenvector need not be strictly positive at the endpoint: some
rows of the limiting matrix can vanish. For symmetric nonnegative matrices
with a strictly positive Perron vector, its maximal coordinate cannot lie on
one of these zero rows, since the Perron value dominates any single entry.
This gives nonzero pairing with a branch positive on the surviving rows. -/
@[expose] public section
open Filter Topology Matrix Finset
namespace PottsDiscontinuity.PerronFrobenius

lemma eventually_eq_of_supported_wave {ι X : Type*} [Fintype ι] [Nonempty ι] {l : Filter X}
    {A : X → Matrix ι ι ℝ} {B : Matrix ι ι ℝ} {ψ : X → ι → ℂ} {w : ι → ℝ}
    {μ : X → ℂ} {ρ : X → ℝ} (hA : ∀ i j, Tendsto (fun t => A t i j) l (𝓝 (B i j)))
    (hψ : ∀ i, Tendsto (fun t => (ψ t i).re) l (𝓝 (w i))) (hw : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, w i = 0 → ∀ j, B i j = 0) (hentry : ∃ a b, 0 < B a b)
    (he : ∀ᶠ t in l, (∀ i j, 0 ≤ A t i j) ∧ (A t).IsSymm ∧
      (∃ y : ι → ℝ, (∀ i, 0 < y i) ∧ A t *ᵥ y = ρ t • y) ∧
      (A t).map (algebraMap ℝ ℂ) *ᵥ ψ t = μ t • ψ t) :
    ∀ᶠ t in l, μ t = (ρ t : ℂ) := by
  classical
  obtain ⟨a,b,hab⟩ := hentry
  let err t := ∑ j, |(ψ t j).re - w j|
  have herr : Tendsto err l (𝓝 0) := by
    simpa [err] using tendsto_finsetSum univ fun i _ => ((hψ i).sub_const (w i)).abs
  have good (i) : ∀ᶠ t in l, (0 < w i → err t < w i) ∧ (w i = 0 → ∑ j, A t i j < A t a b) := by
    rcases (hw i).eq_or_lt with hi | hi
    · have hx := tendsto_finsetSum univ fun j _ => hA i j
      simp only [hsupp i hi.symm,sum_const_zero] at hx
      filter_upwards [hx.eventually_lt (hA a b) hab] with t ht; exact ⟨fun h => (hi.not_lt h).elim, fun _ => ht⟩
    · filter_upwards [herr.eventually (Iio_mem_nhds hi)] with t ht; exact ⟨fun _ => ht,fun h => (hi.ne' h).elim⟩
  filter_upwards [he,eventually_all.mpr good] with t ⟨h₀,hs,⟨y,hy,hey⟩,heψ⟩ hgood
  have row (i) := congrFun hey i
  change ∀ i, (∑ j, A t i j*y j) = ρ t*y i at row
  have single (i j) : A t i j*y j ≤ ρ t*y i := row i ▸ single_le_sum (fun k _ => mul_nonneg (h₀ i k) (hy k).le) (mem_univ j)
  have hsym : A t b a = A t a b := congrFun (congrFun hs a) b
  have hr : A t a b ≤ ρ t := by
    have h := single b a; rw [hsym] at h
    exact le_of_mul_le_mul_right (a := y a + y b) (by nlinarith [single a b]) (add_pos (hy a) (hy b))
  obtain ⟨i,_,hi⟩ := univ.exists_max_image y univ_nonempty
  have hle (j) := hi j (mem_univ _)
  have hsum : ρ t ≤ ∑ j, A t i j := by
    apply le_of_mul_le_mul_right (a := y i) _ (hy i)
    rw [← row,sum_mul]; exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (h₀ i j)
  have hwpos := (hw i).lt_of_ne (fun hz => (not_lt_of_ge (hr.trans hsum)) ((hgood i).2 hz.symm))
  have hepos := mul_lt_mul_of_pos_left ((hgood i).1 hwpos) (hy i)
  have hm : y i*w i ≤ ∑ j, y j*w j := single_le_sum (fun j _ => mul_nonneg (hy j).le (hw j)) (mem_univ _)
  have hd : ∑ j, y j*(w j-(ψ t j).re) ≤ y i*err t := by
    dsimp only [err]; rw [mul_sum]; apply sum_le_sum; intro j _
    calc
      _ ≤ y j * |(ψ t j).re-w j| := mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; apply le_abs_self) (hy j).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (hle j) (abs_nonneg _)
  simp only [mul_sub,sum_sub_distrib] at hd
  let v := fun j => (y j : ℂ)
  have hn : v ⬝ᵥ ψ t ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp [dotProduct, v, Complex.mul_re] at h; linarith
  let T := (A t).map (algebraMap ℝ ℂ)
  have hv : T *ᵥ v = (ρ t:ℂ) • v := by
    ext j; change (∑ k, (A t j k : ℂ)*y k) = (ρ t:ℂ)*y j; exact_mod_cast row j
  have hT : T.IsSymm := by ext u v; exact congrArg Complex.ofReal (congrFun (congrFun hs u) v)
  have h := dotProduct_mulVec v T (ψ t)
  rw [heψ,dotProduct_smul,← show Tᵀ = T from hT, vecMul_transpose,hv,smul_dotProduct] at h
  exact mul_right_cancel₀ hn h

end PottsDiscontinuity.PerronFrobenius
