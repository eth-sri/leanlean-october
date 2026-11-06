module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticOffset
public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl

/-! # Linear control and asymptotic equicontinuity of the step offsets -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem abs_sub_le_mul_root_dist_of_pos {n : ℕ} (hn : 0 < n)
    (q u : Fin n → ℝ) {K : ℝ} (hq : Monotone q)
    (hstep : ∀ j (hj : j + 1 < n), |u ⟨j + 1, hj⟩ - u ⟨j, by omega⟩| ≤
      K * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩)) :
    ∀ i j, |u i - u j| ≤ K * |q i - q j| := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact abs_sub_le_mul_root_dist q u hq  fun j => hstep j.val (by omega) 

theorem root_spacing_lower_at {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {M : ℝ}
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi, rootStepDensity N n p hp hn hs x ≤ M)
    (j : ℕ) (hj : j + 1 < n) :
    1 ≤ M * ((N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  
  have he := hupper (p (⟨j, by omega⟩ : Fin k).castSucc)
    ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
  rw [rootStepDensity_interior hp hs ⟨j, by omega⟩ ⟨le_rfl,  hp.2.1 (by change j < j + 1; omega) ⟩] at he
  exact (div_le_iff₀ (mul_pos (by exact_mod_cast  by omega ) (sub_pos.mpr (hp.2.1 (by change j < j + 1; omega))))).mp he

theorem offset_root_lipschitz {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hN : 0 < N) (hn : 0 < N / 2 - r)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hq : q ∈ S_n (N / 2 - r)) {M H : ℝ} (hH : 0 ≤ H)
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (N / 2 - r) q hq hn (by omega) x ≤ M)
    (hinc : ∀ j (hj : j + 1 < N / 2 - r),
      |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
        offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤ H / N) :
    ∀ i j, |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤
      H * M * |q i - q j| := abs_sub_le_mul_root_dist_of_pos hn q (offsetDisplacement N r h4 hr p q)
                         hq.2.1.monotone  fun j hj => by
                                            apply (hinc j hj).trans
                                            apply (div_le_iff₀ (Nat.cast_pos.mpr hN )).mpr
                                            
                                            nlinarith only [(mul_le_mul_of_nonneg_left (root_spacing_lower_at hq hn (by omega) hupper j hj) hH)] 

end PottsDiscontinuity.Bethe
