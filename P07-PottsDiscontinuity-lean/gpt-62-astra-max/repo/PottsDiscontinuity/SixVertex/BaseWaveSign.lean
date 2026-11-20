module
public import PottsDiscontinuity.SixVertex.Cor34BetheBase
public import PottsDiscontinuity.SixVertex.InfinityPhase
public import PottsDiscontinuity.SixVertex.InfinityMoves
public import PottsDiscontinuity.BetheAnsatz.GapGeometry

/-! Shrinking each occupied site by its rank turns the infinite-anisotropy
wave into an ordinary centered Slater determinant. Its sine Vandermonde has
one fixed phase on the entire chamber and is strictly positive away from
collisions (including the periodic seam). -/
@[expose] public section
open Finset Complex
namespace PottsDiscontinuity.SixVertex
open BetheAnsatz
variable {N n : ℕ}

def compressed (x : Fin n → ℤ) (i : Fin n) := x i + ((n-1-i.val : ℕ):ℤ)

lemma base_wave_formula (hnN : n < N) (x : Fin n → ℤ) :
    cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n) x =
      slaterPhase n * (sineLiftWeight ((N-n:ℕ):ℝ) (compressed x) : ℂ) := by
  rw [← slater_centered_unitWave]
  let p := Bethe.discreteBaseSolution N n
  have hq : unitWave (Real.pi/((N-n:ℕ):ℝ)) = cor34_halfRoot (N-n) := by
    simp only [unitWave,cor34_halfRoot,Complex.ofReal_div,Complex.ofReal_natCast]; congr 1; ring
  have hz (k) : centeredMomenta (k := n) (unitWave (Real.pi/((N-n:ℕ):ℝ))) k = z (p k) := by
    rw [hq]; exact (cor34_base_z_eq_halfRoot_zpow hnN k).symm
  unfold slater cor34_normalizedCoordinate
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply sum_congr rfl; intro σ _
  have plane (k : Fin n) : Complex.exp (I * (p (σ k):ℂ) * (x k:ℂ)) = z (p (σ k)) ^ x k := by
    rw [z,← Complex.exp_int_mul]; congr 1; ring
  simp only [cor34_normalizedAmplitude_zero,prod_const,Fin.card_Ioi,planeWave,Matrix.transpose_apply,planeWaveMatrix]
  change ((Equiv.Perm.sign σ:ℤ):ℂ) * (∏ i, z (p (σ i))^(n-1-i.val)) *
    (∏ i, Complex.exp (I * (p (σ i):ℂ) * (x i:ℂ))) = _
  rw [mul_assoc,← prod_mul_distrib]; congr 1
  apply prod_congr rfl; intro k _
  rw [plane,hz,compressed,zpow_add₀ (z_ne_zero _),zpow_natCast,mul_comm]

private lemma distances {N n : ℕ} (x : State (N+1) (n+1)) {a b : Fin (n+1)} (hab : a < b) :
    let y := compressed (positions x); let L : ℤ := (N+1:ℕ) - (n+1:ℕ)
    0 ≤ y b-y a ∧ y b-y a ≤ L ∧ (NoConsecutiveUp x.1 → 0 < y b-y a ∧ y b-y a < L) := by
  let p := x.1.orderEmbOfFin x.2
  let u := fun i : Fin (n+1) => ((p i).val : ℤ) - i.val
  have hy (i) : compressed (positions x) i = u i + n := by
    dsimp [compressed,positions,u,p]; omega
  have hs (i : Fin n) := p.strictMono (Fin.castSucc_lt_succ (i := i))
  have hu : Monotone u := Fin.monotone_iff_le_succ.mpr fun i => by
    have hi : (p i.castSucc).val < (p i.succ).val := hs i
    dsimp [u]; omega
  have h₁ := hu (Fin.zero_le a); have h₂ := hu (Fin.le_last b)
  have hbnd := (p (Fin.last n)).isLt
  simp only [u,Fin.val_zero,Fin.val_last, Nat.cast_zero,sub_zero] at h₁ h₂
  dsimp only; rw [hy,hy]
  have hp (i) : p i ∈ x.val := orderEmbOfFin_mem x.1 x.2 i
  refine ⟨by linarith [hu hab.le],by dsimp [u]; omega, fun h => ⟨?_,?_⟩⟩
  · have strict : StrictMono u := Fin.strictMono_iff_lt_succ.mpr fun i => by
      have hi : (p i.castSucc).val < (p i.succ).val := hs i
      have hne : (p i.castSucc).val+1 ≠ (p i.succ).val := by
        intro he
        have he' : nxt (p i.castSucc) = p i.succ := Fin.ext ((nxt_val_of_lt (by omega)).trans he)
        exact h _ (hp _) (he' ▸ hp _)
      dsimp [u]; omega
    linarith [strict hab]
  · have hne : (p 0).val ≠ 0 ∨ (p (Fin.last n)).val ≠ N := by
      by_contra! he
      have h0 : p 0 = 0 := Fin.ext he.1
      have hlast : p (Fin.last n) = Fin.last N := Fin.ext he.2
      exact h _ (hp (Fin.last n)) (by rw [hlast]; simpa [h0] using hp 0)
    dsimp [u]; omega

lemma base_chamber_sign (hn : 0 < n) (hbound : 2*n ≤ N) (x : State N n) :
    let w := sineLiftWeight ((N-n:ℕ):ℝ) (compressed (positions x))
    0 ≤ w ∧ (NoConsecutiveUp x.1 → 0 < w) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hL : (0:ℝ) < ((N+1-(n+1):ℕ):ℝ) := by exact_mod_cast (by omega : 0 < N+1-(n+1))
  have h (i j : Fin (n+1)) (hij : i < j) := distances x hij
  dsimp only; constructor
  · apply prod_nonneg; intro i _; apply prod_nonneg; intro j hj
    obtain ⟨h₁,h₂,_⟩ := h i j (Finset.mem_Ioi.mp hj)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · apply div_nonneg _ hL.le; apply mul_nonneg Real.pi_pos.le; exact_mod_cast h₁
    · apply (div_le_iff₀ hL).mpr; apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      rw [Nat.cast_sub (by omega)]; exact_mod_cast h₂
  · intro hx; apply prod_pos; intro i _; apply prod_pos; intro j hj
    obtain ⟨h₁,h₂⟩ := (h i j (Finset.mem_Ioi.mp hj)).2.2 hx
    apply Real.sin_pos_of_pos_of_lt_pi
    · apply div_pos _ hL; apply mul_pos Real.pi_pos; exact_mod_cast h₁
    · apply (div_lt_iff₀ hL).mpr; apply mul_lt_mul_of_pos_left _ Real.pi_pos
      rw [Nat.cast_sub (by omega)]; exact_mod_cast h₂

end PottsDiscontinuity.SixVertex
