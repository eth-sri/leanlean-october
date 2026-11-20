module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Price.LogExtension
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Price.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Comparison

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation TensorResource
variable {K : Type*} [CommSemiring K] [Nontrivial K]

/-- A reusable catalyst costs only a constant factor in rank. -/
private theorem currency_bound {d k : ℕ} (hd : 0 < d) {c y : TensorClass K} (hc : 1 ≤ c*y)
    (h : c * matrixClass d ≤ c * scalars k) : (d:ℝ)^exactRankExponent K ≤ k := by
  classical
  apply polynomial_overhead (by positivity) (Polynomial.C (rank (c*y):ℝ))
  intro j
  have hpow := (Commute.all (matrixClass d) (scalars (K := K) k)).function_commute_mul_right.iterate_le_of_map_le
    (fun _ _ h => mul_le_mul' h le_rfl) (fun _ _ h => mul_le_mul' h le_rfl) h j
  have he : matrixClass (K := K) (d^j) ≤ scalars (rank (c*y)*k^j) := by
    rw [matrixClass_pow,map_mul,map_pow]
    calc
      _ ≤ c*matrixClass d^j*y := by simpa [mul_right_comm] using mul_le_mul' hc (le_refl (matrixClass d^j))
      _ ≤ _ := (mul_le_mul' (by simpa using hpow) (le_refl y)).trans (by
        simpa [mul_right_comm] using mul_le_mul' (le_rank (c*y)) (le_refl ((scalars (K := K) k)^j)))
  have hr : exactMatrixRank K (d^j) ≤ rank (c*y)*k^j := Nat.find_min' _ he
  simpa [Real.rpow_pow_comm (by positivity : (0:ℝ) ≤ d)] using
    (exactMatrixRank_rpow_lower_of_pos (K := K) (pow_pos hd j)).trans (Nat.cast_le.mpr hr)

/-- Support a price on the multiplicative monoid. An element is tradeable
if a multiple dominates one; this is exactly the saturation of the upper
interval at one. Prices outside this multiplicatively closed face are zero. -/
theorem exists_detecting_price {d k : ℕ} (hd : 0 < d) (hk₀ : 0 < k)
    (hk : (k:ℝ) < (d:ℝ)^exactRankExponent K) :
    ∃ χ : Price K, χ.eval (scalars k) ≤ (d:ℝ)^3 := by
  classical
  let S := TensorClass K
  let U := (Submonoid.oneLE S).saturation.toSubmonoid
  have mem {x : S} : x ∈ U ↔ ∃ y, 1 ≤ x*y := Submonoid.mem_saturation_iff
  have upwards {x y : S} (h : x ≤ y) : x ∈ U → y ∈ U := fun hx =>
    let ⟨z,hz⟩ := mem.mp hx; mem.mpr ⟨z,hz.trans (mul_le_mul' h le_rfl)⟩
  have above {x : S} (h : 1 ≤ x) : x ∈ U := upwards h U.one_mem
  have s1 {a : ℕ} (h : 1 ≤ a) : 1 ≤ scalars (K := K) a := by simpa using scalars.monotone' h
  have htwo : scalars (K := K) 2 ≤ matrixClass 4 := (scalars.monotone' (by decide : 2 ≤ 4)).trans (diag_le 4)
  let unit : U := ⟨matrixClass 4,above ((s1 (by decide)).trans htwo)⟩
  let M : U := ⟨matrixClass d,above ((s1 hd).trans (diag_le d))⟩
  let cash : U := ⟨scalars k,above (s1 hk₀)⟩
  have upper (x : S) : x ≤ scalars 2 ^ rank x := (le_rank x).trans (by
    simpa using (scalars (K := K)).monotone' (Nat.lt_two_pow_self (n := rank x)).le)
  obtain ⟨f,hf,hm⟩ := log_price (Additive.ofMul unit) (Additive.ofMul M) (Additive.ofMul cash) (by
    intro x
    obtain ⟨z,hz⟩ := mem.mp x.toMul.property
    refine ⟨rank z,rank x.toMul.val,?_,?_⟩
    · change 1 ≤ (matrixClass 4)^rank z * x.toMul.val
      exact hz.trans (by rw [mul_comm]; exact mul_le_mul' ((upper z).trans (pow_le_pow_left' htwo _)) le_rfl)
    · exact (upper x.toMul.val).trans (pow_le_pow_left' htwo _)) (by
    intro c m n h
    obtain ⟨z,hz⟩ := mem.mp c.toMul.property
    have hp := currency_bound (k := k^n) (d := 4^(m+1)*d^n) (by positivity) hz (by
      change c.toMul.val * matrixClass 4^(m+1) * matrixClass d^n ≤ c.toMul.val * scalars k^n at h
      simpa only [matrixClass_mul,matrixClass_pow,map_pow,mul_assoc] using h)
    push_cast at hp
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_pow_comm (by positivity), ← Real.rpow_pow_comm (by positivity)] at hp
    have ht : 0 < exactRankExponent K := (by norm_num : (0:ℝ)<2).trans_le exactRankExponent_lower
    have hu : 1 < (4:ℝ)^exactRankExponent K := Real.one_lt_rpow (by norm_num) ht
    exact (lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) hk.le n) (lt_mul_of_one_lt_left (by positivity) (one_lt_pow₀ hu (by omega)))).not_ge hp)
  let l (x : U) := f (Additive.ofMul x)
  have ladd x y : l (x*y) = l x + l y := map_add f ..
  let price (x : U) := (2:ℝ)^(l x)
  let g : S →*o ℝ := {
    toFun x := if h : x ∈ U then price ⟨x,h⟩ else 0
    map_one' := by rw [dite_eq_left U.one_mem]; change (2:ℝ)^(f 0) = 1; simp
    map_mul' x y := by
      have hxy : x*y ∈ U ↔ x ∈ U ∧ y ∈ U := (Submonoid.oneLE S).saturation.2.mul_mem_iff
      by_cases hx : x ∈ U <;> by_cases hy : y ∈ U <;> simp [hx, hy, hxy]
      change price ((⟨x,hx⟩:U)*⟨y,hy⟩) = _
      dsimp only [price]; rw [ladd, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    monotone' := by
      intro x y hxy; dsimp only; split_ifs with hx hy
      · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact f.monotone' (show Additive.ofMul (⟨x,hx⟩ : U) ≤ Additive.ofMul ⟨y,hy⟩ from hxy)
      · exact (hy (upwards hxy hx)).elim
      all_goals first | exact le_rfl | apply Real.rpow_nonneg; norm_num }
  have good (x : U) : g x = price x := dite_eq_left x.2
  have gM : g (matrixClass 4) = 2 := by rw [good unit]; simp [price,l,hf]
  have nn (a : S) : 0 ≤ g a := by change 0 ≤ dite _ _ _; split <;> positivity
  let χ : Price K := ⟨g, nn, gM⟩
  refine ⟨χ, ?_⟩
  apply χ.scalar_le_cube hd
  change g cash ≤ g M
  rw [good cash, good M]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm

end OAI.MatrixMultiplication.AuxiliarySeparation
