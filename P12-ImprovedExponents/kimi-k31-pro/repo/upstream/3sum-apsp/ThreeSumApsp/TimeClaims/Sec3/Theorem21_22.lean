module

public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

@[expose] public section

namespace ThreeSumApsp

/-- Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. -/
theorem Theorem21a.of_CH20_VW13 (M : DetTimeModel) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.Theorem_21a M := by
  obtain ⟨c, E₂, Num₂, size₂, hc, hE₂, hNum₂, hsize₂, hsize₂_pos, hVW⟩ := hVW
  intro κ hκ
  obtain ⟨E₁, Num₁, mag₁, N, c', κ', hE₁, hNum₁, hN, hpos, hCH⟩ := hCH κ hκ
  have hN' := hN.isPowLittleO
  have hwords : IsPowLittleO (fun n : ℕ => 1 + logU (mag₁ n)) 0 :=
    ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).isPowLittleO
  refine ⟨fun n => E₁ n + Num₁ n * (E₂ (N n) * (1 + logU (mag₁ n))), fun n => Num₁ n * Num₂ (N n),
    fun n => c * mag₁ n, fun n => size₂ (N n), c * c', κ', ?_, ?_, ?_, fun n hn => ?_,
    fun T hT => ?_⟩
  · exact hE₁.isPowLittleO.add ((hNum₁.isPowLittleO.mul
      ((hE₂.comp hN' (by norm_num) (by norm_num)).mul hwords)).mono (by norm_num))
  · exact (hNum₁.isPowLittleO.mul
      (hNum₂.isPowLittleO.comp hN' (by norm_num) (by norm_num))).mono (by norm_num)
  · exact (hsize₂.isPowLittleO.comp hN' (by norm_num) (by norm_num)).mono (by norm_num)
  · obtain ⟨hN1, hmag1, hmag⟩ := hpos n hn
    refine ⟨hsize₂_pos _ hN1, one_le_mul_of_one_le_of_one_le hc hmag1, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmag (zero_le_one.trans hc)
  · obtain ⟨T', hT', hb⟩ := hCH _ (hVW T hT)
    exact ⟨T', hT', fun n hn => (hb n hn).trans (le_of_eq (by ring))⟩

/-- Plug a uniform Exact Triangle bound into Theorem 21(a). -/
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) :
    Claim.ThreeSumInLittleO M (2 - δ / 2) := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex
  have hsizes := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
    (by linarith) (by norm_num)
  have hwords := (((isPowPolylog_const 1).add
    (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow 2).isPowLittleO
  have htotal : IsPowLittleO (fun n => E n + Num n * uniformTime K δ e (size n) (mag n))
      (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((hsizes.mul hwords).const_mul K)).mono (le_of_eq (by push_cast; ring)))
  exact ⟨T', hT', htotal.upperPowLittleO.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩

/-- An inclusion between two classes of running times carries over to the claims. -/
theorem Claim.SolvedAlongPow.mono {S : (ℕ → ℝ → ℝ) → Prop} {Cls Cls' : (ℕ → ℝ) → ℝ → Prop}
    {a b : ℝ} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp
