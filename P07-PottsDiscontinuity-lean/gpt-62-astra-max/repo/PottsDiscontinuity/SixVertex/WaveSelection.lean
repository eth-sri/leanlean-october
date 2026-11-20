module
public import PottsDiscontinuity.SixVertex.BaseWaveSign
public import PottsDiscontinuity.SixVertex.SupportedBranch
public import PottsDiscontinuity.SixVertex.Cor34Spectral

/-! # Selection of the physical Perron branch

After a constant phase adjustment, the limiting Bethe wave is nonnegative on
all row states, and positive on every state supporting the limiting matrix.
Consequently its continuation pairs nontrivially with the physical positive
Perron vector, identifying the eigenvalue without diagonalizing the limit. -/
@[expose] public section
open Matrix Filter Topology Complex
namespace PottsDiscontinuity.SixVertex
open PerronFrobenius BetheAnsatz

private def separatedState {n N : ℕ} (h : 2*n ≤ N) : IndependentState N n := by
  let e : Fin n ↪ Fin N := ⟨fun i => ⟨2*i.val,by omega⟩,fun i j hij => Fin.ext (by
    have h : 2*i.val = 2*j.val := congrArg Fin.val hij; omega)⟩
  refine ⟨⟨Finset.univ.map e,by simp⟩,?_⟩
  intro i hi hnext
  obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hnext
  have hv := congrArg Fin.val hb
  rw [nxt_val_of_lt (by change 2*a.val+1 < N; omega)] at hv
  change 2*b.val = 2*a.val+1 at hv; omega

lemma select_physical_branch {N n : ℕ} (hn : 0 < n) (hbound : 2*n ≤ N)
    {P : ℝ → Fin n → ℝ} (hP : ContinuousAt P 0) (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    {μ : ℝ → ℂ} (he : ∀ᶠ ε in 𝓝[<] (0:ℝ),
      (transferBlock N (Real.sqrt (2-2/ε)) n).map (algebraMap ℝ ℂ) *ᵥ blockWave (1/ε) (P ε) =
        μ ε • blockWave (1/ε) (P ε)) :
    ∀ᶠ ε in 𝓝[<] (0:ℝ), μ ε = (pfRoot (transferBlock N (Real.sqrt (2-2/ε)) n):ℂ) := by
  classical
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  let A := cor34_normalizedTransferBlock N n
  let c := fun ε : ℝ => Real.sqrt (2-2/ε)
  let a := fun ε : ℝ => ((-2/ε)^n)⁻¹
  let w := fun x : State N n => sineLiftWeight ((N-n:ℕ):ℝ) (compressed (positions x))
  let ψ := fun ε (x : State N n) => (slaterPhase n)⁻¹ * cor34_normalizedCoordinate ε (P ε) (positions x)
  have hA (x y) := ((cor34_normalizedTransferBlock_entry_analyticAt (N := N) (n := n) x y 0).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0)))
  rw [cor34_normalizedTransferBlock_zero] at hA
  have hψ (x : State N n) : Tendsto (fun ε => (ψ ε x).re) (𝓝[<] 0) (𝓝 (w x)) := by
    have h := (cor34_normalizedCoordinate_tendsto hP (positions x)).const_mul (slaterPhase n)⁻¹
    rw [hP0,base_wave_formula (by omega),inv_mul_cancel_left₀ (slaterPhase_ne_zero n)] at h
    exact (continuous_re.continuousAt.tendsto.comp h).mono_left nhdsWithin_le_nhds
  let x := separatedState hbound
  have hx : infinityBlock N n x.val (rotateIndependent x).val = 1 := infinityRestriction_rotate hn x
  have hs := eventually_eq_of_supported_wave (μ := fun ε => (a ε:ℂ)*μ ε)
    (ρ := fun ε => a ε * pfRoot (transferBlock N (c ε) n)) (A := A) (ψ := ψ)
    hA hψ (fun i => (base_chamber_sign hn hbound i).1)
    (fun i hi j => infinityBlock_eq_zero_of_not_noConsecutiveUp hn i j
      (fun h => ((base_chamber_sign hn hbound i).2 h).ne' hi)) ⟨_,_,hx ▸ zero_lt_one⟩
  have ha {ε : ℝ} (hε : ε < 0) : 0 < a ε := inv_pos.mpr (pow_pos (div_pos_of_neg_of_neg (by norm_num) hε) _)
  apply Filter.Eventually.mp (hs ?_) _
  swap
  · filter_upwards [self_mem_nhdsWithin] with ε hε h
    rw [ofReal_mul] at h; exact mul_left_cancel₀ (ofReal_ne_zero.mpr (ha hε).ne') h
  filter_upwards [he,self_mem_nhdsWithin] with ε he hε
  have hc : 0 < c ε := Real.sqrt_pos.mpr (sub_pos.mpr ((div_neg_of_pos_of_neg (by norm_num) hε).trans (by norm_num)))
  have hm : A ε = a ε • transferBlock N (c ε) n := cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε
  obtain ⟨v,hv,hv'⟩ := (transferBlock_perronFrobenius hc (show n ≤ N by omega)).2.2.1
  refine ⟨fun i j => ?_, ?_, ⟨v,hv,?_⟩,?_⟩
  · rw [hm]; exact mul_nonneg (ha hε).le (transferBlock_nonneg hc.le n i j)
  · ext i j; exact cor34_normalizedTransferBlock_symm _ j i
  · rw [hm,smul_mulVec,hv',smul_smul]
  · have hmc : (A ε).map (algebraMap ℝ ℂ) = (a ε:ℂ) • (transferBlock N (c ε) n).map (algebraMap ℝ ℂ) := by
      rw [hm]; ext i j; simp [map_apply,Matrix.smul_apply]
    have hv : ψ ε = ((slaterPhase n)⁻¹ * ((-ε/2:ℝ):ℂ)^cor34_pairCount n) • blockWave (N := N) (1/ε) (P ε) := by
      funext i; simp only [ψ,cor34_normalizedCoordinate_eq_scaled_coordinateWave _ _ _ (ne_of_lt hε)]
      simp [blockWave,mul_assoc]
    rw [hmc,hv,smul_mulVec,mulVec_smul,he]; simp only [smul_smul]; congr 1; ring
end PottsDiscontinuity.SixVertex
