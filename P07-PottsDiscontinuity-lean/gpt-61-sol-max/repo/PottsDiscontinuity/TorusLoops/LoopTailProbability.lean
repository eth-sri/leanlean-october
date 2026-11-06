module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.LoopTailUnionBound

/-!
# Finite-energy winding-loop tail after the root-set union bound

Combining the seam-closing estimate with the root-set exploration estimate
gives an explicit probability bound for a large homological loop count.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops


open PottsDiscontinuity.TorusRC

variable {N M : ℕ}

noncomputable section

/-- The two deleted seams contain at most `N + M` indexed edges. -/
theorem rectangleSeamIndices_card_le_add
    (hNp : 0 < N) (hMp : 0 < M) :
    (rectangleSeamIndices (N := N) (M := M)).card ≤ N + M := by
  
  let : NeZero N := ⟨Nat.ne_of_gt hNp⟩
  let : NeZero M := ⟨Nat.ne_of_gt hMp⟩
  let sx : Finset (Fin N × Fin M) :=
    Finset.univ.filter fun v => v.1.val = 0
  let sy : Finset (Fin N × Fin M) :=
    Finset.univ.filter fun v => v.2.val = 0
  have hsplit : rectangleSeamIndices (N := N) (M := M) = sx ∪ sy := by
    ext v
    simp [rectangleSeamIndices, sx, sy]
  have hsx : sx = Finset.univ.image  fun j  => (0, j)  := by
    aesop
  have hsy : sy = Finset.univ.image  fun i  => (i, 0)  := by
    aesop
  have hsx_card : sx.card = M := by
    rw [hsx, Finset.card_image_of_injective _  fun ⦃a b⦄ => congrArg Prod.snd ]
    simp
  have hsy_card : sy.card = N := by
    rw [hsy, Finset.card_image_of_injective _  fun ⦃a b⦄ => congrArg Prod.fst ]
    simp
  rw [hsplit]
  calc
    (sx ∪ sy).card ≤ sx.card + sy.card := Finset.card_union_le _ _
    _ = M + N := by rw [hsx_card, hsy_card]
    _ = N + M := Nat.add_comm _ _

section

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (m : ℕ)


/-- Corrected (3.17) followed by the exploration union bound, before division
by the finite-energy cost of closing all seams. -/
theorem torusRCProbability_windingTail_mul_seam_le_rootUnion
     :
    (1 - (rcCriticalParameter q).val) ^
        (rectangleSeamIndices (N := N) (M := M)).card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      (2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
        ((m - 3 * N + 1) / 2) := Trans.trans (torusRCProbability_windingTail_le_rectangleFKCrossings hN hM hNp hMp q m)
                                   (rectangleFKCrossingEvent_probability_le_rootUnion hN hM q ((m - 3 * N + 1) / 2))

/-- The winding-loop tail bound with its finite-energy cost divided out and
with the seam count replaced by the linear estimate `N + M`. -/
theorem torusRCProbability_windingTail_le_rootUnion
     :
    phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
       (2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
        ((m - 3 * N + 1) / 2)  /
        (1 - (rcCriticalParameter q).val) ^ (N + M) := by
  have hα  := sub_pos.mpr (criticalParameter_lt_one q)
  
  
  
  have hmul := torusRCProbability_windingTail_mul_seam_le_rootUnion
    hN hM hNp hMp q m
  have hprob :
      phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
         (2 ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
          ((m - 3 * N + 1) / 2)  /
          (1 - (rcCriticalParameter q).val) ^
            (rectangleSeamIndices (N := N) (M := M)).card := by
    apply (le_div_iff₀ (pow_pos hα _)).2
    all_goals grind
  
  
  exact hprob.trans (div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (by norm_num ) _)
                                                    (pow_nonneg (by
                                                                   unfold rectangleFreeOneArmProbability
                                                                   exact NNReal.coe_nonneg _) _)) (pow_pos hα _ ) (pow_le_pow_of_le_one hα.le (by
                                                                                                                        linarith [criticalParameter_pos q]) (rectangleSeamIndices_card_le_add hNp hMp)))

end

end

end PottsDiscontinuity.TorusLoops
