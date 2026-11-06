module

public import Chazelle.Golf

public import Chazelle.Core.GranNFBounds

/-!
# WP-F, init part 12: the environment of a run

From the descriptor of the model and a valid normal form: the environment `envOf` (kind and
chain length read from the descriptor), its hypotheses `Env.Good` (`envOf_good`), the number of
counted edges computed by the header (`szOf_eq`), and the correctness of the static arrays
(`statOK_of`).
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

/-- The environment of a run. -/
noncomputable def envOf (M : Model) (P : Polygon) (N : NF) (reg : ℕ → Set Point) (γ D kind m : ℕ) :
    Env := ⟨M, Qof P, N, reg, γ, D, decide (kind = 0), m⟩

/-- The model kind and chain length read from a descriptor describe the counted edges. -/
theorem desc_count {P : Polygon} {mem : ℕ → ℕ} {MD : ℕ} {M : Model}
    (h : ModelDescAt mem MD (Qof P) M) :
    CountDesc M (decide (mem MD = 0)) (mem (MD + 3)) ∧
      (decide (mem MD = 0) = true → M.W.n = 2 * mem (MD + 3) + 7) ∧
      szOf P (mem MD) (mem (MD + 3)) = cntIn (decide (mem MD = 0)) (mem (MD + 3)) 0 M.W.n := by
  rcases h with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩
  · have hm : mem (MD + 3) = C.m := hC.2.2.2.1
    have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta
    rw [hm, h0]
    simp only [decide_true]
    refine ⟨⟨fun _ => by rw [hn]; omega, fun p hp => ?_⟩, fun _ => hn, ?_⟩
    · simp [chainModel]
    · unfold szOf cntIn; rw [hn]; simp only [ite_true]; omega
  · rw [h1]
    simp only [show (1 : ℕ) ≠ 0 by decide, decide_false]
    refine ⟨⟨fun h => absurd h (by decide), fun p hp => ?_⟩, fun h => absurd h (by decide), ?_⟩
    · simp [interiorModel]
    · unfold szOf cntIn
      simp only [Bool.false_eq_true, ite_false, ite_eq_right (show (1 : ℕ) ≠ 0 by decide),
        Nat.sub_zero]
      show P.n = (interiorWalk (Qof P)).n
      rw [NFLoc.interiorWalk_n]
      exact (shear_n _ _).symm

/-- **The environment satisfies its hypotheses.** -/
theorem envOf_good {P : Polygon} {mem : ℕ → ℕ} {MD : ℕ} {M : Model} {N : NF}
    {reg : ℕ → Set Point} {γ D : ℕ} (hMD : ModelDescAt mem MD (Qof P) M) (hGM : GoodModel M)
    (hNF : IsNF M (Qof P) N) (hRC : RegionCorr M (Qof P) N reg)
    (hCS : ChordSidesOK M (Qof P) N reg) (hRO : RegionsOK M (Qof P) N reg)
    (hne : (N.F M (Qof P)).Nonempty) :
    (envOf M P N reg γ D (mem MD) (mem (MD + 3))).Good := by
  obtain ⟨hcd, hn, -⟩ := desc_count hMD
  exact ⟨walkAx_of_goodModel hGM, hGM, hNF, hRC, hCS, hRO, hne, hcd, hn⟩

theorem envOf_sz {P : Polygon} {mem : ℕ → ℕ} {MD : ℕ} {M : Model} {N : NF}
    {reg : ℕ → Set Point} {γ D : ℕ} (hMD : ModelDescAt mem MD (Qof P) M) :
    (envOf M P N reg γ D (mem MD) (mem (MD + 3))).sz = szOf P (mem MD) (mem (MD + 3)) :=
  (desc_count hMD).2.2.symm

/-- The chain length of a well-formed chain descriptor is below `64 n`. -/
theorem chain_m_le {P : Polygon} {E : ℕ} {mem : ℕ → ℕ} {MD : ℕ} {M : Model}
    (hwf : ModelDescWF P E mem MD) (h : ModelDescAt mem MD (Qof P) M) (h0 : mem MD = 0) :
    mem (MD + 3) ≤ 64 * P.n := by
  rcases h with ⟨-, H, C, hC, rfl⟩ | ⟨h1, -, -⟩
  · obtain ⟨hl, hwfH, -, -⟩ := (hwf.2 h0).2 H C hC
    have := NFLoc.chain_n_le hC hl hwfH
    have hm : mem (MD + 3) = C.m := hC.2.2.2.1
    have := C.m_lt
    omega
  · omega

/-- The number of counted edges is below the word bound. -/
theorem szOf_le {P : Polygon} {E W : ℕ} {mem : ℕ → ℕ} {MD : ℕ} {M : Model}
    (hwf : ModelDescWF P E mem MD) (h : ModelDescAt mem MD (Qof P) M)
    (hW : hostWords P.n ≤ W) : szOf P (mem MD) (mem (MD + 3)) ≤ W := by
  unfold szOf hostWords at *
  split_ifs with h0
  · have := chain_m_le hwf h h0; omega
  · omega

end

end Gran

end Chazelle.Core
