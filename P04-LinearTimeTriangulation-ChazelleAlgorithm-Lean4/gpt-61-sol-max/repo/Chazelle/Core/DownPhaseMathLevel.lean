module

public import Chazelle.Core.DownPhaseDrvMStep
public import Chazelle.Core.DownPhaseDrvCount
public import Chazelle.Core.FactsL23
public import Chazelle.Core.RestoreRound

/-!
# Down phase, math (D10 rest): the chord count of one level

The count bound (I3) of the level invariant (design `docs/design-downphase-driver.md` §2.2, §4.3)
follows from three facts, proved here; the arithmetic is `DownPhaseMathCount`.

* **Lemma 2.3 per region** (`lemma23_chain`): a `γ`-granular chord family of degree `≤ D` of a
  chain of a simple host has `|F| (γ + 1) ≤ 140 (D + 2) (2 m + 1)` chords (the explicit constant of
  `lemma23`).
* **One level** (`level_count`): with region chains `C R` of at most `nk` (or, clockwise, the
  mirrored `nk`) points and `γ`-granular region maps `F R` of degree `≤ D_H`, the family after
  the extraction satisfies
  `|stepFam Q S F| (γ + 1) ≤ |S| (γ + 1) + 560 (D_H + 2) (n + 4 |S|)`
  (Σ over the regions of the host sizes is `≤ n + 4|S|`, `DownDrv.sum_nk_le`, in each
  orientation).
* **The restoration factor** (`round_ncard`): one restoration round (`Restore.RoundData`, at most
  one new chord per region) at most doubles the count: `|S ∪ E| ≤ 2 |S| + 1`;
  `rounds_ncard`: after `t` rounds, `|S_t| + 1 ≤ 2^t (|S_0| + 1)`.
* `level_bound` combines them into the hypothesis of `DownMath.cnt_step` with `A = 2^t`,
  `B = 560 (D_H + 2)`, `G = γ + 1`.
* `trans_count`: Lemma 2.3 for the top chain (the input of `DownMath.cnt_trans`).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (regionsIn)
open DownHost DownStep Mir

/-! ## Lemma 2.3 in a chain model, explicit constant -/

theorem chainModel_size (C : Chain) : (chainModel C).size = 2 * C.m := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  unfold Model.size
  have : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} =
      Set.Ico 6 (2 * C.m + 6) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, hn]
    change p < 2 * C.m + 7 ∧ (6 ≤ p ∧ p < 2 * C.m + 6) ↔ _
    omega
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
  omega

/-- **Lemma 2.3 for a chain model** (explicit constant): `|F| (γ + 1) ≤ 140 (D + 2) (2 m + 1)`. -/
theorem lemma23_chain {C : Chain} (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    {γ D : ℕ} (hF : (chainModel C).ChordFamily Q F) (hdeg : (chainModel C).DegLe F D)
    (hgran : (chainModel C).Granular F γ) :
    F.ncard * (γ + 1) ≤ 140 * (D + 2) * (2 * C.m + 1) := by
  have hM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk _ hM
  rw [← chainModel_size]
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact absurd hgran.1 (hW.not_semigranular_zero hAdm hfin hne hp₀ hc₀)
  · have h := hW.lemma23_walk hAdm hfin hdeg hgran
    calc F.ncard * (γ + 1) ≤ 2 * (F.ncard * γ) := by nlinarith
      _ ≤ 2 * (2 * (D + 2) * (5 * (chainModel C).W.n)) := Nat.mul_le_mul_left _ h
      _ ≤ 2 * (2 * (D + 2) * (5 * (7 * ((chainModel C).size + 1)))) := by gcongr
      _ = 140 * (D + 2) * ((chainModel C).size + 1) := by ring

/-! ## The host sizes -/

theorem interiorModel_n (Q : Polygon) : (interiorModel Q).W.n = Q.n :=
  interiorWalk_n Q

/-- **The host sizes** sum to at most `n + 4 |S|`. -/
theorem sum_nk_le' {Q : Polygon} (hQ : Q.Simple) {S : Set (Set Point)}
    (hFam : (interiorModel Q).ChordFamily Q S) (T : Finset (Set Point))
    (hT : ∀ R ∈ T, R ∈ (interiorModel Q).regions S) :
    ∑ R ∈ T, nk (interiorModel Q) S R ≤ Q.n + 4 * S.ncard := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have hsum := DownDrv.sum_nk_le hM hFam.2.1 hFam.1
  have hsys := hM.sys _ hFam.2.1 hFam.1
  have hRfin : ((interiorModel Q).regions S).Finite :=
    hsys.regionsIn_finite hM.preconn hM.nonempty subset_rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, interiorModel_n] at hsum
  refine le_trans (Finset.sum_le_sum_of_subset fun R hR => ?_) hsum
  simp_all

/-! ## One level -/

/-! ## Restoration rounds -/

/-- **The level bound** in the form of `DownMath.cnt_step`: if one level gives `K₁` chords with
`K₁ (γ + 1) ≤ K (γ + 1) + B (n + 4 K)` and the restoration rounds give `K' + 1 ≤ A (K₁ + 1)`,
then `K' (γ + 1) ≤ A ((K + 1) (γ + 1) + B (n + 4 K))`. -/
theorem level_bound {K K₁ K' A B n γ : ℕ} (h1 : K₁ * (γ + 1) ≤ K * (γ + 1) + B * (n + 4 * K))
    (h2 : K' + 1 ≤ A * (K₁ + 1)) :
    K' * (γ + 1) ≤ A * ((K + 1) * (γ + 1) + B * (n + 4 * K)) := by
  calc K' * (γ + 1) ≤ (K' + 1) * (γ + 1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    _ ≤ A * (K₁ + 1) * (γ + 1) := Nat.mul_le_mul_right _ h2
    _ = A * (K₁ * (γ + 1) + (γ + 1)) := by ring
    _ ≤ A * (K * (γ + 1) + B * (n + 4 * K) + (γ + 1)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right h1 _)
    _ = A * ((K + 1) * (γ + 1) + B * (n + 4 * K)) := by ring

/-! ## The transition -/

/-- **Lemma 2.3 for the top chain**: a `γ'_p`-canonical map of the top chain (`m = n - 1`, cap
`4`) has `K₀ (γ'_p + 1) ≤ 840 (2 (n - 1) + 1)` chords (the hypothesis of
`DownMath.cnt_trans`). -/
theorem trans_count {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hN : IsCanonicalNF (chainModel C) Q N γ 4) :
    (N.F (chainModel C) Q).ncard * (γ + 1) ≤ 840 * (2 * C.m + 1) := by
  obtain ⟨hNF, hdeg, hgran, -⟩ := hN
  have := lemma23_chain hP hNF.1 hdeg hgran
  omega

end

end DownMath

end Chazelle.Core
