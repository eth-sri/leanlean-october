module

public import Chazelle.Core.GranSize
public import Chazelle.Core.FactsL23
public import Chazelle.Core.FactsInterior
public import Chazelle.Core.UpPhaseGran
public import Chazelle.Core.SpecMerge

/-!
# WP-F merge assembly, part 1: mathematics

* weights are at most the size of the model (`weight_le_size`), so a semigranular family is
  `min γ size`-semigranular (`semigranular_min`); the size is at most the walk length;
* the degree of a normal form is the largest length of the chord lists of its regions
  (`degLe_of_lens`, `lens_of_degLe`);
* Lemma 2.3 bounds the chord count of a canonical normal form of a chain model
  (`nChords_le_canonical`);
* `Nat.clog` arithmetic for the cost bound.
-/

namespace Chazelle.Core

namespace MergeAsm

@[expose] public section

open Set

/-! ## Weights and sizes -/

theorem arcWt_le_size (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.size := by
  unfold Model.arcWt Model.size
  refine Set.ncard_le_ncard ?_ ((Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1)
  rintro p ⟨hp, hc, -⟩
  exact ⟨hp, hc⟩

theorem weight_le_size (M : Model) (F : Set (Set Point)) (U : Set Point) :
    M.weight F U ≤ M.size := by
  unfold Model.weight
  refine csSup_le' ?_
  rintro _ ⟨ab, -, rfl⟩
  exact arcWt_le_size M _ _

/-- A `γ`-semigranular family is `min γ size`-semigranular. -/
theorem semigranular_min {M : Model} {F : Set (Set Point)} {γ : ℕ} (h : M.Semigranular F γ) :
    M.Semigranular F (min γ M.size) :=
  fun U hU => le_min (h U hU) (weight_le_size M F U)

theorem size_le_n (M : Model) : M.size ≤ M.W.n := by
  unfold Model.size
  calc {p : ℕ | p < M.W.n ∧ M.counted p}.ncard ≤ (Set.Iio M.W.n).ncard :=
        Set.ncard_le_ncard (fun p hp => hp.1) (Set.finite_Iio _)
    _ = M.W.n := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]

theorem chainModel_n (C : Chain) : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _

/-- The size of a chain model: its `2 m` tour edges. -/
theorem chainModel_size (C : Chain) : (chainModel C).size = 2 * C.m := by
  unfold Model.size
  have e : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} =
      ((Finset.Ico 6 (2 * C.m + 6) : Finset ℕ) : Set ℕ) := by
    ext p
    simp only [mem_ofPred_eq, Finset.coe_Ico, Set.mem_Ico, chainModel_n]
    show p < 2 * C.m + 7 ∧ (6 ≤ p ∧ p < 2 * C.m + 6) ↔ _
    omega
  rw [e, Set.ncard_coe_finset, Nat.card_Ico]
  omega

/-- A `(γ + 1)`-semigranular family of a chain model is `(min γ (2 m) + 1)`-semigranular. -/
theorem semigranular_min_chain' {C : Chain} {F : Set (Set Point)} {γ : ℕ}
    (h : (chainModel C).Semigranular F (γ + 1)) :
    (chainModel C).Semigranular F (min γ (2 * C.m) + 1) := by
  refine Model.Semigranular.mono _ (semigranular_min h) ?_
  rw [chainModel_size]
  omega

/-! ## Degrees of normal forms -/

/-- **The degree bound from the chord lists** of the regions. -/
theorem degLe_of_lens {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {d : ℕ}
    (h : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d) : M.DegLe (N.F M Q) d := by
  obtain ⟨-, -, -, reg, hRC, -, -, hRO, -⟩ := id hN
  intro U hU
  obtain ⟨r, hr, rfl⟩ := hRC.2.2 U hU
  rw [Gran.deg_region hN hRC hRO hr]
  exact h r hr

/-- **The chord lists from the degree bound.** -/
theorem lens_of_degLe {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {d : ℕ}
    (h : M.DegLe (N.F M Q) d) : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d := by
  obtain ⟨-, -, -, reg, hRC, -, -, hRO, -⟩ := id hN
  intro r hr
  rw [← Gran.deg_region hN hRC hRO hr]
  exact h _ (hRC.1 r hr)

/-! ## Lemma 2.3 -/

/-- **Chord count of a canonical normal form** of a chain model (Lemma 2.3, with its constant
`c`). -/
theorem nChords_le_canonical {c : ℕ → ℕ} (hc : ∀ (M : Model) (Q : Polygon) (F : Set (Set Point))
      (γ D : ℕ), GoodModel M → M.ChordFamily Q F → M.DegLe F D → M.Granular F γ →
        F.ncard * (γ + 1) ≤ c D * (M.size + 1))
    {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ D : ℕ}
    (hN : IsCanonicalNF (chainModel C) Q N γ D) : N.nChords ≤ c D * (2 * C.m + 8) := by
  obtain ⟨hnf, hdeg, hgr, -⟩ := hN
  have h := hc _ Q _ γ D (Or.inl ⟨C, hP, rfl⟩) hnf.1 hdeg hgr
  rw [Gran.ncard_F hnf] at h
  have hs := size_le_n (chainModel C)
  rw [chainModel_n] at hs
  calc N.nChords ≤ N.nChords * (γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ c D * ((chainModel C).size + 1) := h
    _ ≤ c D * (2 * C.m + 8) := Nat.mul_le_mul_left _ (by omega)

/-! ## `Nat.clog` arithmetic -/

theorem clog_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

/-- `⌈log₂ (a b)⌉ ≤ ⌈log₂ a⌉ + ⌈log₂ b⌉`. -/
theorem clog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) a) (Nat.le_pow_clog (by norm_num) b)

theorem clog_le_self (a : ℕ) : Nat.clog 2 a ≤ a := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_two_pow_self).le

/-- `⌈log₂ (a b)⌉ ≤ a + ⌈log₂ b⌉`. -/
theorem clog_mul_le' (a b : ℕ) : Nat.clog 2 (a * b) ≤ a + Nat.clog 2 b :=
  (clog_mul_le a b).trans (by have := clog_le_self a; omega)

end

end MergeAsm

end Chazelle.Core
