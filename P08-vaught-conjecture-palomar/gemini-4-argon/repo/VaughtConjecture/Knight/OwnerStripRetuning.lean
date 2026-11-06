/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixAmbient
public import VaughtConjecture.Knight.PairedCoupledSections
public import VaughtConjecture.Knight.GradeCutLayerRows

/-! # Retuning a saturated strip from its owner's actual witness

An invisible image determines the source offset and the entire affine source
strip by clause 5. The prescribed witness on that strip produces a retuned
witness, rather than an assumed alignment map. Repaired composition is used
only on grade-short constructed sources; no composition principle for arbitrary
faithful transformations is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OwnerStripRetuning

open Transform Value ExtOrd SharpWitnessComposition

theorem invisible_preimage {K i : ℕ} {α : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) {x : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i)) :
    ∃ v : Ordinal.{0}, x = ofOrd (limitPart v + i) ∧
      ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
  have hinvis : ¬ SelfVis K (α x) := by
    rw [hx, selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    exact not_le_of_gt hi
  have hxinvis : ¬ SelfVis K x := fun hv => by
    have he := hα.clause5 x K (by rw [gTop_of_le le_rfl]; exact le_top) K le_rfl
    rw [hv] at he; exact hinvis he.symm
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (hxinvis (selfVis_bot K)).elim
  · exact (hxinvis (extVisibilityReplace_top K K)).elim
  have hv : finitePart v < K := not_le.mp fun h => hxinvis (selfVis_ofOrd_iff.mpr h)
  have orbit (n : ℕ) (hn : n ≤ K) :
      α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
    have he := hα.clause5 (ofOrd v) K (by rw [gTop_of_le le_rfl]; exact le_top) n hn
    rwa [hx, extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hv,
      ordinalReplace, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact hi),
      ordinalReplace, limitPart_limitPart_add_nat] at he
  have hoff : finitePart v = i := by
    have he := orbit (finitePart v) hv.le
    rw [decomposition, hx, ofOrd_inj] at he
    exact (Nat.cast_inj.mp ((add_right_inj (limitPart u)).mp he)).symm
  exact ⟨v, by rw [← hoff, decomposition], orbit⟩

theorem floor_bound {K i : ℕ} {β : ExtOrd → ExtOrd}
    (hβ : Witness (gTop K) β) {v : Ordinal.{0}} (hi : i < K)
    {γ : ExtOrd} (hγ : SelfVis K γ)
    (hb : γ ≤ β (ofOrd (limitPart v + i))) : γ ≤ β (ofOrd (limitPart v)) := by
  have he := hβ.clause5 (ofOrd (limitPart v + i)) K
    (by rw [gTop_of_le le_rfl]; exact le_top) 0 (Nat.zero_le _)
  rw [extVisibilityReplace_ofOrd, visibilityReplace,
    ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact hi),
    ordinalReplace, limitPart_limitPart_add_nat, Nat.cast_zero, add_zero] at he
  rw [he, ← evr_eq_self_of_selfVis hγ 0]
  exact evr_mono hb (Nat.zero_le _)

theorem exists_retuning_with_transfer {K i : ℕ} {α β τ : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) (hβ : Witness (gTop K) β) (hτ : Witness (gTop K) τ)
    {x γ M : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i))
    (hγ : SelfVis K γ) (hτbound : ∀ z, τ z ≤ γ) (hsat : τ (α x) = γ)
    (hp : γ ≤ β x) (hβbound : ∀ z, β z ≤ M) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd), Witness (gTop K) ρ ∧
      γ ≤ δ ∧ δ ≤ M ∧ SelfVis K δ ∧ ρ (ofOrd (limitPart u + K)) = δ ∧
      (∀ z n, n < K → α z = ofOrd (limitPart u + n) → ρ (α z) = β z) ∧
      (∀ z, ofOrd (limitPart u + K) ≤ α z → δ ≤ β z) ∧
      (∀ z, Short K z → min (ρ z) γ = min (τ z) γ) ∧ ∀ z, ρ z ≤ M := by
  classical
  have hK : 0 < K := Nat.zero_le i |>.trans_lt hi
  obtain ⟨v, hv, horbit⟩ := invisible_preimage hα hi hx
  have hbf : γ ≤ β (ofOrd (limitPart v)) := floor_bound hβ hi hγ (hv ▸ hp)
  have htf : τ (ofOrd (limitPart u)) = γ := le_antisymm (hτbound _)
    (floor_bound hτ hi hγ (by rw [← hx, hsat]))
  let η := FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v)
  have hη : Witness (gTop K) η :=
    (FiniteOrbitEmbedding.ray_step K (limitPart_idem v)).normalizedWitness
  let κ := (β ∘ η) ∘ trim K
  have hκ : Witness (gTop K) κ := (bounded_comp hη hβ le_rfl).witness
  have hκread (z : ExtOrd) (hz : Short K z) : κ z = β (η z) := by
    simp only [κ, Function.comp_apply, trim_of_short hz]
  let ρ := fun z => max (τ z) (κ z)
  let δ := β (ofOrd (limitPart v + K))
  have hδ : γ ≤ δ := hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add))
  have hδvis : SelfVis K δ := by
    have he := hβ.clause5 (ofOrd (limitPart v + K)) K
      (by rw [gTop_of_le le_rfl]; exact le_top) K le_rfl
    have hvv : SelfVis K (ofOrd (limitPart v + K)) := by
      rw [selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    rw [hvv] at he; exact he.symm
  have hstrip (n : ℕ) (hn : n ≤ K) :
      ρ (ofOrd (limitPart u + n)) = β (ofOrd (limitPart v + n)) := by
    have hshort : Short K (ofOrd (limitPart u + n)) :=
      Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hn⟩)
    have he : η (ofOrd (limitPart u + n)) = ofOrd (limitPart v + n) := by
      simp only [η, FiniteOrbitEmbedding.ray_ofOrd, limitPart_limitPart_add_nat,
        lt_self_iff_false, ite_false, ite_true, finitePart_limitPart_add_nat, min_eq_left hn]
    change max _ _ = _
    rw [hκread _ hshort, he, max_eq_right]
    exact (hτbound _).trans (hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add)))
  have hcap (z : ExtOrd) (hz : Short K z) : min (ρ z) γ = min (τ z) γ := by
    change min (max _ _) γ = _
    rw [hκread _ hz]
    have hray : η z = ⊥ ∨ ofOrd (limitPart u) ≤ z ∧ ofOrd (limitPart v) ≤ η z := by
      rcases ExtOrd.cases z with rfl | rfl | ⟨w, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨le_top, ofOrd_le_ofOrd.mpr le_self_add⟩
      · dsimp only [η]; rw [FiniteOrbitEmbedding.ray_ofOrd]
        by_cases hw : limitPart w < limitPart u
        · exact Or.inl (ite_eq_left hw)
        · rw [ite_eq_right hw]
          refine Or.inr ⟨ofOrd_le_ofOrd.mpr ((not_lt.mp hw).trans (limitPart_le w)), ?_⟩
          split_ifs <;> exact ofOrd_le_ofOrd.mpr le_self_add
    rcases hray with he | ⟨hzu, hzv⟩
    · rw [he, hβ.bot, max_bot_right]
    · have htz : τ z = γ := le_antisymm (hτbound _) (htf ▸ hτ.mono hzu)
      have hbz : γ ≤ β (η z) := hbf.trans (hβ.mono hzv)
      rw [htz, max_eq_right hbz, min_eq_right hbz, min_self]
  refine ⟨ρ, δ, hτ.max hκ, hδ, hβbound _, hδvis, hstrip K le_rfl, ?_, ?_, hcap,
    fun z => max_le ((hτbound z).trans (hδ.trans (hβbound _))) (hβbound _)⟩
  · intro z n hn hz
    obtain ⟨w, hw, hwo⟩ := invisible_preimage hα hn hz
    have no_lt (a b : Ordinal.{0})
        (ha : ∀ m ≤ K, α (ofOrd (limitPart a + m)) = ofOrd (limitPart u + m))
        (hb : ∀ m ≤ K, α (ofOrd (limitPart b + m)) = ofOrd (limitPart u + m)) :
        ¬ limitPart a < limitPart b := fun hlt => by
      have he := hα.mono (ofOrd_le_ofOrd.mpr (limitPart_add_nat_le_of_lt hlt K))
      have hz0 := hb 0 (Nat.zero_le K)
      simp only [Nat.cast_zero, add_zero] at hz0
      rw [ha K le_rfl, hz0, ofOrd_le_ofOrd] at he
      exact not_lt_of_ge he (by
        simpa only [Nat.cast_zero, add_zero] using add_lt_add_right (Nat.cast_lt.mpr hK) (limitPart u))
    have he : limitPart v = limitPart w :=
      le_antisymm (not_lt.mp (no_lt w v hwo horbit)) (not_lt.mp (no_lt v w horbit hwo))
    exact (congrArg ρ hz).trans
      ((hstrip n hn.le).trans (congrArg β (by simpa only [he] using hw)).symm)
  · intro z hz
    have hlow : ofOrd (limitPart v + K) ≤ z := by
      by_contra hn
      have hlt := not_le.mp hn
      rcases ExtOrd.cases z with rfl | rfl | ⟨w, rfl⟩
      · exact not_ofOrd_le_bot _ (hα.bot ▸ hz)
      · exact not_lt_of_ge le_top hlt
      · obtain ⟨t, ht, hwt⟩ :=
          (Ordinal.lt_add_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK))).mp (ofOrd_lt_ofOrd.mp hlt)
        obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (ht.trans (Ordinal.natCast_lt_omega0 K))
        have he := hz.trans (hα.mono (ofOrd_le_ofOrd.mpr hwt))
        rw [horbit n (Nat.cast_lt.mp ht).le, ofOrd_le_ofOrd] at he
        exact not_lt_of_ge he (add_lt_add_right ht (limitPart u))
    exact hβ.mono hlow
