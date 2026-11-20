/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerRows
public import VaughtConjecture.Knight.PairedCoupledSections
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient

@[expose] public section

namespace VaughtConjecture.Knight.OwnerStripRetuning

open Transform Value ExtOrd SharpWitnessComposition

/-- A visible lower bound at an invisible source already holds at its floor.
This includes a plateau whose interior output equals the agreement cap. -/
theorem floor_bound {K i : ℕ} {β : ExtOrd → ExtOrd}
    (hβ : Witness (gTop K) β) {v : Ordinal.{0}} (hi : i < K)
    {γ : ExtOrd} (hγ : SelfVis K γ)
    (hb : γ ≤ β (ofOrd (limitPart v + i))) : γ ≤ β (ofOrd (limitPart v)) := by
  have he := hβ.comm (ofOrd (limitPart v + i)) (k := K) (i := 0) le_rfl (Nat.zero_le _)
  rw [extVisibilityReplace_of_finitePart_lt (by rwa [finitePart_limitPart_add_nat]),
    limitPart_limitPart_add_nat, Nat.cast_zero, add_zero] at he
  rw [he, ← evr_eq_self_of_selfVis hγ 0]
  exact evr_mono hb (Nat.zero_le _)

/-- Distinct original strips cannot both map affinely onto the same strip.
This is proved from the actual monotone witness, not a source-order record. -/
theorem strip_unique {K : ℕ} {α : ExtOrd → ExtOrd} (hα : Witness (gTop K) α)
    (hK : 0 < K) {u v w : Ordinal.{0}}
    (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
    (hw : ∀ n ≤ K, α (ofOrd (limitPart w + n)) = ofOrd (limitPart u + n)) :
    limitPart v = limitPart w :=
  le_antisymm (strip_le_of_affine hα.mono hK hv hw le_rfl)
    (strip_le_of_affine hα.mono hK hw hv le_rfl)

/-- The affine endpoint reflects order even though the witness need not be
injective elsewhere. -/
theorem endpoint_reflects {K : ℕ} {α : ExtOrd → ExtOrd} (hα : Witness (gTop K) α)
    (hK : 0 < K) {u v : Ordinal.{0}}
    (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
    {z : ExtOrd} (hz : ofOrd (limitPart u + K) ≤ α z) :
    ofOrd (limitPart v + K) ≤ z := by
  by_contra hn
  have hlt := not_le.mp hn
  rcases ExtOrd.cases z with rfl | rfl | ⟨w, rfl⟩
  · exact not_ofOrd_le_bot _ (hα.bot ▸ hz)
  · trivial
  · have hKn : (K : Ordinal.{0}) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
    obtain ⟨t, ht, hwt⟩ := Ordinal.lt_add_iff hKn |>.mp (ofOrd_lt_ofOrd.mp hlt)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (ht.trans (Ordinal.natCast_lt_omega0 K))
    have hnK : n < K := Nat.cast_lt.mp ht
    have he := hz.trans (hα.mono (ofOrd_le_ofOrd.mpr hwt))
    rw [hv n hnK.le, ofOrd_le_ofOrd] at he
    (simp_all <;> omega)

theorem invisible_readback {K n : ℕ} {α : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) {u v : Ordinal.{0}}
    (hv : ∀ m ≤ K, α (ofOrd (limitPart v + m)) = ofOrd (limitPart u + m))
    {z : ExtOrd} (hn : n < K) (hz : α z = ofOrd (limitPart u + n)) :
    z = ofOrd (limitPart v + n) := by
  obtain ⟨w, hw, hwo⟩ := read_strip_at hα.bounded hn hz
  have he := strip_unique hα (Nat.zero_le n |>.trans_lt hn) hv hwo
  simp_all

private theorem ray_cases (K : ℕ) (u v : Ordinal.{0}) (x : ExtOrd) :
    FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x = ⊥ ∨
      ofOrd (limitPart u) ≤ x ∧ ofOrd (limitPart v) ≤
        FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨w, rfl⟩
  · tauto
  · exact Or.inr ⟨le_top, ofOrd_le_ofOrd.mpr le_self_add⟩
  · rw [FiniteOrbitEmbedding.ray_ofOrd]
    by_cases hw : limitPart w < limitPart u
    · simp_all
    · rw [ite_eq_right hw]
      refine Or.inr ⟨ofOrd_le_ofOrd.mpr ((not_lt.mp hw).trans (limitPart_le w)), ?_⟩
      aesop

/-- Construct the replacement strip directly from two owner witnesses and a
saturated invisible incidence. Every short source retains its ORIGINAL cap,
including unused strip points and all supported controller coordinates. -/
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
      ∀ z, Short K z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨v, hv, horbit⟩ := read_strip_at hα.bounded hi hx
  have hbf : γ ≤ β (ofOrd (limitPart v)) := floor_bound hβ hi hγ (hv ▸ hp)
  have htf : τ (ofOrd (limitPart u)) = γ := le_antisymm (hτbound _)
    (floor_bound hτ hi hγ (by simp_all))
  let η := FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v)
  have hη : Witness (gTop K) η :=
    (FiniteOrbitEmbedding.ray_step K (limitPart_idem v)).normalizedWitness
  let κ := (β ∘ η) ∘ trim K
  have hκ : Witness (gTop K) κ := (hβ.bounded.comp hη.bounded le_rfl).witness
  have hκread (z : ExtOrd) (hz : Short K z) : κ z = β (η z) := by
    simp only [κ, Function.comp_apply, trim_of_short hz]
  let ρ := fun z => max (τ z) (κ z)
  let δ := β (ofOrd (limitPart v + K))
  have hδ : γ ≤ δ := hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add))
  have hδvis : SelfVis K δ := by
    have he := hβ.clause5 (ofOrd (limitPart v + K)) K
      (by rw [gTop_of_le le_rfl]; simp) K le_rfl
    have hvv : SelfVis K (ofOrd (limitPart v + K)) := by
      rw [selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    grind
  have hstrip (n : ℕ) (hn : n ≤ K) :
      ρ (ofOrd (limitPart u + n)) = β (ofOrd (limitPart v + n)) := by
    have hshort : Short K (ofOrd (limitPart u + n)) :=
      Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; assumption⟩)
    have he : η (ofOrd (limitPart u + n)) = ofOrd (limitPart v + n) := by
      simp only [η, FiniteOrbitEmbedding.ray_ofOrd, limitPart_limitPart_add_nat,
        lt_self_iff_false, ite_false, ite_true, finitePart_limitPart_add_nat, min_eq_left hn]
    change max _ _ = _
    rw [hκread _ hshort, he, max_eq_right]
    exact (hτbound _).trans (hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add)))
  have hcap (z : ExtOrd) (hz : Short K z) : min (ρ z) γ = min (τ z) γ := by
    change min (max _ _) γ = _
    rw [hκread _ hz]
    rcases ray_cases K u v z with he | ⟨hzu, hzv⟩
    · change η z = ⊥ at he
      rw [he, hβ.bot, max_bot_right]
    · have htz : τ z = γ := le_antisymm (hτbound _) (htf ▸ hτ.mono hzu)
      simp_all
  refine ⟨ρ, δ, hτ.max hκ, hδ, hβbound _, hδvis, hstrip K le_rfl, ?_, ?_, hcap⟩
  · intro z n hn hz
    rw [hz, hstrip n hn.le, invisible_readback hα horbit hn hz]
  · intro z hz
    exact hβ.mono (endpoint_reflects hα (Nat.zero_le i |>.trans_lt hi) horbit hz)

end VaughtConjecture.Knight.OwnerStripRetuning
