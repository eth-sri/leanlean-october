/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Tactic.DeriveFintype
public import VaughtConjecture.Knight.GradeCutLayerRows
public import VaughtConjecture.Knight.PairedCoupledSections
public import VaughtConjecture.Knight.SourcePrefixAmbient
public import VaughtConjecture.Knight.AlignedCutEncoding

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace OwnerLocalEndpoint

/-- Rounding to the `j`-visible endpoint of the strip of `x`. -/
noncomputable abbrev endpoint (j : ℕ) (x : ExtOrd) : ExtOrd := extVisibilityReplace x j j

theorem le_endpoint (j : ℕ) (x : ExtOrd) : x ≤ endpoint j x := le_extVisibilityReplace_self x j

theorem selfVis_endpoint (j : ℕ) (x : ExtOrd) : SelfVis j (endpoint j x) := by
  unfold endpoint
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot j
  · exact extVisibilityReplace_top j j
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs <;> omega

theorem endpoint_of_selfVis {j : ℕ} {x : ExtOrd} (h : SelfVis j x) : endpoint j x = x := h

theorem endpoint_mono {j : ℕ} {x y : ExtOrd} (h : x ≤ y) : endpoint j x ≤ endpoint j y :=
  evr_mono h le_rfl

theorem endpoint_ne_top {j : ℕ} {x : ExtOrd} (h : x ≠ ⊤) : endpoint j x ≠ ⊤ := by
  unfold endpoint
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_ne_top
  · exact absurd rfl h
  · rw [extVisibilityReplace_ofOrd]; exact ofOrd_ne_top _

variable {ι : Type*}

/-- The owner-local saturation hypotheses: `τ` is bottom-preserving, monotone and bounded by the
positive cap `γ`; the owner `c` exceeds the cap under `p`; the face equation holds on every
argument; every source observation is proper; and the owner's source value is `j`-visible. -/
structure Saturation (j : ℕ) (s p : ι → ExtOrd) (c : ι) (τ : ExtOrd → ExtOrd) (γ : ExtOrd) :
    Prop where
  bot : τ ⊥ = ⊥
  mono : Monotone τ
  bound : ∀ x, τ x ≤ γ
  pos : ⊥ < γ
  cap : γ < p c
  face : ∀ d, τ (s d) = min (p d) γ
  proper : ∀ d, s d ≠ ⊤
  owner_vis : SelfVis j (s c)

/-- The endpoint `h` is the least rounded saturated observation. -/
structure IsEndpoint (j : ℕ) (s : ι → ExtOrd) (τ : ExtOrd → ExtOrd) (γ h : ExtOrd) : Prop where
  least : IsLeast {x | ∃ d, τ (s d) = γ ∧ endpoint j (s d) = x} h

theorem IsEndpoint.le_of_saturated {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) {d : ι} (hd : τ (s d) = γ) : h ≤ endpoint j (s d) :=
  H.least.2 ⟨d, hd, rfl⟩

theorem IsEndpoint.exists_witness {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) : ∃ d, τ (s d) = γ ∧ endpoint j (s d) = h :=
  H.least.1

section Conclusions

variable {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}

/-- The owner is saturated. -/
theorem Saturation.owner_saturated (S : Saturation j s p c τ γ) : τ (s c) = γ := by
  rw [S.face c, min_eq_right S.cap.le]

/-- Visibility: the endpoint is `j`-visible. -/
theorem IsEndpoint.selfVis (H : IsEndpoint j s τ γ h) : SelfVis j h := by
  obtain ⟨d, -, hd⟩ := H.exists_witness
  rw [← hd]
  exact selfVis_endpoint j (s d)

/-- Properness, from properness of the observations. -/
theorem IsEndpoint.ne_top (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : h ≠ ⊤ := by
  obtain ⟨d, -, hd⟩ := H.exists_witness
  rw [← hd]
  exact endpoint_ne_top (S.proper d)

/-- Reaching: the endpoint itself is mapped to the cap. -/
theorem IsEndpoint.reach (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : τ h = γ := by
  obtain ⟨d, hd, hdh⟩ := H.exists_witness
  refine le_antisymm (S.bound h) ?_
  calc γ = τ (s d) := hd.symm
    _ ≤ τ h := S.mono (hdh ▸ le_endpoint j (s d))

/-- Positivity: a saturated observation is not bottom, so neither is the endpoint. -/
theorem IsEndpoint.bot_lt (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : ⊥ < h := by
  refine bot_lt_iff_ne_bot.mpr fun hb ↦ ?_
  have := H.reach S
  rw [hb, S.bot] at this
  exact S.pos.ne this

/-- The owner bound: the endpoint is at most the owner's (visible) source value. -/
theorem IsEndpoint.le_owner (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : h ≤ s c :=
  (H.le_of_saturated S.owner_saturated).trans_eq (endpoint_of_selfVis S.owner_vis)

/-- The single-strip conclusion: a saturated observation below the endpoint rounds to it. -/
theorem IsEndpoint.strip (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h) (hd : τ (s d) = γ) :
    endpoint j (s d) = h :=
  le_antisymm ((endpoint_mono hlt.le).trans_eq (endpoint_of_selfVis H.selfVis))
    (H.le_of_saturated hd)

/-- A saturated observation strictly below the endpoint is `j`-invisible. -/
theorem IsEndpoint.not_selfVis_of_lt (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h)
    (hd : τ (s d) = γ) : ¬ SelfVis j (s d) := fun hv ↦
  hlt.ne (((endpoint_of_selfVis hv).symm.trans (H.strip hlt hd)))

end Conclusions

/-- **The owner-local saturation endpoint lemma** (notes40 §2.1).  Over a finite family of owner
arguments the least rounded saturated observation exists; it is positive, proper, `j`-visible,
reaches the cap, is bounded by the owner's source value, and collects every saturated
observation below it into its own strip. -/
theorem exists_isEndpoint [Finite ι] {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (S : Saturation j s p c τ γ) :
    ∃ h, IsEndpoint j s τ γ h ∧ ⊥ < h ∧ h ≠ ⊤ ∧ SelfVis j h ∧ τ h = γ ∧ h ≤ s c ∧
      ∀ d, s d < h → τ (s d) = γ → endpoint j (s d) = h := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨d₀, hd₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun d ↦ τ (s d) = γ)
    (fun d ↦ endpoint j (s d)) ⟨c, by simp [S.owner_saturated]⟩
  have H : IsEndpoint j s τ γ (endpoint j (s d₀)) :=
    ⟨⟨⟨d₀, (Finset.mem_filter.mp hd₀).2, rfl⟩, by
      rintro x ⟨d, hd, rfl⟩
      exact hmin d (by simp [hd])⟩⟩
  exact ⟨_, H, H.bot_lt S, H.ne_top S, H.selfVis, H.reach S, H.le_owner S,
    fun d hlt hd ↦ H.strip hlt hd⟩

/-- The map hypotheses of `Saturation` from a normalized witness with suppressor `gTop j`
(the sufficient condition named in notes40 §2). -/
theorem Saturation.of_witness {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (hτ : Witness (gTop j) τ) (bound : ∀ x, τ x ≤ γ) (pos : ⊥ < γ) (cap : γ < p c)
    (face : ∀ d, τ (s d) = min (p d) γ) (proper : ∀ d, s d ≠ ⊤) (owner_vis : SelfVis j (s c)) :
    Saturation j s p c τ γ :=
  ⟨hτ.bot, hτ.mono, bound, pos, cap, face, proper, owner_vis⟩

end OwnerLocalEndpoint

end VaughtConjecture.Knight

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
  have hxinvis : ¬ SelfVis K x := by
    intro hv
    have he := hα.clause5 x K (by rw [gTop_of_le le_rfl]; exact le_top) K le_rfl
    rw [hv] at he
    exact hinvis he.symm
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (hxinvis (selfVis_bot K)).elim
  · exact (hxinvis (extVisibilityReplace_top K K)).elim
  have hv : finitePart v < K := by
    exact not_le.mp (fun h => hxinvis (selfVis_ofOrd_iff.mpr h))
  have orbit (n : ℕ) (hn : n ≤ K) :
      α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
    have he := hα.clause5 (ofOrd v) K
      (by rw [gTop_of_le le_rfl]; exact le_top) n hn
    rw [hx, extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hv,
      ordinalReplace, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact hi),
      ordinalReplace, limitPart_limitPart_add_nat] at he
    exact he
  have hoff : finitePart v = i := by
    have he := orbit (finitePart v) hv.le
    rw [decomposition, hx, ofOrd_inj] at he
    exact (Nat.cast_inj.mp ((add_right_inj (limitPart u)).mp he)).symm
  exact ⟨v, by rw [← hoff, decomposition], orbit⟩

/-- A visible lower bound at an invisible source already holds at its floor.
This includes a plateau whose interior output equals the agreement cap. -/
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

/-- Distinct original strips cannot both map affinely onto the same strip.
This is proved from the actual monotone witness, not a source-order record. -/
theorem strip_unique {K : ℕ} {α : ExtOrd → ExtOrd} (hα : Witness (gTop K) α)
    (hK : 0 < K) {u v w : Ordinal.{0}}
    (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
    (hw : ∀ n ≤ K, α (ofOrd (limitPart w + n)) = ofOrd (limitPart u + n)) :
    limitPart v = limitPart w := by
  have no_lt (v w : Ordinal.{0})
      (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
      (hw : ∀ n ≤ K, α (ofOrd (limitPart w + n)) = ofOrd (limitPart u + n)) :
      ¬ limitPart v < limitPart w := by
    intro hlt
    have he := hα.mono (ofOrd_le_ofOrd.mpr (limitPart_add_nat_le_of_lt hlt K))
    have hz := hw 0 (Nat.zero_le K)
    simp only [Nat.cast_zero, add_zero] at hz
    rw [hv K le_rfl, hz, ofOrd_le_ofOrd] at he
    have hh : limitPart u < limitPart u + K := by
      have hk : (0 : Ordinal.{0}) < (K : Ordinal.{0}) := Nat.cast_lt.mpr hK
      simpa only [add_zero] using add_lt_add_right hk (limitPart u)
    exact not_lt_of_ge he hh
  exact le_antisymm (not_lt.mp (no_lt w v hw hv)) (not_lt.mp (no_lt v w hv hw))

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
  · exact (not_lt_of_ge le_top hlt).elim
  · have hKn : (K : Ordinal.{0}) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
    obtain ⟨t, ht, hwt⟩ := Ordinal.lt_add_iff hKn |>.mp (ofOrd_lt_ofOrd.mp hlt)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (ht.trans (Ordinal.natCast_lt_omega0 K))
    have hnK : n < K := Nat.cast_lt.mp ht
    have he := hz.trans (hα.mono (ofOrd_le_ofOrd.mpr hwt))
    rw [hv n hnK.le, ofOrd_le_ofOrd] at he
    exact not_lt_of_ge he (add_lt_add_right ht (limitPart u))

theorem invisible_readback {K n : ℕ} {α : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) {u v : Ordinal.{0}}
    (hv : ∀ m ≤ K, α (ofOrd (limitPart v + m)) = ofOrd (limitPart u + m))
    {z : ExtOrd} (hn : n < K) (hz : α z = ofOrd (limitPart u + n)) :
    z = ofOrd (limitPart v + n) := by
  obtain ⟨w, hw, hwo⟩ := invisible_preimage hα hn hz
  have he := strip_unique hα (Nat.zero_le n |>.trans_lt hn) hv hwo
  simpa only [he] using hw

private theorem ray_cases (K : ℕ) (u v : Ordinal.{0}) (x : ExtOrd) :
    FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x = ⊥ ∨
      ofOrd (limitPart u) ≤ x ∧ ofOrd (limitPart v) ≤
        FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨w, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨le_top, ofOrd_le_ofOrd.mpr le_self_add⟩
  · rw [FiniteOrbitEmbedding.ray_ofOrd]
    by_cases hw : limitPart w < limitPart u
    · exact Or.inl (ite_eq_left hw)
    · rw [ite_eq_right hw]
      refine Or.inr ⟨ofOrd_le_ofOrd.mpr ((not_lt.mp hw).trans (limitPart_le w)), ?_⟩
      split_ifs <;> exact ofOrd_le_ofOrd.mpr le_self_add

/-- Construct the replacement strip directly from two owner witnesses and a
saturated invisible incidence. Every short source retains its ORIGINAL cap,
including unused strip points and all supported controller coordinates. -/
theorem exists_retuning {K i : ℕ} {α β τ : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) (hβ : Witness (gTop K) β) (hτ : Witness (gTop K) τ)
    {x γ M : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i))
    (hγ : SelfVis K γ) (hτbound : ∀ z, τ z ≤ γ) (hsat : τ (α x) = γ)
    (hp : γ ≤ β x) (hβbound : ∀ z, β z ≤ M) :
    ∃ (v : Ordinal.{0}) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      x = ofOrd (limitPart v + i) ∧ Witness (gTop K) ρ ∧
      γ ≤ δ ∧ δ ≤ M ∧ SelfVis K δ ∧
      ρ (ofOrd (limitPart u + K)) = δ ∧
      ρ (α x) = β x ∧
      (∀ n ≤ K, ρ (ofOrd (limitPart u + n)) = β (ofOrd (limitPart v + n))) ∧
      (∀ z, Short K z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ M := by
  obtain ⟨v, hv, _⟩ := invisible_preimage hα hi hx
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
    rw [hvv] at he
    exact he.symm
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
    rcases ray_cases K u v z with he | ⟨hzu, hzv⟩
    · change η z = ⊥ at he
      rw [he, hβ.bot, max_bot_right]
    · have htz : τ z = γ := le_antisymm (hτbound _) (htf ▸ hτ.mono hzu)
      have hbz : γ ≤ β (η z) := hbf.trans (hβ.mono hzv)
      rw [htz, max_eq_right hbz, min_eq_right hbz, min_self]
  refine ⟨v, ρ, δ, hv, hτ.max hκ, hδ, hβbound _, hδvis, hstrip K le_rfl,
    ?_, hstrip, hcap, ?_⟩
  · rw [hx, hstrip i hi.le, ← hv]
  · intro z
    apply max_le ((hτbound z).trans (hδ.trans (hβbound _)))
    -- The repaired composite has its bounded range even off the short grid.
    exact hβbound _

/-- The same constructed retuning reads EVERY occurrence from the saturated
strip, not just the occurrence used to choose it. Values beyond the endpoint
have the required prescribed-witness lower bound, derived from source order. -/
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
  obtain ⟨v, ρ, δ, hv, hρ, hγδ, hδM, hδvis, hend, _, hstrip, hcap, hbound⟩ :=
    exists_retuning hα hβ hτ hi hx hγ hτbound hsat hp hβbound
  obtain ⟨w, hw, hwo⟩ := invisible_preimage hα hi hx
  have he : limitPart w = limitPart v := by
    have heq := congrArg limitPart (ofOrd_inj.mp (hw.symm.trans hv))
    simpa only [limitPart_limitPart_add_nat] using heq
  have horbit (n : ℕ) (hn : n ≤ K) :
      α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
    simpa only [he] using hwo n hn
  refine ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, ?_, ?_, hcap, hbound⟩
  · intro z n hn hz
    have hread := invisible_readback hα horbit hn hz
    exact (congrArg ρ hz).trans ((hstrip n hn.le).trans (congrArg β hread).symm)
  · intro z hz
    have hlow := endpoint_reflects hα (Nat.zero_le i |>.trans_lt hi) horbit hz
    exact (hend.symm.trans (hstrip K le_rfl)).le.trans (hβ.mono hlow)

end VaughtConjecture.Knight.OwnerStripRetuning

namespace VaughtConjecture.Knight.OwnerLocalAlignment
open Transform Value ExtOrd SharpWitnessComposition OwnerStripRetuning OwnerLocalEndpoint
noncomputable section

theorem saturated_subcut {X : Type*} {j : ℕ} {s p : X → ExtOrd} {c : X}
    {τ : ExtOrd → ExtOrd} {γ h : ExtOrd} (sat : Saturation j s p c τ γ)
    (H : IsEndpoint j s τ γ h) (d : X) (hd : s d < h) (hsat : τ (s d) = γ) :
    ∃ (u : Ordinal.{0}) (n : ℕ), n < j ∧
      s d = ofOrd (limitPart u + n) ∧ h = ofOrd (limitPart u + j) := by
  have hnv := H.not_selfVis_of_lt hd hsat
  rcases ExtOrd.cases (s d) with hb | ht | ⟨u, hu⟩
  · exact (hnv (hb ▸ selfVis_bot j)).elim
  · exact (sat.proper d ht).elim
  · have hn : finitePart u < j := by
      by_contra hn
      exact hnv (hu ▸ selfVis_ofOrd_iff.mpr (not_lt.mp hn))
    refine ⟨u, finitePart u, hn, ?_, ?_⟩
    · simpa only [limitPart_add_finitePart] using hu
    · have he := H.strip hd hsat
      rw [endpoint, hu, extVisibilityReplace_of_finitePart_lt hn] at he
      exact he.symm

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D}

/-- Internal alignment at the constructed owner-local endpoint. -/
theorem alignment_at_endpoint (c : Cell D)
    {s p : D.below (D.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hshort : ∀ e, Short (D.grade c) (s e))
    {τ : ExtOrd → ExtOrd} {h γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ)
    (sat : Saturation (D.grade c) s p ⟨c, GradedLe.refl _⟩ τ γ)
    (H : IsEndpoint (D.grade c) s τ γ h) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧
      (∀ e, δ < min (p e) (p ⟨c, GradedLe.refl _⟩) → h ≤ s e) ∧
      (∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ p ⟨c, GradedLe.refl _⟩ := by
  have hτbound := sat.bound
  have hpc := sat.cap
  have hface := sat.face
  have hreach := H.reach sat
  classical
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let M := p self
  by_cases halign : ∀ e : D.below (D.cell c), γ < min (p e) M → h ≤ s e
  · refine ⟨τ, γ, hτ, le_rfl, hpc.le, hγ, hreach, ?_, halign,
      fun _ _ => rfl, fun z => (hτbound z).trans hpc.le⟩
    intro e
    rw [min_eq_left (hτbound _), hface]
  push Not at halign
  obtain ⟨d, hpd, hsub⟩ := halign
  have hsd : s d < h := hsub
  have hsat : γ ≤ τ (s d) := by
    rw [hface d, min_eq_right (lt_of_lt_of_le hpd (min_le_left _ _)).le]
  obtain ⟨u, i, hi, hdi, hendpoint⟩ := saturated_subcut sat H d hsd (le_antisymm (hτbound _) hsat)
  have howner : h ≤ s self := H.le_owner sat
  obtain ⟨α, hα, _, hαread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := s) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hs.orderly self).symm (hs.locality self)
  obtain ⟨β, hβ, hβbound, hβread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := p) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hp.orderly self).symm (hp.locality self)
  have ha (e : D.below (D.cell c)) (he : s e < h) : α (sem.E c e) = s e :=
    (hαread e).trans (min_eq_left (he.le.trans howner))
  obtain ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, hstrip, habove, hcap, hbound⟩ :=
    exists_retuning_with_transfer hα hβ hτ hi ((ha d hsd).trans hdi) hγ hτbound
      (by rw [ha d hsd]; exact le_antisymm (hτbound _) hsat)
      (by rw [hβread d]; exact hpd.le) hβbound
  have hρh : ρ h = δ := hendpoint ▸ hend
  have subread (e : D.below (D.cell c)) (he : s e < h) :
      min (p e) M = ρ (s e) := by
    by_cases hlo : τ (s e) < γ
    · have hpread : p e = τ (s e) := AmbientGradeCharts.eq_of_cap_below
        (by rw [min_eq_left (hτbound _)]; exact (hface e).symm) hlo
      have hρread : ρ (s e) = τ (s e) :=
        AmbientGradeCharts.eq_of_cap_below (hcap _ (hshort e)) hlo
      rw [hpread, hρread, min_eq_left (hlo.le.trans hpc.le)]
    · obtain ⟨w, n, hn, heq, hwe⟩ :=
        saturated_subcut sat H e he (le_antisymm (hτbound _) (not_lt.mp hlo))
      have hfloor : limitPart w = limitPart u := by
        have heq := congrArg limitPart (ofOrd_inj.mp (hwe.symm.trans hendpoint))
        simpa only [limitPart_limitPart_add_nat] using heq
      rw [hfloor] at heq
      exact (hβread e).symm.trans
        ((hstrip (sem.E c e) n hn ((ha e he).trans heq)).symm.trans
          (congrArg ρ (ha e he)))
  refine ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hρh, ?_, ?_, hcap, hbound⟩
  · intro e
    by_cases he : s e < h
    · have hc : min (min (p e) M) δ = min (p e) δ := by
        rw [min_assoc, min_eq_right hδM]
      rw [← hc, subread e he]
    · have has : ofOrd (limitPart u + D.grade c) ≤ α (sem.E c e) := by
        rw [hαread e, ← hendpoint]
        exact le_min (not_lt.mp he) howner
      have hpe : δ ≤ p e := (habove _ has).trans
        ((hβread e).le.trans (min_le_left _ _))
      rw [min_eq_right hpe, min_eq_right (hρh ▸ hρ.mono (not_lt.mp he))]
  · intro e hhigh
    by_contra hn
    have he := not_le.mp hn
    have hle : min (p e) M ≤ δ := by
      rw [subread e he, ← hρh]
      exact hρ.mono he.le
    exact not_lt_of_ge hle hhigh

/-- The endpoint and retuning are constructed from lawful owner data. No source
grid, first-reaching-grid assertion, or alignment conclusion is an input. -/
theorem exists_alignment (c : Cell D)
    {s p : D.below (D.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hproper : ∀ e, s e ≠ ⊤) (hshort : ∀ e, Short (D.grade c) (s e))
    {τ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hpos : ⊥ < γ) (hτbound : ∀ z, τ z ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (h : ExtOrd) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      IsEndpoint (D.grade c) s τ γ h ∧
      ⊥ < h ∧ h ≠ ⊤ ∧ SelfVis (D.grade c) h ∧ h ≤ s ⟨c, GradedLe.refl _⟩ ∧
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧
      (∀ e, δ < min (p e) (p ⟨c, GradedLe.refl _⟩) → h ≤ s e) ∧
      (∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ p ⟨c, GradedLe.refl _⟩ := by
  let sat : Saturation (D.grade c) s p ⟨c, GradedLe.refl _⟩ τ γ :=
    Saturation.of_witness hτ hτbound hpos hpc hface hproper
      (hs.orderly ⟨c, GradedLe.refl _⟩).symm
  obtain ⟨h, H, hhpos, hhtop, hvis, _, howner, _⟩ := exists_isEndpoint sat
  exact ⟨h, by
    obtain ⟨ρ, δ, hrest⟩ := alignment_at_endpoint c hs hp hshort hτ hγ sat H
    exact ⟨ρ, δ, H, hhpos, hhtop, hvis, howner, hrest⟩⟩

/-- A finite tail budget follows from an explicit complete-inventory bound.
The number `m` is not tied to the cardinality of the prescribed owner face. -/
theorem tail_room {j m : ℕ} {x : ExtOrd}
    (hx : x ≤ ofOrd (Ordinal.omega0 * (2 * m : ℕ) + j)) :
    x < ofOrd (Ordinal.omega0 * (2 * m + 1 : ℕ)) :=
  hx.trans_lt (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (by omega)) j))

/-- Construct the lawful encoded owner face and exact owner-capped readback.
The complete source inventory controls the tail budget; the local endpoint is
produced from the actual owner observations, not a separately assumed grid. -/
theorem exists_coded_face (c : Cell D) [Fintype (D.below (D.cell c))]
    {s p : D.below (D.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hproper : ∀ e, s e ≠ ⊤) (hshort : ∀ e, Short (D.grade c) (s e))
    (m : ℕ)
    (hbudget : s ⟨c, GradedLe.refl _⟩ ≤ ofOrd (Ordinal.omega0 * (2 * m : ℕ) + D.grade c))
    {τ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hpos : ⊥ < γ) (hτbound : ∀ z, τ z ≤ γ)
    (hface : ∀ e, τ (s e) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (h : ExtOrd) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd)
        (f : D.below (D.cell c) → ExtOrd),
      IsEndpoint (D.grade c) s τ γ h ∧
      ⊥ < h ∧ SelfVis (D.grade c) h ∧ h ≤ s ⟨c, GradedLe.refl _⟩ ∧
      h < ofOrd (Ordinal.omega0 * (2 * m + 1 : ℕ)) ∧
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      RespectsSemanticsBelow sem (D.cell c) f ∧
      (∀ e, min (f e) h = min (s e) h) ∧
      f = AlignedCutEncoding.encode s (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩))
        (D.grade c) (2 * m + 1) h δ ∧
      (∀ e, PaddedSourceDecoder.extend
        (RelativePrefixEncoding.inventory (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)) δ)
        (D.grade c) (2 * m + 1) ρ δ (f e) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      (∀ e, min (p e) δ = min (ρ (s e)) δ) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨h, ρ, δ, H, hhpos, _, hvis, howner, hρ, hγδ, hδM, hδvis, hρh,
      hread, halign, hcap, _⟩ :=
    exists_alignment c hs hp hproper hshort hτ hγ hpos hτbound hface hpc
  let p₀ := fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)
  let f := AlignedCutEncoding.encode s p₀ (D.grade c) (2 * m + 1) h δ
  have hroom := tail_room (howner.trans hbudget)
  have hp₀ : RespectsSemanticsBelow sem (D.cell c) p₀ :=
    hp.cap (hp.orderly ⟨c, GradedLe.refl _⟩).symm
  refine ⟨h, ρ, δ, f, H, hhpos, hvis, howner, hroom,
    hρ, hγδ, hδM, hδvis, hρh, ?_, ?_, rfl, ?_, hread, hcap⟩
  · exact AlignedCutEncoding.encode_respects hs hp₀ (fun e => e.2.2)
      hvis hhpos.ne' hδvis hroom halign
  · exact AlignedCutEncoding.encode_cap s p₀ hroom halign
  · intro e
    apply AlignedCutEncoding.decode_encode s p₀ hρ.mono hroom hρh.ge
    intro d
    change min (ρ (s d)) δ = min (min (p d) (p ⟨c, GradedLe.refl _⟩)) δ
    rw [min_assoc, min_eq_right hδM]
    exact (hread d).symm

end
end VaughtConjecture.Knight.OwnerLocalAlignment
