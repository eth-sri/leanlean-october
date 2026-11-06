module

public import Chazelle.Core.SweepEvTasks3
public import Chazelle.Core.SweepEvCand3
public import Chazelle.Core.GranSize
public import Chazelle.Core.FactsArcs

/-!
# The sweep (WP-D), stage 3: the number of keys (Task C, mathematics)

The offsets of the cut keys of `F₂⁺` and of the possible window ends are at most
`4 K₂ + 2 K₁ + 9`:

* `attach_keys`: an admissible chord is attached at at most two keys (its two ends,
  `WalkAx.attach_endpoint`, each attached once, `WalkAx.attach_unique`), so a finite admissible
  family has at most `2 |F|` cut keys (`cut_keys_ncard`);
* `F₂plus_ncard_le`: `|F₂⁺| ≤ 2 K₂ + 4` (`ncard_fusion_le`, two top chords);
* `win_uniq`: a cut key of `N₁` gives at most one window offset `Lst + ψ d + t` with `MValid d t`
  and `0 ≤ t ≤ 1` (the two readings `(d, 1)`, `(d + 1, 0)` of a vertex key give the same offset;
  the wrap `d + 1 ≡ 0` is excluded since the point at `b₁` is the shared vertex);
* **`countTask : CountTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed Sweep

@[expose] public section

/-! ## Counting through a relation with unique preimages -/

/-- If every element of `A` is related to some element of a finite set `B` and every element of
`B` is related to at most one element of `A`, then `A` is finite with `|A| ≤ |B|`. -/
theorem finite_ncard_le_of_rel {α β : Type*} {A : Set α} {B : Set β} (hB : B.Finite)
    (R : α → β → Prop) (hcov : ∀ a ∈ A, ∃ b ∈ B, R a b)
    (huniq : ∀ a a' b, R a b → R a' b → a = a') : A.Finite ∧ A.ncard ≤ B.ncard := by
  classical
  rcases A.eq_empty_or_nonempty with hA | ⟨a₀, ha₀⟩
  · rw [hA]; exact ⟨finite_empty, by simp⟩
  obtain ⟨b₀, -, -⟩ := hcov a₀ ha₀
  have : Nonempty β := ⟨b₀⟩
  choose! f hfB hfR using hcov
  have hinj : InjOn f A := fun a ha a' ha' h =>
    huniq a a' (f a) (hfR a ha) (by rw [h]; exact hfR a' ha')
  refine ⟨Finite.of_finite_image (hB.subset ?_) hinj, ncard_le_ncard_of_injOn f hfB hinj hB⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hfB a ha

/-! ## Cut keys -/

/-- **An admissible chord is attached at at most two keys.** -/
theorem attach_keys {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ x y : ℝ, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t → (p : ℝ) + t = x ∨ (p : ℝ) + t = y := by
  obtain ⟨a, b, -, rfl, -, hopen, ⟨⟨pa, ta, hAa, hpa⟩, -⟩, ⟨⟨pb, tb, hAb, hpb⟩, -⟩⟩ :=
    hM.ends _ hc
  refine ⟨pa + ta, pb + tb, fun p t hA => ?_⟩
  rcases hM.attach_endpoint hopen hA with h | h
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hAa (h.trans hpa.symm)
    exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hAb (h.trans hpb.symm)
    exact Or.inr rfl

/-- **The cut keys of a finite admissible family** are finitely many, at most twice its size. -/
theorem cut_keys_ncard {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) :
    {x : ℝ | M.IsCut F x}.Finite ∧ {x : ℝ | M.IsCut F x}.ncard ≤ 2 * F.ncard := by
  classical
  choose! fx fy hxy using fun c (hc : c ∈ F) => attach_keys hM (hF hc)
  have hsub : {x : ℝ | M.IsCut F x} ⊆ fx '' F ∪ fy '' F := by
    rintro x ⟨c, hc, p, t, hA, rfl⟩
    rcases hxy c hc p t hA with h | h
    · exact Or.inl ⟨c, hc, h.symm⟩
    · exact Or.inr ⟨c, hc, h.symm⟩
  have hfu : (fx '' F ∪ fy '' F).Finite := (hfin.image _).union (hfin.image _)
  refine ⟨hfu.subset hsub, ?_⟩
  calc {x : ℝ | M.IsCut F x}.ncard ≤ (fx '' F ∪ fy '' F).ncard := ncard_le_ncard hsub hfu
    _ ≤ (fx '' F).ncard + (fy '' F).ncard := ncard_union_le _ _
    _ ≤ F.ncard + F.ncard := Nat.add_le_add (ncard_image_le hfin) (ncard_image_le hfin)
    _ = 2 * F.ncard := by ring

/-! ## The size of `F₂⁺` -/

/-- There are at most two top chords at the top of `C₂`. -/
theorem topChords₂_ncard_le (J : Merge.Junction) : (topChords₂ J).ncard ≤ 2 := by
  have hsub : topChords₂ J ⊆
      (fun σ => J.whole.chordSet (J.m₁ + J.right.topIdx) σ) '' ({1, -1} : Set ℝ) := by
    rintro d ⟨σ, hσ, -, rfl⟩
    exact ⟨σ, by rcases hσ with rfl | rfl <;> simp, rfl⟩
  calc (topChords₂ J).ncard
      ≤ ((fun σ => J.whole.chordSet (J.m₁ + J.right.topIdx) σ) '' ({1, -1} : Set ℝ)).ncard :=
        ncard_le_ncard hsub ((toFinite _).image _)
    _ ≤ ({1, -1} : Set ℝ).ncard := ncard_image_le (toFinite _)
    _ = 2 := ncard_pair (by norm_num)

/-- **`|F₂⁺| ≤ 2 |S₂| + 4`.** -/
theorem F₂plus_ncard_le (J : Merge.Junction) {S₂ : Set (Set Point)} (hS₂f : S₂.Finite) :
    (F₂plus J S₂).ncard ≤ 2 * S₂.ncard + 4 := by
  have h1 := J.ncard_fusion_le finite_empty hS₂f
  rw [ncard_empty, zero_add] at h1
  have h2 := topChords₂_ncard_le J
  calc (F₂plus J S₂).ncard ≤ (J.fusion ∅ S₂).ncard + (topChords₂ J).ncard := ncard_union_le _ _
    _ ≤ 2 * S₂.ncard + 4 := by omega

/-- **The offsets of the cut keys of `F₂⁺`**: finitely many, at most `4 |S₂| + 8`. -/
theorem cutOffs_ncard (J : Merge.Junction) (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    (cutOffs J S₂).Finite ∧ (cutOffs J S₂).ncard ≤ 4 * S₂.ncard + 8 := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  obtain ⟨hfin, hle⟩ := cut_keys_ncard hM (F₂plus_subset J hS₂) (F₂plus_finite J hS₂f)
  have hsub : cutOffs J S₂ ⊆ oW J '' {x : ℝ | (chainModel J.whole).IsCut (F₂plus J S₂) x} := by
    rintro o ⟨x, hx, -, -, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨(hfin.image _).subset hsub, ?_⟩
  have := F₂plus_ncard_le J hS₂f
  calc (cutOffs J S₂).ncard
      ≤ (oW J '' {x : ℝ | (chainModel J.whole).IsCut (F₂plus J S₂) x}).ncard :=
        ncard_le_ncard hsub (hfin.image _)
    _ ≤ {x : ℝ | (chainModel J.whole).IsCut (F₂plus J S₂) x}.ncard := ncard_image_le hfin
    _ ≤ 4 * S₂.ncard + 8 := by omega

/-! ## The window offsets -/

/-- The point of the walk of `C₁` at `b₁` is the shared vertex. -/
theorem b₁_pt (J : Merge.Junction) :
    sidePt (chainModel J.left).W ((b₁ J + 0) % (chainModel J.left).W.n) 0 = J.shared := by
  rw [add_zero, Nat.mod_eq_of_lt (b₁_lt (J := J))]
  unfold b₁
  split_ifs with h
  · rw [(sidePt_top_copies J.left).2]
    exact left_top_eq J (caseB_facts J h).1
  · rw [Chazelle.Chain.sidePt_zero, vtx_tpos' J.left (k := J.m₁) (le_refl _)]
    rfl

/-- The predecessor of a nonzero residue. -/
theorem pred_mod' {b d n e : ℕ} (hb : b < n) (hd : d < n) (h1 : 1 ≤ d)
    (he : (b + d) % n = e) (he0 : e ≠ 0) : (b + (d - 1)) % n + 1 = e := by
  by_cases h : b + d < n
  · rw [Nat.mod_eq_of_lt h] at he
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at he
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The two readings `(d, 1)` and `(d + 1, 0)` of a vertex key give the same offset. -/
theorem win_uniq_step (J : Merge.Junction) (hP : J.P.Simple) {d d' : ℕ}
    (hv : MValid J d 1) (hv' : MValid J d' 0)
    (hk : (b₁ J + d') % (chainModel J.left).W.n = (b₁ J + d) % (chainModel J.left).W.n + 1) :
    ψ J d + 1 = ψ J d' := by
  have hb := b₁_lt (J := J)
  have hE := E₁_le (J := J) hP
  have hd : d < (chainModel J.left).W.n := lt_of_lt_of_le hv.1 hE
  have hd' : d' < (chainModel J.left).W.n := lt_of_lt_of_le hv'.1 hE
  have hd'1 : 1 ≤ d' := by
    rcases Nat.eq_zero_or_pos d' with h0 | h0
    · subst h0; exact absurd (b₁_pt J) (hv'.2.2.2 rfl)
    · exact h0
  have hpm := pred_mod' hb hd' hd'1 hk (by omega)
  have hdd : d = d' - 1 := add_mod_inj (g := b₁ J) hd (by omega) (by omega)
  subst hdd
  obtain ⟨-, hg, hl, -⟩ := hv
  obtain ⟨-, hg', -, -⟩ := hv'
  have hl' : ¬ (0 < lδ J ∧ d' - 1 = lL1 J) := fun h => hl ⟨h.1, h.2, one_ne_zero⟩
  unfold ψ
  split_ifs <;> omega

/-- **A cut key of `N₁` gives at most one window offset.** -/
theorem win_uniq (J : Merge.Junction) (hP : J.P.Simple) {d d' : ℕ} {t t' : ℝ}
    (hv : MValid J d t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv' : MValid J d' t') (ht0' : 0 ≤ t')
    (ht1' : t' ≤ 1)
    (hx : (((b₁ J + d) % (chainModel J.left).W.n : ℕ) : ℝ) + t =
      (((b₁ J + d') % (chainModel J.left).W.n : ℕ) : ℝ) + t') :
    (ψ J d : ℝ) + t = ψ J d' + t' := by
  set n₁ := (chainModel J.left).W.n
  have hE := E₁_le (J := J) hP
  have hd : d < n₁ := lt_of_lt_of_le hv.1 hE
  have hd' : d' < n₁ := lt_of_lt_of_le hv'.1 hE
  set k := (b₁ J + d) % n₁
  set k' := (b₁ J + d') % n₁
  have hlo : (k : ℝ) < k' + 2 := by linarith
  have hhi : (k' : ℝ) < k + 2 := by linarith
  have hlo' : k < k' + 2 := by exact_mod_cast hlo
  have hhi' : k' < k + 2 := by exact_mod_cast hhi
  rcases (show k = k' ∨ k' = k + 1 ∨ k = k' + 1 by omega) with h | h | h
  · have htt : t = t' := by rw [h] at hx; linarith
    have hdd : d = d' := add_mod_inj hd hd' h
    rw [htt, hdd]
  · have e : (k' : ℝ) = k + 1 := by exact_mod_cast h
    have ht : t = 1 := by linarith
    have ht' : t' = 0 := by linarith
    subst ht ht'
    have := win_uniq_step J hP hv hv' h
    have e2 : ((ψ J d + 1 : ℕ) : ℝ) = ψ J d' := by rw [this]
    push_cast at e2
    linarith
  · have e : (k : ℝ) = k' + 1 := by exact_mod_cast h
    have ht' : t' = 1 := by linarith
    have ht : t = 0 := by linarith
    subst ht ht'
    have := win_uniq_step J hP hv' hv h
    have e2 : ((ψ J d' + 1 : ℕ) : ℝ) = ψ J d := by rw [this]
    push_cast at e2
    linarith

/-- **The window offsets**: finitely many, at most `2 K₁ + 1`. -/
theorem winOffs_ncard (P : Polygon) (J : Merge.Junction) (hP : J.P.Simple) (N₁ : NF)
    (hN₁ : IsNF (chainModel J.left) (Qof P) N₁) :
    (winOffs P J N₁).Finite ∧ (winOffs P J N₁).ncard ≤ 2 * N₁.nChords + 1 := by
  have hP₁ : J.left.P.Simple := hP
  have hM : WalkAx (chainModel J.left) := FactsChain.walkAx J.left hP₁
  obtain ⟨hfin, hle⟩ := cut_keys_ncard hM hN₁.1.2.1 hN₁.1.1
  rw [Gran.ncard_F hN₁] at hle
  obtain ⟨hf2, hl2⟩ := finite_ncard_le_of_rel hfin
    (A := {o | ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        (((b₁ J + d) % (chainModel J.left).W.n : ℕ) + t) ∧ o = (Lst J : ℝ) + ψ J d + t})
    (fun o x => ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      x = (((b₁ J + d) % (chainModel J.left).W.n : ℕ) : ℝ) + t ∧ o = (Lst J : ℝ) + ψ J d + t)
    (by
      rintro o ⟨d, t, hv, h0, h1, hc, rfl⟩
      exact ⟨_, hc, d, t, hv, h0, h1, rfl, rfl⟩)
    (by
      rintro o o' x ⟨d, t, hv, h0, h1, rfl, rfl⟩ ⟨d', t', hv', h0', h1', hx, rfl⟩
      have := win_uniq J hP hv h0 h1 hv' h0' h1' hx
      linarith)
  refine ⟨(finite_singleton _).union hf2, ?_⟩
  calc (winOffs P J N₁).ncard ≤ ({(Lst J : ℝ) + lL1 J} : Set ℝ).ncard + _ := ncard_union_le _ _
    _ ≤ 2 * N₁.nChords + 1 := by rw [ncard_singleton]; omega

/-- **Task C (mathematics): the number of keys.** -/
theorem countTask : CountTask := by
  intro P J N₁ N₂ hP hN₁ hN₂
  obtain ⟨hc, hcl⟩ := cutOffs_ncard J hP hN₂.1.2.1 hN₂.1.1
  rw [Gran.ncard_F hN₂] at hcl
  obtain ⟨hw, hwl⟩ := winOffs_ncard P J hP N₁ hN₁
  refine ⟨hc.union hw, ?_⟩
  have := ncard_union_le (cutOffs J (N₂.F (chainModel J.right) (Qof P))) (winOffs P J N₁)
  omega

end

end SweepEv

end Chazelle.Core
