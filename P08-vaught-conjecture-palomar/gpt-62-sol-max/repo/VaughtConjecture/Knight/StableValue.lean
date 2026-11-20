/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalLift
public import VaughtConjecture.Knight.TopGradeStableCore
public import VaughtConjecture.Knight.BlockReflection

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType

universe w

/-- The provisional value of an `∞`-cell is `α + j` for a natural `j`. -/
theorem someProvisionalValue_top_form {β : Ordinal.{0}} {n : ℕ} {p : S β n}
    {Xi : Cell p.scheme.scheme} (htop : p.label Xi = ⊤) :
    ∃ j : ℕ, p.someProvisionalValue Xi = ofOrd (β + j) := by
  by_cases hcap : p.ProvisionalCap Xi
  · exact ⟨p.topGrade, someProvisionalValue_of_cap htop hcap⟩
  · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
    exact ⟨i, hval⟩

/-- Respect is closed under the jump map below the visible threshold. -/
theorem RespectsSemantics.jump {n : ℕ} {D : SemScheme n} {v : Cell D.scheme → ExtOrd}
    (h : RespectsSemantics D.rows v) {β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (K : ℕ)
    (hgr : ∀ d : Cell D.scheme, D.scheme.grade d ≤ K) :
    RespectsSemantics D.rows (fun d => ExtOrd.jump (ofOrd (β + K)) (v d)) where
  orderly d := by
    simp only [ExtOrd.jump]
    split_ifs
    · exact h.orderly d
    · exact (extVisibilityReplace_top _ _).symm
  locality c := by
    have hvis : SelfVis K (ofOrd (β + K)) := selfVis_ofOrd_iff.mpr (by
      rw [← limitPart_of_succLimit hβ, finitePart_limitPart_add_nat])
    simpa only [Function.comp_apply, jump_min] using
      TransformsTo.jump_target (h.locality c) hvis (fun d => hgr d.1)
  availability c d hs hg := by
    obtain ⟨e, he, hle⟩ := h.availability c d hs hg
    exact ⟨e, he, jump_mono _ hle⟩

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- **The stable value `M⁺(Ξ)` as a function** (Def. 5.3.9, functional under clauses (2) and
(3)): a classical choice from the total graph `HasStableValue`. -/
noncomputable def stableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) : ExtOrd :=
  Classical.choose (exists_hasStableValue (R := R) t p Xi)

/-- The specification of `stableValue`. -/
theorem hasStableValue_stableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) :
    R.HasStableValue t p Xi (R.stableValue t p Xi) :=
  Classical.choose_spec (exists_hasStableValue (R := R) t p Xi)

/-- Any value of the graph is the stable value. -/
theorem stableValue_eq (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p)
    {Xi : Cell p.scheme.scheme} {γ : ExtOrd} (h : R.HasStableValue t p Xi γ) :
    R.stableValue t p Xi = γ :=
  HasStableValue.unique hcons hcov hpt (R.hasStableValue_stableValue t p Xi) h

/-- A stabilizing value is the stable value. -/
theorem stableValue_of_stabilizesTo (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ : ExtOrd}
    (hγ : γ < ofOrd (α.1 + Ordinal.omega0)) (h : R.StabilizesTo t p Xi γ) :
    R.stableValue t p Xi = γ :=
  stableValue_eq hcons hcov hpt (Or.inl ⟨hγ, h⟩)

/-- The stable value of a non-`∞` cell is its source label. -/
theorem stableValue_of_ne_top (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (hne : p.label Xi ≠ ⊤) :
    R.stableValue t p Xi = p.label Xi := by
  have hlt : p.label Xi < ofOrd (α.1 + Ordinal.omega0) := by
    rcases p.label_bound Xi with h | h
    · exact h.trans (ofOrd_lt_ofOrd.mpr (lt_add_of_pos_right _ Ordinal.omega0_pos))
    · exact absurd h hne
  exact stableValue_of_stabilizesTo hcons hcov hpt hlt
    (stabilizesTo_label_of_ne_top ⟨n, t, p, hpt⟩ hne hcons hcov)

/-- The stable value of an `∞` cell is at least `α`. -/
theorem le_stableValue_of_top {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (_hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (htop : p.label Xi = ⊤) :
    ofOrd α.1 ≤ R.stableValue t p Xi := by
  rcases R.hasStableValue_stableValue t p Xi with ⟨-, hs⟩ | ⟨heq, -⟩
  · obtain ⟨m', u, g, f, q, hpq, hq, hgu, hfu, hval⟩ := hs t
    have hlab : q.label (mapCell hpq Xi) = ⊤ := by rw [label_mapCell hpq Xi]; exact htop
    calc ofOrd α.1 ≤ q.someProvisionalValue (mapCell hpq Xi) :=
          le_someProvisionalValue_of_top hlab
      _ = R.stableValue t p Xi := (isProvisionalValue_iff.mp hval).symm
  simp_all

/-- **Face naturality of stabilization from exact consistency alone**: along an actual face,
a cell stabilizes iff its underlying ambient cell does.  Each witness over the face, requested
at a tuple joining `u` to the requested tuple, already is an actual common extension; exact
consistency and injectivity identify its embeddings.  The face's own evaluation is not an
input. -/
theorem stabilizesTo_mapCell_iff' (hcons : R.IsExactParentConsistent) {n m : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m} (hqu : R.eval u = some q)
    {f : Fin n ↪ Fin m} (hfu : f.trans u = t) (hpq : typeMap f q = some p)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo u q (mapCell hpq Xi) γ ↔ R.StabilizesTo t p Xi γ := by
  constructor
  · -- compose each witness's root embedding with the face
    intro hs k s
    obtain ⟨l, z, g, e, r, hqr, hz, hgz, hez, hv⟩ := hs s
    have hpr : typeMap (f.trans e) r = some p := by
      rw [← typeMap_trans f e r q hqr]; exact hpq
    refine ⟨l, z, g, f.trans e, r, hpr, hz, hgz, ?_, ?_⟩
    · aesop
    · rw [mapCell_trans hqr hpq hpr Xi]; exact hv
  · -- join `u` and `s` into one tuple; stabilization over `t` supplies its actual extension
    intro hs k s
    obtain ⟨l, w, a, hwu, hws⟩ := exists_common_tuple u s
    obtain ⟨j, z, g, e, r, hpr, hz, hgz, hez, hv⟩ := hs w
    set b : Fin m ↪ Fin j := (Fin.castAddEmb l).trans g with hb
    have hbz : b.trans z = u := by
      aesop
    have hqr : typeMap b r = some q := by
      have h := hcons z r b hz
      simp_all
    have he : e = f.trans b := by
      apply Function.Embedding.ext
      intro i
      apply z.injective
      have hfb : (f.trans b).trans z = t := by
        rw [Function.Embedding.trans_assoc, hbz, hfu]
      exact (DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfb i).symm
    subst he
    refine ⟨j, z, a.trans g, b, r, hqr, hz, ?_, hbz, ?_⟩
    · rw [Function.Embedding.trans_assoc, hgz, hws]
    · rw [mapCell_trans hqr hpq hpr Xi] at hv; exact hv

/-- **Face naturality of the stable-value graph from exact consistency alone**: along an actual
face, a cell has stable value `γ` iff its underlying ambient cell does. -/
theorem hasStableValue_mapCell_iff' (hcons : R.IsExactParentConsistent) {n m : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m} (hqu : R.eval u = some q)
    {f : Fin n ↪ Fin m} (hfu : f.trans u = t) (hpq : typeMap f q = some p)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) :
    R.HasStableValue u q (mapCell hpq Xi) γ ↔ R.HasStableValue t p Xi γ := by
  have h := fun δ => stabilizesTo_mapCell_iff' hcons hqu hfu hpq Xi δ
  refine or_congr (and_congr_right fun _ => h γ) (and_congr_right fun _ => ?_)
  simp_all

/-- **Face naturality of the stable value from exact consistency alone** (the paper's
`s_y = p*` coherence): along an actual face, corresponding cells have equal stable values. -/
theorem stableValue_mapCell' (hcons : R.IsExactParentConsistent) {n m : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m} (hqu : R.eval u = some q)
    {f : Fin n ↪ Fin m} (hfu : f.trans u = t) (hpq : typeMap f q = some p)
    (Xi : Cell p.scheme.scheme) :
    R.stableValue u q (mapCell hpq Xi) = R.stableValue t p Xi :=
  HasStableValue.unique_of_consistent hcons (R.hasStableValue_stableValue u q _)
    ((hasStableValue_mapCell_iff' hcons hqu hfu hpq Xi _).mpr
      (R.hasStableValue_stableValue t p Xi))

set_option linter.unusedVariables false in
/-- **Face naturality of the stable value** (the paper's `s_y = p*` coherence), in its original
interface.  The covering and face-evaluation hypotheses are no longer used; see
`stableValue_mapCell'`. -/
theorem stableValue_mapCell (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n m : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M}
    {q : S α.1 m} (hpt : R.eval t = some p) (hqu : R.eval u = some q) {f : Fin n ↪ Fin m}
    (hfu : f.trans u = t) (hpq : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    R.stableValue u q (mapCell hpq Xi) = R.stableValue t p Xi :=
  stableValue_mapCell' hcons hqu hfu hpq Xi

end KnightRealization

end VaughtConjecture.Knight
