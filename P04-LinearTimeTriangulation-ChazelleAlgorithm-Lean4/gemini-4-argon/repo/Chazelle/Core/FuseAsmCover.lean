module

public import Chazelle.Core.FuseAsmPtQ
public import Chazelle.Core.FuseAsmFin
public import Chazelle.Core.FuseAsmList

/-!
# WP-F fusion assembly, part 15: the query lists of the two sweeps

The query list of side `0` is `endQL N₁.chords ++ P₀` and that of side `1` is
`endQL N₂.chords ++ P₁`, where the point queries are

* `P₀ = v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀`: the shared vertex and the top of `C₁` in both directions
  (codes `1`, `0`), and the cap query if its far arm is on `C₁`;
* `P₁ = t'₁ ++ t'₀ ++ k₁`: the top of `C₂` in both directions and the cap query if its far arm
  is on `C₂`.

`PtLists` collects the `PtAns` facts; `cover_of` proves `Cover` and the validity of all queries.
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Merge (FreeAt lend rend)

variable (J : Merge.Junction) (Q : Polygon)

theorem geoQ_append (i : ℕ) (A B : List (ℕ × ℕ × ℕ)) :
    geoQ J Q i (A ++ B) = geoQ J Q i A ∪ geoQ J Q i B := by
  ext x; simp only [geoQ, List.mem_append, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq | hq, rfl⟩
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨q, Or.inl hq, rfl⟩
    · exact ⟨q, Or.inr hq, rfl⟩

theorem endQ_union (S₁ S₂ : Set (Set Point)) : endQ (S₁ ∪ S₂) = endQ S₁ ∪ endQ S₂ := by
  ext x; simp only [endQ, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨c, hc | hc, rfl⟩ | ⟨c, hc | hc, rfl⟩)
    · exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr ⟨c, hc, rfl⟩)
  · rintro ((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩))
    · exact Or.inl ⟨c, Or.inl hc, rfl⟩
    · exact Or.inr ⟨c, Or.inl hc, rfl⟩
    · exact Or.inl ⟨c, Or.inr hc, rfl⟩
    · exact Or.inr ⟨c, Or.inr hc, rfl⟩

theorem geo_ptAns {i : ℕ} {z : Point} {σ : ℝ} {l : List (ℕ × ℕ × ℕ)} (h : PtAns J Q i z σ l) :
    geoQ J Q i l ⊆ {(z, σ)} ∧ (FreeAt J.whole z σ → (z, σ) ∈ geoQ J Q i l) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨-, -, hp, hd⟩ := h.1 q hq
    rw [hp, hd]; rfl
  · cases l with
    | nil => exact absurd hf (h.2 rfl)
    | cons q l =>
      obtain ⟨-, -, hp, hd⟩ := h.1 q (by simp)
      exact ⟨q, by simp, by rw [hp, hd]⟩

theorem ok_ptAns {i : ℕ} {z : Point} {σ : ℝ} {l : List (ℕ × ℕ × ℕ)} (h : PtAns J Q i z σ l) :
    ∀ q ∈ l, QueryOK J Q i q ∧ HeightOK J Q i q := fun q hq =>
  ⟨(h.1 q hq).1, (h.1 q hq).2.1⟩

/-- The chord-end queries have the heights of their codes. -/
theorem endQL_height (i : ℕ) {N : NF} (hN : IsNF (chainModel (sideChain J i)) Q N) :
    ∀ q ∈ endQL N.chords, HeightOK J Q i q := by
  intro q hq
  simp only [endQL, List.mem_map, List.mem_range] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  have hk : j / 2 < N.chords.length := by omega
  have hA := hN.2.2.1 (j / 2) hk
  unfold NF.chord at hA
  obtain ⟨⟨-, -, -, hml, -⟩, ⟨-, -, -, hmr, -⟩⟩ := hA
  unfold HeightOK
  split_ifs
  · simp only [Nat.add_sub_cancel]
    exact hml.1
  · simp only [Nat.add_sub_cancel]
    exact hmr.1

/-- The nearer arm of the cap is `u` (the far arm `[v, w]` is on `C₂`). -/
def NearU : Prop := |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2|

/-- The cap queries of the two sides. -/
def CapAns (k₀ k₁ : List (ℕ × ℕ × ℕ)) : Prop :=
  (SharedExtremum J → (¬ NearU J → PtAns J Q 0 (capOrigin J) (capDir J) k₀ ∧ k₁ = []) ∧
    (NearU J → k₀ = [] ∧ PtAns J Q 1 (capOrigin J) (capDir J) k₁)) ∧
  (¬ SharedExtremum J → k₀ = [] ∧ k₁ = [])

/-- The point queries of the two sides. -/
structure PtLists (v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁ : List (ℕ × ℕ × ℕ)) : Prop where
  v₁ : PtAns J Q 0 (J.whole.vertex J.m₁) 1 v₁
  v₀ : PtAns J Q 0 (J.whole.vertex J.m₁) (-1) v₀
  t₁ : PtAns J Q 0 (J.whole.vertex J.left.topIdx) 1 t₁
  t₀ : PtAns J Q 0 (J.whole.vertex J.left.topIdx) (-1) t₀
  t'₁ : PtAns J Q 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) 1 t'₁
  t'₀ : PtAns J Q 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) (-1) t'₀
  cap : CapAns J Q k₀ k₁

theorem cover_of {N₁ N₂ : NF} (hN₁ : IsNF (chainModel J.left) Q N₁)
    (hN₂ : IsNF (chainModel J.right) Q N₂) {v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁ : List (ℕ × ℕ × ℕ)}
    (hP : PtLists J Q v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁) :
    Cover J Q (N₁.F (chainModel J.left) Q) (N₂.F (chainModel J.right) Q)
        (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀))
        (endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁)) ∧
      (∀ q ∈ endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀),
        QueryOK J Q 0 q ∧ HeightOK J Q 0 q) ∧
      (∀ q ∈ endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁), QueryOK J Q 1 q ∧ HeightOK J Q 1 q) := by
  have hN₁' : IsNF (chainModel (sideChain J 0)) Q N₁ := hN₁
  have hN₂' : IsNF (chainModel (sideChain J 1)) Q N₂ := hN₂
  obtain ⟨ok₁, ge₁⟩ := endQL_ok J Q 0 hN₁'
  obtain ⟨ok₂, ge₂⟩ := endQL_ok J Q 1 hN₂'
  have ge₁' : geoQ J Q 0 (endQL N₁.chords) = endQ (N₁.F (chainModel J.left) Q) := ge₁
  have ge₂' : geoQ J Q 1 (endQL N₂.chords) = endQ (N₂.F (chainModel J.right) Q) := ge₂
  have he₁ := endQL_height J Q 0 hN₁'
  have he₂ := endQL_height J Q 1 hN₂'
  obtain ⟨gv₁, fv₁⟩ := geo_ptAns J Q hP.v₁
  obtain ⟨gv₀, fv₀⟩ := geo_ptAns J Q hP.v₀
  obtain ⟨gt₁, ft₁⟩ := geo_ptAns J Q hP.t₁
  obtain ⟨gt₀, ft₀⟩ := geo_ptAns J Q hP.t₀
  obtain ⟨gs₁, fs₁⟩ := geo_ptAns J Q hP.t'₁
  obtain ⟨gs₀, fs₀⟩ := geo_ptAns J Q hP.t'₀
  -- the cap pieces
  have gk : geoQ J Q 0 k₀ ∪ geoQ J Q 1 k₁ ⊆ capQ J ∧
      (∀ x ∈ capQ J, FreeAt J.whole x.1 x.2 → x ∈ geoQ J Q 0 k₀ ∪ geoQ J Q 1 k₁) := by
    obtain ⟨hc1, hc2⟩ := hP.cap
    by_cases hx : SharedExtremum J
    · obtain ⟨hn1, hn2⟩ := hc1 hx
      by_cases hu : NearU J
      · obtain ⟨e0, h1⟩ := hn2 hu
        obtain ⟨g, f⟩ := geo_ptAns J Q h1
        subst e0
        refine ⟨fun x hx' => ?_, fun x hx' hf => ?_⟩
        · rcases hx' with ⟨q, hq, -⟩ | hx'
          · simp at hq
          · have := g hx'; simp only [Set.mem_singleton_iff] at this; subst this
            exact ⟨hx, rfl⟩
        · obtain ⟨-, rfl⟩ := hx'; exact Or.inr (f hf)
      · obtain ⟨h0, e1⟩ := hn1 hu
        obtain ⟨g, f⟩ := geo_ptAns J Q h0
        subst e1
        refine ⟨fun x hx' => ?_, fun x hx' hf => ?_⟩
        · rcases hx' with hx' | ⟨q, hq, -⟩
          · have := g hx'; simp only [Set.mem_singleton_iff] at this; subst this
            exact ⟨hx, rfl⟩
          · simp at hq
        · obtain ⟨-, rfl⟩ := hx'; exact Or.inl (f hf)
    · obtain ⟨e0, e1⟩ := hc2 hx
      subst e0 e1
      refine ⟨fun x hx' => ?_, fun x hx' _ => absurd hx'.1 hx⟩
      rcases hx' with ⟨q, hq, -⟩ | ⟨q, hq, -⟩ <;> simp at hq
  have okk : (∀ q ∈ k₀, QueryOK J Q 0 q ∧ HeightOK J Q 0 q) ∧
      ∀ q ∈ k₁, QueryOK J Q 1 q ∧ HeightOK J Q 1 q := by
    obtain ⟨hc1, hc2⟩ := hP.cap
    by_cases hx : SharedExtremum J
    · obtain ⟨hn1, hn2⟩ := hc1 hx
      by_cases hu : NearU J
      · obtain ⟨e0, h1⟩ := hn2 hu
        subst e0
        exact ⟨fun q hq => by simp at hq, ok_ptAns J Q h1⟩
      · obtain ⟨h0, e1⟩ := hn1 hu
        subst e1
        exact ⟨ok_ptAns J Q h0, fun q hq => by simp at hq⟩
    · obtain ⟨e0, e1⟩ := hc2 hx
      subst e0 e1
      exact ⟨fun q hq => by simp at hq, fun q hq => by simp at hq⟩
  set Z := fuseZ J (N₁.F (chainModel J.left) Q) (N₂.F (chainModel J.right) Q)
  have zv₁ : (J.whole.vertex J.m₁, (1 : ℝ)) ∈ Z := Or.inl (Or.inl (Or.inr (Or.inl rfl)))
  have zv₀ : (J.whole.vertex J.m₁, (-1 : ℝ)) ∈ Z := Or.inl (Or.inl (Or.inr (Or.inr rfl)))
  have zt₁ : (J.whole.vertex J.left.topIdx, (1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr (Or.inl (Or.inl rfl)))
  have zt₀ : (J.whole.vertex J.left.topIdx, (-1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr (Or.inl (Or.inr rfl)))
  have zs₁ : (J.whole.vertex (J.m₁ + J.right.topIdx), (1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  have zs₀ : (J.whole.vertex (J.m₁ + J.right.topIdx), (-1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr (Or.inr (Or.inr rfl)))
  have ze₁ : endQ (N₁.F (chainModel J.left) Q) ⊆ Z := fun x h =>
    Or.inl (Or.inl (Or.inl (by rw [endQ_union]; exact Or.inl h)))
  have ze₂ : endQ (N₂.F (chainModel J.right) Q) ⊆ Z := fun x h =>
    Or.inl (Or.inl (Or.inl (by rw [endQ_union]; exact Or.inr h)))
  have zk : capQ J ⊆ Z := fun x h => Or.inr h
  have sing : ∀ {i : ℕ} {l : List (ℕ × ℕ × ℕ)} {y : Point × ℝ}, geoQ J Q i l ⊆ {y} → y ∈ Z →
      geoQ J Q i l ⊆ Z := fun h hy x hx => by
    have := h hx; rw [Set.mem_singleton_iff] at this; rwa [this]
  have mono : ∀ {i : ℕ} {A B : List (ℕ × ℕ × ℕ)}, (∀ q ∈ A, q ∈ B) →
      geoQ J Q i A ⊆ geoQ J Q i B := fun h x ⟨q, hq, hx⟩ => ⟨q, h q hq, hx⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [geoQ_append, geoQ_append, geoQ_append, geoQ_append, geoQ_append, geoQ_append,
      geoQ_append, geoQ_append, ge₁, ge₂]
    refine Set.union_subset (Set.union_subset ze₁ (Set.union_subset (Set.union_subset
      (Set.union_subset (Set.union_subset (sing gv₁ zv₁) (sing gv₀ zv₀)) (sing gt₁ zt₁))
      (sing gt₀ zt₀)) ?_)) (Set.union_subset ze₂ (Set.union_subset (Set.union_subset
      (sing gs₁ zs₁) (sing gs₀ zs₀)) ?_))
    · exact fun x hx => zk (gk.1 (Or.inl hx))
    · exact fun x hx => zk (gk.1 (Or.inr hx))
  · intro x hx hf
    have m₀ : ∀ {l : List (ℕ × ℕ × ℕ)}, (∀ q ∈ l, q ∈ endQL N₁.chords ++
        (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)) → x ∈ geoQ J Q 0 l →
        x ∈ geoQ J Q 0 (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)) ∪
          geoQ J Q 1 (endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁)) := fun h hx => Or.inl (mono h hx)
    have m₁ : ∀ {l : List (ℕ × ℕ × ℕ)}, (∀ q ∈ l, q ∈ endQL N₂.chords ++
        (t'₁ ++ t'₀ ++ k₁)) → x ∈ geoQ J Q 1 l →
        x ∈ geoQ J Q 0 (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)) ∪
          geoQ J Q 1 (endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁)) := fun h hx => Or.inr (mono h hx)
    obtain ((he | hv) | ht) | hk := hx
    · rw [endQ_union] at he
      rcases he with h | h
      · rw [← ge₁'] at h; exact m₀ (fun q hq => by simp [hq]) h
      · rw [← ge₂'] at h; exact m₁ (fun q hq => by simp [hq]) h
    · rcases hv with h | h <;> (try rw [Set.mem_singleton_iff] at h) <;> subst h
      · exact m₀ (fun q hq => by simp [hq]) (fv₁ hf)
      · exact m₀ (fun q hq => by simp [hq]) (fv₀ hf)
    · rcases ht with (h | h) | (h | h) <;> (try rw [Set.mem_singleton_iff] at h) <;> subst h
      · exact m₀ (fun q hq => by simp [hq]) (ft₁ hf)
      · exact m₀ (fun q hq => by simp [hq]) (ft₀ hf)
      · exact m₁ (fun q hq => by simp [hq]) (fs₁ hf)
      · exact m₁ (fun q hq => by simp [hq]) (fs₀ hf)
    · rcases gk.2 x hk hf with h' | h'
      · exact m₀ (fun q hq => by simp [hq]) h'
      · exact m₁ (fun q hq => by simp [hq]) h'
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with h | ((((h | h) | h) | h) | h)
    · exact ⟨ok₁ q h, he₁ q h⟩
    · exact ok_ptAns J Q hP.v₁ q h
    · exact ok_ptAns J Q hP.v₀ q h
    · exact ok_ptAns J Q hP.t₁ q h
    · exact ok_ptAns J Q hP.t₀ q h
    · exact okk.1 q h
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with h | ((h | h) | h)
    · exact ⟨ok₂ q h, he₂ q h⟩
    · exact ok_ptAns J Q hP.t'₁ q h
    · exact ok_ptAns J Q hP.t'₀ q h
    · exact okk.2 q h

end

end FuseAsm

end Chazelle.Core
