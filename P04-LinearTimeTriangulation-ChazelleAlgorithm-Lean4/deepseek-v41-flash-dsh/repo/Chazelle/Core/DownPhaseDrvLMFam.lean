module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvLMBkt
public import Chazelle.Core.DownPhaseMathLevel
public import Chazelle.Core.DownPhaseMathHR1
public import Chazelle.Core.GranBD

/-!
# Down-phase level math (D7), part 3: the family after the splice

Abstract setting `LvlCtx`: the chord list `L` of the interior family `S = lset L`, the regions
`reg r` (`r < R`, a bijection onto the regions of `S`), per region a chain `C r` with the
extraction facts and a chain family `F r`, and the kept chords `Lx r` (`lset (Lx r) =
kept (reg r) (F r)`, duplicate-free).

* `LvlCtx.step`: `lset (L ++ L₂) = stepFam Q S F'` (`L₂ = Lx 0 ++ … ++ Lx (R-1)`,
  `F' U = F (rOf U)`);
* `LvlCtx.down`: `DownDrv.downStepG` for it;
* `LvlCtx.ok`: `ChordTriplesOK (L ++ L₂)`;
* `LvlCtx.count`: the size of `L ++ L₂` from per-region bounds;
* `lx_size`: Lemma 2.3 for one kept list.
-/

namespace Chazelle.Core

namespace DrvLM

@[expose] public section

open Set
open DownStep (stepFam)
open Chazelle.Chain (regionsIn freeIn)

/-! ## Lists of chords as sets -/

theorem ncard_lset {α β : Type*} {l : List α} {f : α → β} (hnd : (l.map f).Nodup) :
    {x | ∃ y ∈ l, x = f y}.ncard = l.length := by
  classical
  have : {x | ∃ y ∈ l, x = f y} = ↑(l.map f).toFinset := by
    ext x
    ϴ mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map
    constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨y, hy, h.symm⟩
  Ξ this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map

theorem mem_flat {α : Type*} {Lx : ℕ → List α} {R : ℕ} {y : α} :
    y ∈ (List.range R).flatMap Lx ↔ ∃ r, r < R ∧ y ∈ Lx r := by
  Θ List.mem_flatMap

theorem nodup_flat {α β : Type*} (f : α → β) (Lx : ℕ → List α) (R : ℕ)
    (hnd : ∀ r, r < R → ((Lx r).map f).Nodup)
    (hdis : ∀ r r', r < R → r' < R → ∀ y ∈ Lx r, ∀ y' ∈ Lx r', f y = f y' → r = r') :
    (((List.range R).flatMap Lx).map f).Nodup := by
  induction R with
  | zero => simp
  | succ R ih =>
    Ξ List.range_succ, List.flatMap_append, List.map_append, List.nodup_append
    refine ⟨ih (fun r hr => hnd r (⋄))
      (fun r r' hr hr' => hdis r r' (⋄) (⋄)), by simpa using hnd R (⋄), ?_⟩
    intro a ha b hb hab
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hb
    obtain ⟨r, hr, hyr⟩ := mem_flat.1 hy
    have hy'' : y' ∈ Lx R := by simpa using hy'
    have := hdis r R (⋄) (⋄) y hyr y' hy'' hab
    omega

/-! ## The region index of a region -/

/-- The index of a region (`0` if none). -/
noncomputable def rOf (R : ℕ) (reg : ℕ → Set Point) (U : Set Point) : ℕ := by
  classical
  exact if h : ∃ r, r < R ∧ reg r = U then h.choose else 0

theorem rOf_spec {R : ℕ} {reg : ℕ → Set Point} {U : Set Point} (h : ∃ r, r < R ∧ reg r = U) :
    rOf R reg U < R ∧ reg (rOf R reg U) = U := by
  classical
  unfold rOf
  ϴ dite_eq_left h
  exact h.choose_spec

theorem rOf_reg {R : ℕ} {reg : ℕ → Set Point}
    (hinj : ∀ r r', r < R → r' < R → reg r = reg r' → r = r') {r : ℕ} (hr : r < R) :
    rOf R reg (reg r) = r :=
  hinj _ _ (rOf_spec ⟨r, hr, rfl⟩).1 hr (rOf_spec ⟨r, hr, rfl⟩).2

/-! ## Lemma 2.3 for one kept list -/

theorem lx_size {Q : Polygon} {C : Chain} (hP : C.P.Simple) {F₁ : Set (Set Point)}
    {γ₀ γR D : ℕ} {R₀ : Set Point} {l : List (ℕ × ℕ × ℕ)}
    (hcan : (chainModel C).ChordFamily Q F₁ ∧ (chainModel C).DegLe F₁ D ∧
      (chainModel C).Granular F₁ γR)
    (hγ : γ₀ ≤ γR) (hkept : Gran.lset (interiorModel Q) Q l = Extract.kept R₀ F₁)
    (hnd : (l.map fun y => (recOf y).toSet (interiorModel Q) Q).Nodup) :
    l.length * (γ₀ + 1) ≤ 140 * (D + 2) * (2 * C.m + 1) := by
  have h1 : l.length = (Extract.kept R₀ F₁).ncard := by
    rw [← hkept]; exact (ncard_lset hnd).symm
  have h2 : (Extract.kept R₀ F₁).ncard ≤ F₁.ncard :=
    Set.ncard_le_ncard (fun c hc => hc.1) hcan.1.1
  have h3 := DownMath.lemma23_chain hP hcan.1 hcan.2.1 hcan.2.2
  calc l.length * (γ₀ + 1) ≤ F₁.ncard * (γR + 1) :=
        Nat.mul_le_mul (by rw [h1]; exact h2) (⋄)
    _ ≤ _ := h3

/-! ## The abstract level -/

/-- **The data of one level.** -/
structure LvlCtx (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (R : ℕ) (reg : ℕ → Set Point)
    (C : ℕ → Chain) (F : ℕ → Set (Set Point)) (Lx : ℕ → List (ℕ × ℕ × ℕ)) (D γ : ℕ) :
    Prop where
  hQ : Q.Simple
  hL : ChordTriplesOK (interiorModel Q) Q L
  hdeg : (interiorModel Q).DegLe (Gran.lset (interiorModel Q) Q L) 4
  hmem : ∀ r, r < R → reg r ∈ (interiorModel Q).regions (Gran.lset (interiorModel Q) Q L)
  hinj : ∀ r r', r < R → r' < R → reg r = reg r' → r = r'
  hsurj : ∀ U ∈ (interiorModel Q).regions (Gran.lset (interiorModel Q) Q L),
    ∃ r, r < R ∧ reg r = U
  hEx : ∀ r, r < R → DownDrv.ExtractOK Q (Gran.lset (interiorModel Q) Q L) (reg r) (C r)
  hF : ∀ r, r < R → (chainModel (C r)).ChordFamily Q (F r) ∧ (chainModel (C r)).DegLe (F r) D ∧
    (chainModel (C r)).Semigranular (F r) γ
  hkept : ∀ r, r < R → Gran.lset (interiorModel Q) Q (Lx r) = Extract.kept (reg r) (F r)
  hnd : ∀ r, r < R → ((Lx r).map fun y => (recOf y).toSet (interiorModel Q) Q).Nodup
  hatt : ∀ r, r < R → ∀ y ∈ Lx r, (recOf y).Attached (interiorModel Q) Q ∧ y.1 < Q.n

namespace LvlCtx

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {R : ℕ} {reg : ℕ → Set Point} {C : ℕ → Chain}
  {F : ℕ → Set (Set Point)} {Lx : ℕ → List (ℕ × ℕ × ℕ)} {D γ : ℕ}

theorem fam (X : LvlCtx Q L R reg C F Lx D γ) :
    (interiorModel Q).ChordFamily Q (Gran.lset (interiorModel Q) Q L) := X.hL.1

theorem mem_kept (X : LvlCtx Q L R reg C F Lx D γ) {r : ℕ} (hr : r < R) {y : ℕ × ℕ × ℕ}
    (hy : y ∈ Lx r) : (recOf y).toSet (interiorModel Q) Q ∈ Extract.kept (reg r) (F r) := by
  rw [← X.hkept r hr]; exact ⟨y, hy, rfl⟩

/-- A kept chord is admissible and meets the domain only in its region. -/
theorem loc (X : LvlCtx Q L R reg C F Lx D γ) {r : ℕ} (hr : r < R) {c : Set Point}
    (hc : c ∈ Extract.kept (reg r) (F r)) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ reg r :=
  (X.hEx r hr).loc (X.hF r hr).1.2.1 c hc

theorem step (X : LvlCtx Q L R reg C F Lx D γ) :
    Gran.lset (interiorModel Q) Q (L ++ (List.range R).flatMap Lx) =
      stepFam Q (Gran.lset (interiorModel Q) Q L) (fun U => F (rOf R reg U)) := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · obtain ⟨r, hr, hxr⟩ := mem_flat.1 hx
      refine Or.inr (mem_iUnion₂.2 ⟨reg r, X.hmem r hr, ?_⟩)
      beta_reduce
      Ξ rOf_reg X.hinj hr
      exact X.mem_kept hr hxr
  · rintro (hc | hc)
    · obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨x, List.mem_append_left _ hx, rfl⟩
    · obtain ⟨U, hU, hcU⟩ := mem_iUnion₂.1 hc
      beta_reduce at hcU
      obtain ⟨hr, hrU⟩ := rOf_spec (X.hsurj U hU)
      generalize rOf R reg U = r at hr hrU hcU
      subst hrU
      rw [← X.hkept r hr] at hcU
      obtain ⟨x, hx, rfl⟩ := hcU
      exact ⟨x, List.mem_append_right _ (mem_flat.2 ⟨r, hr, hx⟩), rfl⟩

/-- **The down step of the level.** -/
theorem down (X : LvlCtx Q L R reg C F Lx D γ) :
    (interiorModel Q).ChordFamily Q
        (stepFam Q (Gran.lset (interiorModel Q) Q L) (fun U => F (rOf R reg U))) ∧
      (interiorModel Q).DegLe
        (stepFam Q (Gran.lset (interiorModel Q) Q L) (fun U => F (rOf R reg U))) (D + 4) ∧
      (interiorModel Q).Semigranular
        (stepFam Q (Gran.lset (interiorModel Q) Q L) (fun U => F (rOf R reg U))) γ := by
  have hEx : ∀ U ∈ (interiorModel Q).regions (Gran.lset (interiorModel Q) Q L),
      DownDrv.ExtractOK Q (Gran.lset (interiorModel Q) Q L) U (C (rOf R reg U)) := by
    intro U hU
    obtain ⟨hr, hrU⟩ := rOf_spec (X.hsurj U hU)
    have := X.hEx _ hr
    rw [hrU] at this
    exact this
  have hF : ∀ U ∈ (interiorModel Q).regions (Gran.lset (interiorModel Q) Q L),
      (chainModel (C (rOf R reg U))).ChordFamily Q (F (rOf R reg U)) ∧
        (chainModel (C (rOf R reg U))).DegLe (F (rOf R reg U)) D ∧
        (chainModel (C (rOf R reg U))).Semigranular (F (rOf R reg U)) γ := by
    intro U hU
    obtain ⟨hr, -⟩ := rOf_spec (X.hsurj U hU)
    exact X.hF _ hr
  have h := DownDrv.downStepG (D := D) (γ := γ) X.hQ X.fam X.hdeg (fun U => C (rOf R reg U))
    (fun U => F (rOf R reg U)) hEx hF
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The spliced list is valid.** -/
theorem ok (X : LvlCtx Q L R reg C F Lx D γ) :
    ChordTriplesOK (interiorModel Q) Q (L ++ (List.range R).flatMap Lx) := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel X.hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (interiorModel Q).ChordFamily Q (Gran.lset (interiorModel Q) Q _)
    rw [X.step]; exact X.down.1
  · Ξ List.map_append, List.nodup_append
    refine ⟨X.hL.2.1, nodup_flat _ _ _ X.hnd ?_, ?_⟩
    · intro r r' hr hr' y hy y' hy' hyy
      have h1 := X.loc hr (X.mem_kept hr hy)
      have h2 := X.loc hr' (X.mem_kept hr' hy')
      rw [hyy] at h1
      obtain ⟨p, hp⟩ := Restore.inter_nonempty_of_adm hM h2.1
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint (X.hmem r hr) (X.hmem r' hr') with h | h
      · exact X.hinj r r' hr hr' h
      · exact absurd (h2.2 hp) (Set.disjoint_left.1 h (h1.2 hp))
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      obtain ⟨r, hr, hyr⟩ := mem_flat.1 hy
      have h1 := X.loc hr (X.mem_kept hr hyr)
      obtain ⟨p, hp⟩ := Restore.inter_nonempty_of_adm hM h1.1
      have hpR := Chazelle.Chain.regionsIn_subset (X.hmem r hr) (h1.2 hp)
      refine hpR.2 ⟨(recOf x).toSet (interiorModel Q) Q, ⟨x, hx, rfl⟩, ?_⟩
      rw [hab]; exact hp.1
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact X.hL.2.2.1 x hx
    · obtain ⟨r, hr, hxr⟩ := mem_flat.1 hx
      exact (X.hatt r hr x hxr).1
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact X.hL.2.2.2 x hx
    · obtain ⟨r, hr, hxr⟩ := mem_flat.1 hx
      exact (X.hatt r hr x hxr).2

/-- **The size of the spliced list.** -/
theorem count (X : LvlCtx Q L R reg C F Lx D γ) {γ₀ : ℕ}
    (hper : ∀ r, r < R → (Lx r).length * (γ₀ + 1) ≤
      280 * (D + 2) * DownHost.nk (interiorModel Q) (Gran.lset (interiorModel Q) Q L) (reg r)) :
    (L ++ (List.range R).flatMap Lx).length * (γ₀ + 1) ≤
      L.length * (γ₀ + 1) + 1120 * (D + 2) * (Q.n + 4 * L.length) := by
  classical
  have hsum : ∑ r ∈ Finset.range R,
      DownHost.nk (interiorModel Q) (Gran.lset (interiorModel Q) Q L) (reg r) ≤
        Q.n + 4 * L.length := by
    rw [← Finset.sum_image (f := DownHost.nk (interiorModel Q) (Gran.lset (interiorModel Q) Q L))
      (fun r hr r' hr' h => X.hinj r r' (Finset.mem_range.1 hr) (Finset.mem_range.1 hr') h)]
    have := DownMath.sum_nk_le' X.hQ X.fam ((Finset.range R).image reg) (fun U hU => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hU
      exact X.hmem r (Finset.mem_range.1 hr))
    rwa [show (Gran.lset (interiorModel Q) Q L).ncard = L.length from ncard_lset X.hL.2.1]
      at this
  have hle : ∑ r ∈ Finset.range R, (Lx r).length * (γ₀ + 1) ≤
      ∑ r ∈ Finset.range R, 280 * (D + 2) *
        DownHost.nk (interiorModel Q) (Gran.lset (interiorModel Q) Q L) (reg r) :=
    Finset.sum_le_sum fun r hr => hper r (Finset.mem_range.1 hr)
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hle
  Ξ List.length_append, length_flatMap_range, Nat.add_mul
  have h2 := Nat.mul_le_mul_left (280 * (D + 2)) hsum
  have h3 : 280 * (D + 2) * (Q.n + 4 * L.length) ≤ 1120 * (D + 2) * (Q.n + 4 * L.length) :=
    Nat.mul_le_mul_right _ (⋄)
  omega

end LvlCtx

end

end DrvLM

end Chazelle.Core
