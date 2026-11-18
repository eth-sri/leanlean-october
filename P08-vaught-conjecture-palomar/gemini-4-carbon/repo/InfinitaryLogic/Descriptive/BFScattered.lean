/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.List.Lex
public import Mathlib.Data.ENat.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Basic.Finite.Sum
public import InfinitaryLogic.OrdinalUtil
public import InfinitaryLogic.Scott.BackAndForth
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.AnalyticClosure

@[expose] public section

namespace KleeneBrouwer
open Descriptive MeasureTheory Filter Topology Set

def ProperPrefix (x y : List ℕ) : Prop := x <+: y ∧ x ≠ y
def ExtBelow (y x : List ℕ) : Prop := ProperPrefix x y
def HasInfiniteBranch (T : tree ℕ) : Prop :=
  ∃ f : ℕ → List ℕ, (∀ n, f n ∈ T) ∧ ∀ n, ProperPrefix (f n) (f (n + 1))
def extBelow (T : tree ℕ) (y x : ↥T) : Prop := ExtBelow (y : List ℕ) x

instance (T : tree ℕ) : IsStrictOrder ↥T (extBelow T) where
  irrefl _ h := h.2 rfl
  trans _ _ _ h₁ h₂ := ⟨h₂.1.trans h₁.1,
    fun hxz ↦ h₁.2 ((h₂.1.eq_of_length_le (hxz ▸ h₁.1.length_le)).symm.trans hxz)⟩

theorem wellFounded_extBelow_iff_not_hasInfiniteBranch (T : tree ℕ) :
    WellFounded (extBelow T) ↔ ¬ HasInfiniteBranch T := by
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun ⟨h⟩ ⟨f, hf, hstep⟩ ↦ h (RelEmbedding.natGT (fun n ↦ (⟨f n, hf n⟩ : ↥T)) hstep),
    fun h ↦ ⟨fun e ↦ h ⟨fun n ↦ (e n : List ℕ), fun n ↦ (e n).2,
      fun n ↦ e.map_rel_iff.mpr (Nat.lt_succ_self n)⟩⟩⟩

noncomputable def treeHeight (T : tree ℕ) [WellFounded (extBelow T)] : Ordinal :=
  ⨆ x : ↥T, Order.succ (WellFounded.rank (extBelow T) x)

theorem hasInfiniteBranch_iff_exists_seq (T : tree ℕ) :
    HasInfiniteBranch T ↔ ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ T := by
  constructor
  · rintro ⟨f, hf, hstep⟩
    have hchain : ∀ m n, m ≤ n → f m <+: f n := fun m n hmn ↦ by
      induction n, hmn using Nat.le_induction with
      | base => exact List.prefix_refl _
      | succ n _ ih => exact ih.trans (hstep n).1
    have hlen : ∀ n, n ≤ (f n).length := fun n ↦ by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        have := lt_of_le_of_ne (hstep n).1.length_le fun h ↦ (hstep n).2 ((hstep n).1.eq_of_length h)
        omega
    refine ⟨fun i ↦ (f (i + 1)).getD i 0, fun n ↦ ?_⟩
    have heq : List.ofFn (fun i : Fin n ↦ (f (i + 1)).getD i 0) = (f n).take n :=
      List.ext_getElem (by simp [hlen n]) fun i h₁ _ ↦ by
        have hi : i < n := by simpa using h₁
        have hi' : i < (f (i + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self i) (hlen (i + 1))
        simp only [List.getElem_ofFn, List.getElem_take, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi', Option.getD_some]
        exact (hchain (i + 1) n hi).getElem hi'
    rw [heq]; exact Tree.take_mem ⟨f n, hf n⟩
  · rintro ⟨z, hz⟩
    exact ⟨fun n ↦ List.ofFn (fun i : Fin n ↦ z i), hz, fun n ↦
      ⟨by simp only [List.ofFn_succ_last]; exact List.prefix_append _ _,
       fun h ↦ by simpa using congrArg List.length h⟩⟩

private def fstList (l : List ℕ) : List ℕ := l.map fun n ↦ n.unpair.1
private def SndAgrees (l : List ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ i (h : i < l.length), l[i].unpair.2 = y i
private def pairList (s : List ℕ) (y : ℕ → ℕ) : List ℕ := s.mapIdx fun i a ↦ Nat.pair a (y i)

private def witnessTree {X : Type*} (f : (ℕ → ℕ) → X) (T : X → tree ℕ) : tree ℕ :=
  ⟨{l | ∃ y, SndAgrees l y ∧ fstList l ∈ T (f y)}, fun {_ _} ⟨y, hy, hmem⟩ ↦
    ⟨y, fun i hi ↦ by have := hy i (by simp; omega); rwa [List.getElem_append_left hi] at this,
      Tree.mem_of_prefix (by simp [fstList]) hmem⟩⟩

private theorem rank_lt_omega1 {α : Type} [Countable α] (r : α → α → Prop) [WellFounded r]
    (a : α) : WellFounded.rank r a < Ordinal.omega 1 := by
  induction a using WellFounded.induction' r with
  | ind a ih =>
    rw [WellFounded.rank_eq r]
    exact Ordinal.iSup_lt_omega_one fun b ↦ (Cardinal.isSuccLimit_omega 1).succ_lt (ih b b.2)

theorem analytic_tree_rank_bounded {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AnalyticSet A) (T : X → tree ℕ) (hT : ∀ s : List ℕ, IsClosed {x | s ∈ T x})
    (hwf : ∀ x ∈ A, WellFounded (extBelow (T x))) :
    ∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧
      ∀ x (hx : x ∈ A), @treeHeight (T x) (hwf x hx) < β := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact ⟨0, Ordinal.omega_pos 1, fun _ hx ↦ hx.elim⟩
  have hWwf : WellFounded (extBelow (witnessTree f T)) := by
    rw [wellFounded_extBelow_iff_not_hasInfiniteBranch, hasInfiniteBranch_iff_exists_seq]
    rintro ⟨z, hz⟩
    set x : ℕ → ℕ := fun i ↦ (z i).unpair.1 with hx
    set y : ℕ → ℕ := fun i ↦ (z i).unpair.2
    have hzn (n) : ∃ w, SndAgrees (List.ofFn fun i : Fin n ↦ z i) w ∧
        fstList (List.ofFn fun i : Fin n ↦ z i) ∈ T (f w) := hz n
    choose w hw hmem using hzn
    have hfst (n) : fstList (List.ofFn fun i : Fin n ↦ z i) = List.ofFn fun i : Fin n ↦ x i := by
      simp [fstList, hx, List.map_ofFn, Function.comp_def]
    have htend : Tendsto w atTop (𝓝 y) :=
      tendsto_pi_nhds.mpr fun i ↦ tendsto_atTop_of_eventually_const (i₀ := i + 1) fun n hn ↦ by
        have := hw n i (by simp; omega); simp only [List.getElem_ofFn] at this; exact this.symm
    have hbranch (k) : (List.ofFn fun i : Fin k ↦ x i) ∈ T (f y) := by
      refine ((hT _).preimage hf).mem_of_tendsto htend (eventually_atTop.mpr ⟨k, fun n hn ↦ ?_⟩)
      have hn' : (List.ofFn fun i : Fin n ↦ x i) ∈ T (f (w n)) := hfst n ▸ hmem n
      have htake : (List.ofFn fun i : Fin n ↦ x i).take k = List.ofFn fun i : Fin k ↦ x i :=
        List.ext_getElem (by simp; omega) fun _ _ _ ↦ by simp
      exact htake ▸ Tree.mem_of_prefix (List.take_prefix _ _) hn'
    exact (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mp (hwf (f y) (mem_range_self y))
      ((hasInfiniteBranch_iff_exists_seq _).mpr ⟨x, hbranch⟩)
  refine ⟨treeHeight (witnessTree f T) + 1, ?_, ?_⟩
  · rw [← Order.succ_eq_add_one]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt
      (Ordinal.iSup_lt_omega_one fun x ↦
        (Cardinal.isSuccLimit_omega 1).succ_lt (rank_lt_omega1 _ x))
  · rintro _ ⟨y, rfl⟩
    have := hwf (f y) (mem_range_self y)
    let hom : extBelow (T (f y)) →r extBelow (witnessTree f T) :=
      { toFun := fun s ↦ ⟨pairList s y, y, fun i _ ↦ by simp [pairList], by
          have : fstList (pairList s y) = s :=
            List.ext_getElem (by simp [fstList, pairList]) fun _ _ _ ↦ by simp [fstList, pairList]
          rw [this]; exact s.2⟩
        map_rel' := fun {t s} ⟨⟨r, heq⟩, hne⟩ ↦
          ⟨by
            change pairList (s : List ℕ) y <+: pairList (t : List ℕ) y
            rw [← heq]; simp only [pairList, List.mapIdx_append]; exact List.prefix_append _ _,
           fun heq' ↦ hne (by
            have hlen := congrArg List.length heq'
            change (pairList (s : List ℕ) y).length = (pairList (t : List ℕ) y).length at hlen
            rw [← heq] at hlen
            simp only [pairList, List.length_mapIdx, List.length_append] at hlen
            have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
            simpa [hr] using heq)⟩ }
    exact (Ordinal.iSup_le fun x ↦ (Order.succ_le_succ (InfinitaryLogic.rank_le_rank_of_relHom hom x)).trans
      (Ordinal.le_iSup (fun z : ↥(witnessTree f T) ↦
        Order.succ (WellFounded.rank (extBelow (witnessTree f T)) z)) (hom x))).trans_lt (lt_add_one _)
end KleeneBrouwer

universe u v w'

namespace FirstOrder.Language
open Descriptive KleeneBrouwer Structure Cardinal Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

def CodeBFEquiv (α : Ordinal.{0}) (c d : StructureSpace L) : Prop :=
  @BFEquiv L ℕ c.toStructure ℕ d.toStructure α 0 Fin.elim0 Fin.elim0

private def bfLeft (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then j.val / 2 else s[j.val]

private def bfRight (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then s[j.val] else j.val / 2

private theorem bfLeft_append_singleton (s : List ℕ) (x : ℕ) :
    bfLeft (s ++ [x]) = Fin.snoc (bfLeft s)
      (if s.length % 2 = 0 then s.length / 2 else x) ∘ Fin.cast (by simp) := by
  funext ⟨j, hj⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hj : j < s.length + 1) with hlt | rfl
  · have : (Fin.cast (by simp) ⟨j, hj⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_castSucc, bfLeft]
    rw [List.getElem_append_left hlt]
  · have : (Fin.cast (by simp) ⟨s.length, hj⟩ : Fin (s.length + 1)) = Fin.last _ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_last, bfLeft]; split_ifs <;> simp

private theorem bfRight_append_singleton (s : List ℕ) (x : ℕ) :
    bfRight (s ++ [x]) = Fin.snoc (bfRight s)
      (if s.length % 2 = 0 then x else s.length / 2) ∘ Fin.cast (by simp) := by
  funext ⟨j, hj⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hj : j < s.length + 1) with hlt | rfl
  · have : (Fin.cast (by simp) ⟨j, hj⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_castSucc, bfRight]
    rw [List.getElem_append_left hlt]
  · have : (Fin.cast (by simp) ⟨s.length, hj⟩ : Fin (s.length + 1)) = Fin.last _ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_last, bfRight]; split_ifs <;> simp

private def bfTree (c d : StructureSpace L) : tree ℕ :=
  ⟨{s | @SameAtomicType L ℕ c.toStructure s.length ℕ d.toStructure (bfLeft s) (bfRight s)},
    fun {s a} h ↦ by
      have hst : s <+: s ++ [a] := List.prefix_append s [a]
      have h' := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h
        (Fin.castLE hst.length_le)
      have hl : bfLeft (s ++ [a]) ∘ Fin.castLE hst.length_le = bfLeft s := by
        funext j; simp only [Function.comp_apply, bfLeft, Fin.val_castLE]
        split_ifs; rfl; exact (hst.getElem j.2).symm
      have hr : bfRight (s ++ [a]) ∘ Fin.castLE hst.length_le = bfRight s := by
        funext j; simp only [Function.comp_apply, bfRight, Fin.val_castLE]
        split_ifs; exact (hst.getElem j.2).symm; rfl
      rwa [hl, hr] at h'⟩

private theorem isClosed_setOf_mem_bfTree (s : List ℕ) :
    IsClosed {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} := by
  have heq : {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} =
      ⋂ idx : L.AtomicIdx s.length, {p | @AtomicIdx.holds L ℕ p.1.toStructure _ idx (bfLeft s) ↔
        @AtomicIdx.holds L ℕ p.2.toStructure _ idx (bfRight s)} := by
    ext; simp only [Set.mem_ofPred_eq, Set.mem_iInter]; rfl
  rw [heq]
  refine isClosed_iInter fun idx ↦ IsClopen.isClosed ?_
  cases idx with
  | eq i j =>
    by_cases h : (bfLeft s i = bfLeft s j ↔ bfRight s i = bfRight s j) <;>
      simp [AtomicIdx.holds, h, isClopen_empty, isClopen_univ]
  | rel R f =>
    let g : StructureSpace L × StructureSpace L → Bool × Bool :=
      fun p ↦ (p.1 ⟨⟨_, R⟩, bfLeft s ∘ f⟩, p.2 ⟨⟨_, R⟩, bfRight s ∘ f⟩)
    have hg : Continuous g :=
      ((continuous_apply _).comp continuous_fst).prodMk ((continuous_apply _).comp continuous_snd)
    exact (isClopen_discrete {x : Bool × Bool | x.1 = true ↔ x.2 = true}).preimage hg

private theorem structureIso_of_hasInfiniteBranch {c d : StructureSpace L}
    (hb : HasInfiniteBranch (bfTree c d)) : (structureIsoSetoid L).r c d := by
  obtain ⟨z, hz⟩ := (hasInfiniteBranch_iff_exists_seq _).mp hb
  let seqL (j : ℕ) : ℕ := if j % 2 = 0 then j / 2 else z j
  let seqR (j : ℕ) : ℕ := if j % 2 = 0 then z j else j / 2
  have holds {l : ℕ} (g : Fin l → ℕ) (idx : L.AtomicIdx l) :
      @AtomicIdx.holds L ℕ c.toStructure l idx (seqL ∘ g) ↔
        @AtomicIdx.holds L ℕ d.toStructure l idx (seqR ∘ g) := by
    obtain ⟨N, hN⟩ : ∃ N, ∀ k, g k < N :=
      ⟨Finset.univ.sup g + 1, fun k ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))⟩
    have ht : ∀ k, g k < (List.ofFn fun i : Fin N ↦ z i).length := by simpa using hN
    let σ : Fin l → Fin (List.ofFn fun i : Fin N ↦ z i).length := fun k ↦ ⟨g k, ht k⟩
    have h := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ (hz N) σ idx
    have hl : bfLeft (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqL ∘ g := funext fun k ↦ by simp [bfLeft, seqL, σ]
    have hr : bfRight (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqR ∘ g := funext fun k ↦ by simp [bfRight, seqR, σ]
    rwa [hl, hr] at h
  have heq (i j) : seqL i = seqL j ↔ seqR i = seqR j := holds ![i, j] (.eq 0 1)
  let e (m : ℕ) : ℕ := z (2 * m)
  have hinj : Function.Injective e := fun m m' hm ↦ by
    have := (heq (2 * m) (2 * m')).mpr (by simpa [seqR] using hm)
    simpa [seqL] using this
  have hsurj : Function.Surjective e := fun n ↦ ⟨z (2 * n + 1), by
    have := (heq (2 * z (2 * n + 1)) (2 * n + 1)).mp (by simp [seqL, Nat.add_mod])
    have hR2 : seqR (2 * n + 1) = n := by simp [seqR, Nat.add_mod]; omega
    simpa [seqR, hR2, e] using this⟩
  refine ⟨@Language.Equiv.mk L ℕ ℕ c.toStructure d.toStructure (Equiv.ofBijective e ⟨hinj, hsurj⟩)
    (fun f ↦ isEmptyElim f) fun {l} R v ↦ ?_⟩
  have h := holds (fun k ↦ 2 * v k) (.rel R id)
  have hl : seqL ∘ (fun k ↦ 2 * v k) = v := funext fun k ↦ by simp [seqL]
  have hr : seqR ∘ (fun k ↦ 2 * v k) = e ∘ v := funext fun k ↦ by simp [seqR, e]
  simp only [AtomicIdx.holds, Function.comp_id, hl, hr] at h; exact h.symm

private theorem bfEquiv_comp_cast {M N : Type*} {iM : L.Structure M} {iN : L.Structure N}
    {α : Ordinal.{0}} {n m : ℕ} (h : n = m) (a : Fin m → M) (b : Fin m → N) :
    @BFEquiv L M iM N iN α n (a ∘ Fin.cast h) (b ∘ Fin.cast h) ↔ @BFEquiv L M iM N iN α m a b := by
  subst h; rfl

private theorem le_rank_bfTree_of_bfEquiv {c d : StructureSpace L}
    [WellFounded (extBelow (bfTree c d))] {α : Ordinal.{0}} {s : List ℕ} (hs : s ∈ bfTree c d)
    (h : @BFEquiv L ℕ c.toStructure ℕ d.toStructure α s.length (bfLeft s) (bfRight s)) :
    α ≤ WellFounded.rank (extBelow (bfTree c d)) ⟨s, hs⟩ := by
  induction α using Ordinal.limitRecOn generalizing s with
  | zero => exact zero_le
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at h ⊢
    have hex : ∃ x, @BFEquiv L ℕ c.toStructure ℕ d.toStructure β (s ++ [x]).length
        (bfLeft (s ++ [x])) (bfRight (s ++ [x])) := by
      have happ (x) : @BFEquiv L ℕ c.toStructure ℕ d.toStructure β (s ++ [x]).length
          (bfLeft (s ++ [x])) (bfRight (s ++ [x])) ↔
          @BFEquiv L ℕ c.toStructure ℕ d.toStructure β (s.length + 1)
            (Fin.snoc (bfLeft s) (if s.length % 2 = 0 then s.length / 2 else x))
            (Fin.snoc (bfRight s) (if s.length % 2 = 0 then x else s.length / 2)) := by
        rw [bfLeft_append_singleton, bfRight_append_singleton]; exact bfEquiv_comp_cast _ _ _
      by_cases hk : s.length % 2 = 0
      · obtain ⟨y, hy⟩ := @BFEquiv.forth L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (happ y).mpr (by simpa [hk] using hy)⟩
      · obtain ⟨y, hy⟩ := @BFEquiv.back L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (happ y).mpr (by simpa [hk] using hy)⟩
    obtain ⟨x, hx⟩ := hex
    have hmem : s ++ [x] ∈ bfTree c d :=
      (@BFEquiv.zero L ℕ c.toStructure ℕ d.toStructure _ _ _).mp
        (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ zero_le _ _ hx)
    have hrel : extBelow (bfTree c d) ⟨s ++ [x], hmem⟩ ⟨s, hs⟩ :=
      ⟨List.prefix_append s [x], fun he ↦ by simpa using congrArg List.length he⟩
    exact Order.succ_le_of_lt ((ih hmem hx).trans_lt (WellFounded.rank_lt_of_rel hrel))
  | limit β hβ ih =>
    by_contra hlt
    have hsucc := hβ.succ_lt (not_le.mp hlt)
    exact (Order.lt_succ _).not_ge (ih _ hsucc hs
      (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ hsucc.le _ _ h))

private theorem t2Space_structureSpace : T2Space (StructureSpace L) :=
  inferInstanceAs (T2Space (StructureSpaceOn L ℕ))

attribute [local instance] t2Space_structureSpace in
theorem isThinOn_of_countable_bfObservations [Countable (Σ l, L.Relations l)]
    (C : Set (StructureSpace L)) {Q : Ordinal.{0} → Type w'} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (Set.range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C, obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    IsThinOn (structureIsoSetoid L) C := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  refine IsThinOn.of_no_cantorAntichain fun ⟨f, hcont, hmem, hineq⟩ ↦ ?_
  have : PolishSpace (ℕ → Bool) := PolishSpace.mk
  have hanti : ∀ p ∈ (range f).offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 := by
    rintro ⟨p₁, p₂⟩ hp h
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hne⟩ := mem_offDiag.mp hp
    exact hineq a b (fun hab ↦ hne (congrArg f hab)) h
  have hwf : ∀ p ∈ (range f).offDiag, WellFounded (extBelow (bfTree p.1 p.2)) := fun p hp ↦
    (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr fun hb ↦
      hanti p hp (structureIso_of_hasInfiniteBranch hb)
  obtain ⟨η, hη, hbound⟩ := analytic_tree_rank_bounded
    (analyticSet_range_of_polishSpace hcont).offDiag (fun p ↦ bfTree p.1 p.2)
    isClosed_setOf_mem_bfTree hwf
  haveI : Countable (Set.range (obs η)) := (hc η hη).to_subtype
  have hunc : ¬ Countable (ℕ → Bool) := by
    rw [← Cardinal.mk_le_aleph0_iff, not_le]; simp [Cardinal.aleph0_lt_continuum]
  refine hunc (Function.Injective.countable
    (f := fun x : ℕ → Bool ↦ (⟨obs η ⟨f x, hmem x⟩, ⟨_, rfl⟩⟩ : Set.range (obs η)))
    fun x y hxy ↦ ?_)
  by_contra hne
  have hfne : f x ≠ f y := fun h ↦ hineq x y hne (h ▸ (structureIsoSetoid L).refl _)
  have hbf : CodeBFEquiv η (f x) (f y) := hobs η hη ⟨f x, hmem x⟩ ⟨f y, hmem y⟩ (Subtype.ext_iff.mp hxy)
  have hp : (f x, f y) ∈ (range f).offDiag := mem_offDiag.mpr ⟨⟨x, rfl⟩, ⟨y, rfl⟩, hfne⟩
  haveI := hwf (f x, f y) hp
  have hroot : @BFEquiv L ℕ (f x).toStructure ℕ (f y).toStructure η ([] : List ℕ).length
      (bfLeft []) (bfRight []) := by
    have hl : bfLeft [] = Fin.elim0 := funext fun j ↦ absurd j.2 (by simp)
    have hr : bfRight [] = Fin.elim0 := funext fun j ↦ absurd j.2 (by simp)
    rw [hl, hr]; exact hbf
  have hnil : [] ∈ bfTree (f x) (f y) :=
    (@BFEquiv.zero L ℕ (f x).toStructure ℕ (f y).toStructure _ _ _).mp
      (@BFEquiv.monotone L ℕ (f x).toStructure ℕ (f y).toStructure _ _ _ zero_le _ _ hroot)
  have hlt : η < treeHeight (bfTree (f x) (f y)) :=
    (Order.lt_succ_of_le (le_rank_bfTree_of_bfEquiv hnil hroot)).trans_le
      (Ordinal.le_iSup (fun z : ↥(bfTree (f x) (f y)) ↦
        Order.succ (WellFounded.rank (extBelow (bfTree (f x) (f y))) z)) ⟨[], hnil⟩)
  exact (hlt.trans (hbound (f x, f y) hp)).false

end FirstOrder.Language
