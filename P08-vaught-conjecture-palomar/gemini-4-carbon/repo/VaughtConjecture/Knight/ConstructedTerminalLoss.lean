/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LawfulCapping
public import VaughtConjecture.Knight.CapReceivingModel
public import VaughtConjecture.Knight.ExpansionDomain
public import Mathlib.Order.Ideal
public import Mathlib.Basic.Countable.Basic

@[expose] public section

namespace VaughtConjecture.TypeTower.Realization

universe u v w
variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

/-- Preservation of every defined evaluation. -/
def Extends (A B : T.Realization α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : T.Ty α n), A.eval t = some p → B.eval t = some p

theorem Extends.refl (A : T.Realization α M) : A.Extends A := fun _ _ _ h => h

theorem Extends.trans {A B C : T.Realization α M} (h : A.Extends B) (h' : B.Extends C) :
    A.Extends C := fun _ t p hp => h' t p (h t p hp)

end VaughtConjecture.TypeTower.Realization

namespace VaughtConjecture.Knight.ExpansionDomain
open TypeTower StageType Value ExtOrd KnightRealization FixedHeight
open Cardinal StoppingRankFiltration CellScheme.restrictFace
noncomputable section

section TowerScheduler
universe u v w z z'
variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

private def chainUnion (A : ℕ → T.Realization α M) : T.Realization α M where
  eval t := by classical exact if h : ∃ k, ((A k).eval t).isSome then (A h.choose).eval t else none

private theorem chainUnion_eval_some_exists {A : ℕ → T.Realization α M}
    {n : ℕ} {t : Fin n ↪ M} {p : T.Ty α n}
    (hp : (chainUnion A).eval t = some p) : ∃ k, (A k).eval t = some p := by
  classical
  by_cases h : ∃ k, ((A k).eval t).isSome
  · exact ⟨h.choose, (dite_eq_left h).symm.trans hp⟩
  · rw [show (chainUnion A).eval t = none from dite_eq_right h] at hp; cases hp

private theorem extends_of_le {A : ℕ → T.Realization α M}
    (hchain : ∀ k, (A k).Extends (A (k + 1))) {j k : ℕ} (hjk : j ≤ k) :
    (A j).Extends (A k) := by
  induction hjk with
  | refl => exact Realization.Extends.refl _
  | step _ ih => exact ih.trans (hchain _)

private theorem extends_chainUnion {A : ℕ → T.Realization α M}
    (hchain : ∀ k, (A k).Extends (A (k + 1))) (k : ℕ) :
    (A k).Extends (chainUnion A) := by
  classical
  intro n t p hp
  have h : ∃ j, ((A j).eval t).isSome := ⟨k, by rw [hp]; rfl⟩
  have he : (chainUnion A).eval t = (A h.choose).eval t := dite_eq_left h
  rcases Nat.le_total k h.choose with hk | hk
  · exact he.trans (extends_of_le hchain hk t p hp)
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h.choose_spec
    exact (he.trans hq).trans ((extends_of_le hchain hk t q hq).symm.trans hp)

private theorem chainUnion_consistent {A : ℕ → T.Realization α M}
    (hchain : ∀ k, (A k).Extends (A (k + 1)))
    (hcons : ∀ k, (A k).IsExactParentConsistent) :
    (chainUnion A).IsExactParentConsistent := by
  intro m n t p f hp
  obtain ⟨j, hj⟩ := chainUnion_eval_some_exists hp
  cases h : T.pull f p with
  | some q => exact extends_chainUnion hchain j _ q ((hcons j t p f hj).trans h)
  | none =>
    cases he : (chainUnion A).eval (f.trans t) with
    | none => rfl
    | some q =>
      obtain ⟨i, hi⟩ := chainUnion_eval_some_exists he
      have hc := (hcons (max i j) t p f (extends_of_le hchain (le_max_right i j) t p hj)).symm.trans
        (extends_of_le hchain (le_max_left i j) _ q hi)
      rw [h] at hc; cases hc

structure Master (T : TypeTower.{u} Λ) (α : Λ) (M : Type w) where
  n : ℕ
  tuple : Fin n ↪ M
  type : T.Ty α n

namespace Master
variable (s : Master T α M)

def Supported {n : ℕ} (t : Fin n ↪ M) : Prop :=
  ∃ f : Fin n ↪ Fin s.n, f.trans s.tuple = t

theorem supported_iff {n : ℕ} (t : Fin n ↪ M) :
    s.Supported t ↔ ∀ i, t i ∈ Set.range s.tuple := by
  classical
  refine ⟨by rintro ⟨f, rfl⟩ i; exact ⟨f i, rfl⟩, fun h => ?_⟩
  choose f hf using h
  exact ⟨⟨f, fun i j hij => t.injective ((hf i).symm.trans ((congrArg s.tuple hij).trans (hf j)))⟩,
    Function.Embedding.ext hf⟩

def chart : T.Realization α M where
  eval t := by classical exact if h : s.Supported t then T.pull h.choose s.type else none

theorem chart_factor {n : ℕ} (f : Fin n ↪ Fin s.n) :
    s.chart.eval (f.trans s.tuple) = T.pull f s.type := by
  classical
  have h : s.Supported (f.trans s.tuple) := ⟨f, rfl⟩
  have hf : h.choose = f := Function.Embedding.ext fun i =>
    s.tuple.injective (congrArg (fun e : Fin n ↪ M => e i) h.choose_spec)
  simp only [chart, dite_eq_left h, hf]

theorem chart_self : s.chart.eval s.tuple = some s.type := by
  simpa using (s.chart_factor (Function.Embedding.refl _)).trans (T.pull_refl s.type)

theorem supported_of_eval {n : ℕ} {t : Fin n ↪ M} {p : T.Ty α n}
    (h : s.chart.eval t = some p) : s.Supported t := by
  classical
  by_contra ht
  rw [show s.chart.eval t = none from dite_eq_right ht] at h; cases h

theorem consistent : s.chart.IsExactParentConsistent := by
  intro m n t p f hp
  obtain ⟨g, rfl⟩ := s.supported_of_eval hp
  rw [s.chart_factor] at hp
  rw [← Function.Embedding.trans_assoc, s.chart_factor]
  exact T.pull_trans g f s.type p hp

def Extends (s t : Master T α M) : Prop :=
  ∃ f : Fin s.n ↪ Fin t.n, f.trans t.tuple = s.tuple ∧ T.pull f t.type = some s.type

instance : Preorder (Master T α M) where
  le := Extends
  le_refl s := ⟨Function.Embedding.refl _, rfl, T.pull_refl _⟩
  le_trans _ _ _ := fun ⟨f, hf, hp⟩ ⟨g, hg, hq⟩ =>
    ⟨f.trans g, by rw [Function.Embedding.trans_assoc, hg, hf],
      (T.pull_trans g f _ _ hq).trans hp⟩

theorem range_mono {s t : Master T α M} (h : s ≤ t) :
    Set.range s.tuple ⊆ Set.range t.tuple := by
  obtain ⟨f, hf, _⟩ := h
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, congrArg (fun e : Fin s.n ↪ M => e i) hf⟩

theorem eval_eq {s t : Master T α M} (h : s ≤ t)
    {n : ℕ} {a : Fin n ↪ M} (ha : s.Supported a) : t.chart.eval a = s.chart.eval a := by
  obtain ⟨f, hf, hp⟩ := h
  obtain ⟨g, rfl⟩ := ha
  rw [s.chart_factor, ← hf, ← Function.Embedding.trans_assoc, t.chart_factor]
  exact T.pull_trans f g t.type s.type hp

theorem chart_extends {s t : Master T α M} (h : s ≤ t) : s.chart.Extends t.chart :=
  fun _ _ _ hp => (eval_eq h (s.supported_of_eval hp)).trans hp
end Master

structure Task (T : TypeTower.{u} Λ) (α : Λ) (M : Type w) where
  n : ℕ
  root : Fin n ↪ M
  base : T.Ty α n
  Served : T.Realization α M → Prop
  mono : ∀ {A B}, A.Extends B → Served A → Served B

private theorem exists_scheduled_realization {St : Type z} (master : St → Master T α M)
    (absorb : ∀ (s : St) (x : M), ∃ t, master s ≤ master t ∧ x ∈ Set.range (master t).tuple)
    {I : Type z'} [Countable I] [Countable M] (task : I → Task T α M)
    (serve : ∀ (s : St) (i : I), (master s).chart.eval (task i).root = some (task i).base →
      ∃ t, master s ≤ master t ∧ (task i).Served (master t).chart)
    (seed : St) :
    ∃ R : T.Realization α M, R.IsExactParentConsistent ∧ R.IsCovering ∧
      (∀ i, R.eval (task i).root = some (task i).base → (task i).Served R) ∧
      ∀ {n} (t : Fin n ↪ M) (p : T.Ty α n), R.eval t = some p →
        ∃ s, (master s).chart.eval t = some p := by
  classical
  have habsF : ∀ (s : St) (F : Finset M),
      ∃ t, master s ≤ master t ∧ ∀ x ∈ F, x ∈ Set.range (master t).tuple := by
    intro s F
    induction F using Finset.induction_on with
    | empty => exact ⟨s, le_rfl, by simp⟩
    | @insert x F _ ih =>
      obtain ⟨t, hst, ht⟩ := ih
      obtain ⟨r, htr, hr⟩ := absorb t x
      exact ⟨r, hst.trans htr, fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hr
        · exact Master.range_mono htr (ht y hy)⟩
  let Resolved (r : Task T α M) (s : St) : Prop :=
    (master s).Supported r.root ∧
      ((master s).chart.eval r.root ≠ some r.base ∨ r.Served (master s).chart)
  let : Preorder St := Preorder.lift master
  let : Encodable (I ⊕ M) := Encodable.ofCountable _
  let D : I ⊕ M → Order.Cofinal St
    | .inl i => ⟨{s | Resolved (task i) s}, fun s => by
        obtain ⟨t, hst, ht⟩ := habsF s (Finset.univ.image (task i).root)
        have hsupp : (master t).Supported (task i).root :=
          ((master t).supported_iff _).mpr fun j => ht _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        by_cases hp : (master t).chart.eval (task i).root = some (task i).base
        · obtain ⟨q, htq, hq⟩ := serve t i hp
          exact ⟨q, ⟨((master q).supported_iff _).mpr fun j =>
            Master.range_mono htq (((master t).supported_iff _).mp hsupp j), Or.inr hq⟩,
            hst.trans htq⟩
        · exact ⟨t, ⟨hsupp, Or.inl hp⟩, hst⟩⟩
    | .inr x => ⟨{s | x ∈ Set.range (master s).tuple}, fun s => by
        obtain ⟨t, hst, ht⟩ := absorb s x; exact ⟨t, ht, hst⟩⟩
  let A := Order.sequenceOfCofinals seed D
  have hA : Monotone (master ∘ A) := Order.sequenceOfCofinals.monotone seed D
  have hchain : ∀ k, (master (A k)).chart.Extends (master (A (k + 1))).chart :=
    fun k => Master.chart_extends (hA (Nat.le_succ k))
  have hc := chainUnion_consistent hchain fun k => (master (A k)).consistent
  refine ⟨chainUnion fun k => (master (A k)).chart, hc, ?_, ?_,
    fun _ _ hp => let ⟨k, hk⟩ := chainUnion_eval_some_exists hp; ⟨A k, hk⟩⟩
  · intro n t
    choose ks hks using fun i : Fin n =>
      (⟨_, Order.sequenceOfCofinals.encode_mem seed D (.inr (t i))⟩ :
        ∃ k, t i ∈ Set.range (master (A k)).tuple)
    let k := Finset.univ.sup ks
    obtain ⟨f, hf⟩ := ((master (A k)).supported_iff t).mpr fun i =>
      Master.range_mono (hA (Finset.le_sup (Finset.mem_univ i))) (hks i)
    exact ⟨_, (master (A k)).tuple, f, hf, by
      rw [extends_chainUnion hchain k _ _ (master (A k)).chart_self]; rfl⟩
  · intro i hi
    obtain ⟨hs, hn | hserved⟩ := Order.sequenceOfCofinals.encode_mem seed D (.inl i)
    · obtain ⟨f, hf⟩ := hs
      refine False.elim (hn ?_)
      rw [← hf, (master (A _)).chart_factor]
      exact (hc _ _ f (extends_chainUnion hchain _ _ _ (master (A _)).chart_self)).symm.trans (hf ▸ hi)
    · exact (task i).mono (extends_chainUnion hchain _) hserved
end TowerScheduler

section TopFree
universe w
variable {β : LimitStage} {M : Type w}

private def capType {n : ℕ} (Q : S β.1 (n + 1)) (γ : ExtOrd)
    (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ) (hγβ : γ < ofOrd β.1) :
    S β.1 (n + 1) where
  scheme := Q.scheme
  label d := min (Q.label d) γ
  label_bound _ := Or.inl ((min_le_right _ _).trans_lt hγβ)
  respects := FiniteCutCapping.respects_cap Q.respects hγ

private theorem exists_pinned {N n : ℕ} (P : S β.1 N) (hP : ∀ d, P.label d ≠ ⊤)
    (g : Fin n ↪ Fin N) (p : S β.1 n) (hg : typeMap g P = some p)
    (q : S β.1 (n + 1)) (hq : IsCoface p q) (δ : ExtOrd) (hδ : δ < ofOrd β.1) :
    ∃ Q : S β.1 (N + 1), IsCoface P Q ∧ (∀ d, Q.label d ≠ ⊤) ∧
      ∃ q' : S β.1 (n + 1), typeMap (extendFace g) Q = some q' ∧
        ∃ he : q'.scheme = q.scheme,
          ∀ d, min (q'.label d) δ = min (q.label (SemScheme.castCell he d)) δ := by
  classical
  obtain ⟨Q, hQP, hQq⟩ :=
    pinnedCofaceSupply_of_supply (CanonicalCoatomSupply.supply β.2) P g p hg q hq
  obtain ⟨γ, hγ, _, hvγ, hγβ⟩ :=
    FiniteCutCapping.exists_cap_below_limit (Sum.elim P.label fun _ : Unit => δ) β.2
      (by rintro (d | _); exact (P.label_bound d).resolve_right (hP d); exact hδ) (N + 1)
  let Q' := capType Q γ hγ hγβ
  have hPvis := (typeMap_isSome_iff Fin.castSuccEmb Q).mp (by rw [hQP]; rfl)
  have hPe := Option.some.inj ((typeMap_eq_some Fin.castSuccEmb Q hPvis).symm.trans hQP)
  have hQP' : IsCoface P Q' := by
    subst P; rw [IsCoface, typeMap_eq_some Fin.castSuccEmb Q' hPvis]
    exact congrArg some (StageType.ext rfl (heq_of_eq (funext fun d => min_eq_left (hvγ (.inl _)))))
  have hqvis := (typeMap_isSome_iff (extendFace g) Q).mp (by rw [hQq]; rfl)
  obtain rfl := Option.some.inj ((typeMap_eq_some (extendFace g) Q hqvis).symm.trans hQq)
  refine ⟨Q', hQP', fun d => ne_top_of_lt ((min_le_right (Q.label d) γ).trans_lt hγβ),
    Q'.restrictFace (extendFace g) hqvis, typeMap_eq_some (extendFace g) Q' hqvis, rfl, fun d => ?_⟩
  have hδγ : δ ≤ γ := hvγ (.inr ())
  change min (min _ γ) δ = min _ δ
  rw [min_assoc, min_eq_right hδγ]; rfl

structure State (β : LimitStage) (M : Type w) extends Master knightTower β M where
  proper : ∀ d, type.label d ≠ ⊤

private theorem exists_topFree_model [Countable M] [Infinite M]
    (hβ : β.1.card ≤ Cardinal.aleph0) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ {n} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p → ∀ d, p.label d ≠ ⊤ := by
  let Req := Σ n, (Fin n ↪ M) × Σ p : S β.1 n,
    {q : S β.1 (n + 1) // IsCoface p q} × {ν : Ordinal.{0} // ν < β.1}
  haveI : ∀ n : ℕ, Countable (Fin n ↪ M) := fun _ =>
    Function.Injective.countable (f := fun f : Fin _ ↪ M => (f : Fin _ → M)) DFunLike.coe_injective
  haveI : ∀ n : ℕ, Countable (S β.1 n) := StageType.countable_S hβ
  haveI : Countable {ν : Ordinal.{0} // ν < β.1} :=
    ((Ordinal.countable_Iic_of_card_le_aleph0 hβ).mono Set.Iio_subset_Iic_self).to_subtype
  haveI : Countable Req := by dsimp only [Req]; infer_instance
  let Serves (A : KnightRealization β M) : Req → Prop
    | ⟨n, t, _, q, ν⟩ =>
      ∃ (y : M) (hy : y ∉ Set.range t) (r : S β.1 (n + 1)),
        A.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.1.scheme,
          ∀ d, min (r.label d) (ofOrd ν.1) = min (q.1.label (SemScheme.castCell he d)) (ofOrd ν.1)
  let task : Req → Task knightTower β M
    | r@⟨n, t, p, _, _⟩ => ⟨n, t, p, fun A => Serves A r,
        fun h ⟨y, hy, s, hs, he, hc⟩ => ⟨y, hy, s, h _ _ hs, he, hc⟩⟩
  let seed : State β M :=
    { toMaster := ⟨0, Function.Embedding.ofIsEmpty, Classical.choice (StageType.nonempty β.2 0)⟩
      proper := fun d => by
        have hp := (Classical.choice (StageType.nonempty β.2 0)).scheme.scheme.grade_pos d
        have h := FiniteCoverReceiving.grade_le_points
          (Classical.choice (StageType.nonempty β.2 0)).scheme d
        change _ ≤ 0 at h; omega }
  obtain ⟨R, hc, hcover, hs, hfinite⟩ :=
    exists_scheduled_realization State.toMaster
      (fun s x => by
        by_cases hx : x ∈ Set.range s.tuple
        · exact ⟨s, le_rfl, hx⟩
        · obtain ⟨q, _, hq⟩ := exists_highGrade_coface (CanonicalCoatomSupply.supply β.2)
            s.type 0 β.2.pos
          obtain ⟨Q, hQ, hproper, _⟩ := exists_pinned s.type s.proper
            (Function.Embedding.refl _) s.type (typeMap_refl _) q hq ⊥ (bot_lt_ofOrd _)
          exact ⟨⟨⟨s.n + 1, snoc s.tuple x hx, Q⟩, hproper⟩,
            ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc s.tuple x hx, hQ⟩,
            ⟨Fin.last _, snoc_apply_last s.tuple x hx⟩⟩)
      task
      (fun s ⟨n, t, p, q, ν⟩ hr => by
        change s.toMaster.chart.eval t = some p at hr
        obtain ⟨f, rfl⟩ := s.toMaster.supported_of_eval hr
        have hface : typeMap f s.type = some p := (s.toMaster.chart_factor f).symm.trans hr
        obtain ⟨Q, hQP, hQtop, q', hQq, he, hcap⟩ := exists_pinned s.type s.proper f p hface
          q.1 q.2 (ofOrd ν.1) (ofOrd_lt_ofOrd.mpr ν.2)
        obtain ⟨y, hy⟩ := (Set.finite_range s.tuple).infinite_compl.nonempty
        let st' : State β M := ⟨⟨s.n + 1, snoc s.tuple y hy, Q⟩, hQtop⟩
        have hyt : y ∉ Set.range (f.trans s.tuple) := fun ⟨i, hi⟩ => hy ⟨f i, hi⟩
        refine ⟨st', ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc s.tuple y hy, hQP⟩,
          y, hyt, q', ?_, he, hcap⟩
        rw [← extendFace_trans_snoc f hy hyt, st'.toMaster.chart_factor]; exact hQq)
      seed
  have hrec : FiniteCutReceiving R := fun t p hp q hq δ hδ hδβ => by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · exact False.elim ((not_lt_of_ge le_top) hδβ)
    · exact hs ⟨_, t, p, ⟨q, hq⟩, ⟨ν, ofOrd_lt_ofOrd.mp hδβ⟩⟩ hp
  refine ⟨R, hrec.isModel inferInstance hc
    (hcover.toInitialSegment knightTower_permTotal hc.isVisibleFaceConsistent),
    fun t p hp d => ?_⟩
  obtain ⟨s, hs'⟩ := hfinite t p hp
  obtain ⟨f, rfl⟩ := s.toMaster.supported_of_eval hs'
  rw [s.toMaster.chart_factor] at hs'
  have hv := (typeMap_isSome_iff f s.type).mp
    (by change (knightTower.pull f s.type).isSome; rw [hs']; rfl)
  obtain rfl := Option.some.inj ((typeMap_eq_some f s.type hv).symm.trans hs')
  exact s.proper _
end TopFree

theorem cofinal_losses (η : Ordinal.{0}) (hη : η < (aleph 1).ord) :
    ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧ (domain ξ \ domain (ξ + 1)).Nonempty := by
  refine ⟨η, le_rfl, hη, ?_⟩
  obtain ⟨W, hW, htop⟩ := exists_topFree_model (β := blockStage η) (M := ℕ)
    (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hη)))
  have hlt := blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl : η < η + 1)
  have hterm : W.NoProlongationToIn IsModelClass hlt.le := by
    intro hprol
    obtain ⟨k, t, _, ht⟩ := hW.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ ℕ)
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ht
    obtain ⟨R', hR', hred⟩ := (prolongsToIn_isModelClass_iff_on W hlt.le).mp hprol
    have hs' : (R'.reduct hlt.le).eval t = some p := hred ▸ hp
    obtain ⟨p', hpe, -⟩ := eval_reduct_eq_some hlt.le hs'
    obtain ⟨y, hy, q, ⟨Sig, _, hlab⟩, -, hq⟩ :=
      hR'.highGradeDominance t p' hpe (blockStage η).1 hlt
    have hev : W.eval (snoc t y hy) = some (reduceType (blockStage η).2 hlt.le q) := by
      rw [← hred, Realization.reduct_eval, hq]; rfl
    exact htop _ _ hev Sig (truncExt_eq_top_of_ge hlab.le)
  let T : TerminalModel η := ⟨W, hW, hterm⟩
  have hzero : T.toNatModel.atBlockZero = W.reduct (blockStage_zero_le η) := by
    change (liftBlockZero (W.reduct (blockStage_zero_le η))).reduct
      blockStage_zero_le_omegaStage = _
    unfold liftBlockZero; rw [Realization.reduct_reduct, Realization.reduct_refl]
  refine ⟨Quotient.mk knightModelSetoid T.toNatModel, mem_domain_of_model hW hzero.symm,
    fun hnext => ?_⟩
  obtain ⟨V, hV, hVr⟩ := exists_model_of_mem_domain hnext
  exact hterm (Realization.ProlongsToOnIn.prolongsToIn
    ⟨V, hV, eq_of_reduct_eq_of_le η 0 zero_le _ _ (hV.reduct _) hW
      (by rw [Realization.reduct_reduct, hVr, hzero])⟩)

end
end VaughtConjecture.Knight.ExpansionDomain
