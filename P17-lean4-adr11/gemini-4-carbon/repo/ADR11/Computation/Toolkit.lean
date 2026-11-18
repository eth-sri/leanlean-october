module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

def decC (n c : ℕ) : Finset (Fin n) := univ.filter fun i => c.testBit i
def decF (n : ℕ) (l : List ℕ) : Finset (Finset (Fin n)) := (l.map (decC n)).toFinset
def Valid (n : ℕ) (l : List ℕ) : Prop := ∀ c ∈ l, c < 2 ^ n

lemma testBit_false {n c : ℕ} (hc : c < 2 ^ n) {i : ℕ} (hi : n ≤ i) :
    c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hi))

theorem decC_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    decC n a = decC n b ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => h ▸ rfl⟩
  by_cases hi : i < n
  · simpa [decC] using congrArg ((⟨i, hi⟩ : Fin n) ∈ ·) h
  · rw [testBit_false ha (not_lt.1 hi), testBit_false hb (not_lt.1 hi)]

lemma decC_mod (n c : ℕ) : decC n (c % 2 ^ n) = decC n c := by
  ext i; simp [decC, Nat.testBit_mod_two_pow]

theorem decC_or (n a b : ℕ) : decC n (a ||| b) = decC n a ∪ decC n b := by ext i; simp [decC]

lemma decC_subset_iff {n a b : ℕ} (ha : a < 2 ^ n) :
    decC n a ⊆ decC n b ↔ a &&& b = a := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h i hi => ?_⟩
  · rw [Nat.testBit_and]
    by_cases hi : i < n
    · cases ha' : a.testBit i
      · simp
      · simp; simpa [decC] using h (by simp [decC, ha'] : (⟨i, hi⟩ : Fin n) ∈ decC n a)
    · simp [testBit_false ha (not_lt.1 hi)]
  · simp only [decC, mem_filter, mem_univ, true_and] at hi ⊢
    simpa [Nat.testBit_and, hi] using congrArg (·.testBit i) h

theorem decC_full (n : ℕ) : decC n (2 ^ n - 1) = univ := by ext i; simp [decC]

lemma decC_eq_univ_iff {n a : ℕ} (ha : a < 2 ^ n) : decC n a = univ ↔ a = 2 ^ n - 1 := by
  rw [← decC_full n, decC_inj ha (by have := Nat.one_le_two_pow (n := n); omega)]

lemma mem_decF {n : ℕ} {l : List ℕ} {A : Finset (Fin n)} :
    A ∈ decF n l ↔ ∃ c ∈ l, decC n c = A := by simp [decF]

lemma decF_cons (n c : ℕ) (l : List ℕ) :
    decF n (c :: l) = insert (decC n c) (decF n l) := by simp [decF]

def famMask (n : ℕ) (l : List ℕ) : ℕ := l.foldr (fun c m => 2 ^ (c % 2 ^ n) ||| m) 0

def rootsL (F : List ℕ) : List ℕ := F.filter fun c => F.all fun d => !(c &&& d == c) || d == c

lemma mem_rootsL {F : List ℕ} {c : ℕ} :
    c ∈ rootsL F ↔ c ∈ F ∧ ∀ d ∈ F, c &&& d = c → d = c := by
  simp only [rootsL, List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]
  exact ⟨fun ⟨hc, h⟩ => ⟨hc, fun d hd hcd => (h d hd).resolve_left (not_not.2 hcd)⟩,
    fun ⟨hc, h⟩ => ⟨hc, fun d hd => by
      by_cases hcd : c &&& d = c; exacts [Or.inr (h d hd hcd), Or.inl hcd]⟩⟩

lemma decF_rootsL {n : ℕ} {F : List ℕ} (hv : Valid n F) :
    decF n (rootsL F) = roots (decF n F) := by
  ext A; simp only [roots, mem_filter]
  refine ⟨fun hA => ?_, fun ⟨hA, h⟩ => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA; rw [mem_rootsL] at hc
    refine ⟨mem_decF.2 ⟨c, hc.1, rfl⟩, fun B hB hsub => ?_⟩
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rw [hc.2 d hd ((decC_subset_iff (hv c hc.1)).1 hsub)]
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    exact mem_decF.2 ⟨c, mem_rootsL.2 ⟨hc, fun d hd hcd =>
      (decC_inj (hv d hd) (hv c hc)).1 (h _ (mem_decF.2 ⟨d, hd, rfl⟩)
        ((decC_subset_iff (hv c hc)).2 hcd))⟩, rfl⟩

lemma card_roots_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup) :
    #(roots (decF n F)) = (rootsL F).length := by
  have hvr : Valid n (rootsL F) := fun c hc => hv c (mem_rootsL.1 hc).1
  rw [← decF_rootsL hv, decF, List.toFinset_card_of_nodup
    ((hnd.filter _).map_on fun a ha b hb e => (decC_inj (hvr a ha) (hvr b hb)).1 e),
    List.length_map]

def pairsL : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: l => l.map (a, ·) ++ pairsL l

lemma sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [List.flatMap_cons, List.sum_append, ih]

def jumpL : ℕ → List ℕ → List (ℚ × List ℕ)
  | 0, F => [(1, F)]
  | j + 1, F => if (rootsL F).length ≤ 1 then [(1, F)] else
      (pairsL (rootsL F)).flatMap fun p => (jumpL j ((p.1 ||| p.2) :: F)).map fun q =>
        ((((rootsL F).length.choose 2 : ℕ) : ℚ)⁻¹ * q.1, q.2)

lemma jumpMatrix_pow_decF {n : ℕ} : ∀ (j : ℕ) (F : List ℕ), Valid n F → F.Nodup →
    IsForest (decF n F) → ∀ G : Finset (Finset (Fin n)),
    (jumpMatrix ^ j) (decF n F) G = ((jumpL j F).map fun q => if decF n q.2 = G then (q.1 : ℝ) else 0).sum
  | 0, F, _, _, _, G => by by_cases h : decF n F = G <;> simp [jumpL, h]
  | j + 1, F, hv, hnd, hF, G => by
    by_cases hk : (rootsL F).length ≤ 1
    · rw [jumpMatrix_pow_of_card_roots_le_one (by rw [card_roots_decF hv hnd]; exact hk)]
      by_cases h : decF n F = G <;> simp [jumpL, hk, h, eq_comm]
    · have rpair : ∀ {p : ℕ × ℕ}, p ∈ pairsL (rootsL F) →
          (p.1 ∈ rootsL F ∧ p.2 ∈ rootsL F) ∧ decC n p.1 ∈ roots (decF n F) ∧
            decC n p.2 ∈ roots (decF n F) ∧ decC n p.1 ≠ decC n p.2 := fun {p} hp => by
        have hop : ∀ {l : List ℕ}, l.Nodup → p ∈ pairsL l → p.1 ∈ l ∧ p.2 ∈ l ∧ p.1 ≠ p.2 := by
          intro l hl hpl; induction l with
          | nil => simp [pairsL] at hpl
          | cons a l ih =>
            rw [List.nodup_cons] at hl
            rcases List.mem_append.1 hpl with h1 | h2
            · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h1
              exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hb, show a ≠ b by rintro rfl; exact hl.1 hb⟩
            · obtain ⟨h1, h2', hne⟩ := ih hl.2 h2
              exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2', hne⟩
        obtain ⟨h1, h2, hne⟩ := hop (hnd.filter _) hp
        have hvr : Valid n (rootsL F) := fun c hc => hv c (mem_rootsL.1 hc).1
        rw [← decF_rootsL hv]
        exact ⟨⟨h1, h2⟩, mem_decF.2 ⟨_, h1, rfl⟩, mem_decF.2 ⟨_, h2, rfl⟩,
          fun h => hne ((decC_inj (hvr _ h1) (hvr _ h2)).1 h)⟩
      have hsum : ∀ g : Finset (Finset (Fin n)) → ℝ, ∑ F' ∈ merges (decF n F), g F' =
          ((pairsL (rootsL F)).map fun p => g (decF n ((p.1 ||| p.2) :: F))).sum := fun g => by
        have hmp : ∀ {l : List ℕ} {a b : ℕ}, a ∈ l → b ∈ l → a ≠ b →
            (a, b) ∈ pairsL l ∨ (b, a) ∈ pairsL l := by
          intro l a b ha hb hab; induction l with
          | nil => simp at ha
          | cons c l ih =>
            simp only [pairsL, List.mem_append, List.mem_map, Prod.mk.injEq]
            rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
            exacts [absurd rfl hab, Or.inl (Or.inl ⟨b, hb', rfl, rfl⟩),
              Or.inr (Or.inl ⟨a, ha', rfl, rfl⟩), (ih ha' hb').imp Or.inr Or.inr]
        have hlen : ∀ l : List ℕ, (pairsL l).length = l.length.choose 2 := fun l => by
          induction l with
          | nil => rfl
          | cons _ _ ih => simp [pairsL, ih, Nat.choose_succ_succ]
        have hm : merges (decF n F) =
            ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).toFinset := by
          ext F'
          simp only [merges, mem_image, mem_offDiag, List.mem_toFinset, List.mem_map, Prod.exists]
          constructor
          · rintro ⟨A, B, ⟨hA, hB, hAB⟩, rfl⟩
            rw [← decF_rootsL hv] at hA hB
            obtain ⟨a, ha, rfl⟩ := mem_decF.1 hA; obtain ⟨b, hb, rfl⟩ := mem_decF.1 hB
            rcases hmp ha hb (fun h => hAB (h ▸ rfl)) with h | h
            · exact ⟨a, b, h, by rw [decF_cons, decC_or]⟩
            · exact ⟨b, a, h, by rw [decF_cons, decC_or, union_comm]⟩
          · rintro ⟨a, b, hp, rfl⟩
            obtain ⟨_, ha, hb, hne⟩ := rpair hp
            exact ⟨decC n a, decC n b, ⟨ha, hb, hne⟩, by rw [decF_cons, decC_or]⟩
        have hcard := hF.card_merges; rw [hm] at hcard ⊢
        have hnd' : ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).Nodup :=
          List.dedup_eq_self.1 ((List.dedup_sublist _).eq_of_length
            (by rw [← List.card_toFinset, hcard, card_roots_decF hv hnd, List.length_map, hlen]))
        rw [List.sum_toFinset _ hnd', List.map_map]; rfl
      rw [jumpMatrix_pow_succ_apply (by rw [card_roots_decF hv hnd]; omega),
        hsum, card_roots_decF hv hnd, jumpL, ite_eq_right hk,
        sum_map_flatMap, ← List.sum_map_mul_left]
      congr 1; refine List.map_congr_left fun p hp => ?_
      obtain ⟨⟨h1, h2⟩, ha, hb, hne⟩ := rpair hp
      have hv' : Valid n ((p.1 ||| p.2) :: F) := fun c hc =>
        (List.mem_cons.1 hc).elim
          (fun e => e ▸ Nat.or_lt_two_pow (hv _ (mem_rootsL.1 h1).1) (hv _ (mem_rootsL.1 h2).1)) (hv c)
      have hnd' : ((p.1 ||| p.2) :: F).Nodup := List.nodup_cons.2
        ⟨fun h => union_not_mem_of_mem_roots ha hb hne (decC_or n p.1 p.2 ▸ mem_decF.2 ⟨_, h, rfl⟩), hnd⟩
      have hF' : IsForest (decF n ((p.1 ||| p.2) :: F)) := by
        rw [decF_cons, decC_or]; exact hF.isForest_merge ha hb
      rw [jumpMatrix_pow_decF j _ hv' hnd' hF' G, ← List.sum_map_mul_left, List.map_map]
      congr 1; refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp_apply]; split_ifs <;> push_cast <;> ring

def checkF (n : ℕ) (F : List ℕ) : Bool :=
  decide (∀ c ∈ F, c < 2 ^ n) && decide F.Nodup && F.all (· != 0) &&
    F.all fun c => F.all fun d => (c &&& d == c) || (c &&& d == d) || (c &&& d == 0)

def unrootL (m : ℕ) (F : List ℕ) : List ℕ :=
  let G := F.filter fun c => c % 2 ^ m != 2 ^ m - 1
  G ++ G.map ((2 ^ m - 1) ^^^ ·)

def flatMapO {α β : Type*} (f : α → Option (List β)) : List α → Option (List β)
  | [] => some []
  | a :: l => match f a, flatMapO f l with
    | some x, some y => some (x ++ y)
    | _, _ => none

def gPoly : ℕ → ℕ → List (ℚ × ℕ)
  | 1, 1 => [(1, 0)]
  | 2, 1 => [(1, 0), (-1, 1)] | 2, 2 => [(1, 1)]
  | 3, 1 => [(1, 0), (-3/2, 1), (1/2, 3)] | 3, 2 => [(3/2, 1), (-3/2, 3)] | 3, 3 => [(1, 3)]
  | 4, 1 => [(1, 0), (-9/5, 1), (1, 3), (-1/5, 6)]
  | 4, 2 => [(9/5, 1), (-3, 3), (6/5, 6)] | 4, 3 => [(2, 3), (-2, 6)] | 4, 4 => [(1, 6)]
  | _, _ => []

structure CTerm where
  coef : ℚ
  key : List (ℕ × ℕ)
  forest : List ℕ

noncomputable def monoVal {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) : ℝ :=
  (k.map fun ae => Real.exp (-len (decC n ae.1)) ^ ae.2).prod

noncomputable def CTerm.val {n : ℕ} (len : Finset (Fin n) → ℝ) (τ : CTerm) : ℝ :=
  τ.coef * monoVal len τ.key

@[simp] theorem monoVal_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : monoVal len [] = 1 := rfl

@[simp] theorem monoVal_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (ae : ℕ × ℕ)
    (k : List (ℕ × ℕ)) :
    monoVal len (ae :: k) = Real.exp (-len (decC n ae.1)) ^ ae.2 * monoVal len k := rfl

lemma monoVal_append {n : ℕ} (len : Finset (Fin n) → ℝ) (k₁ k₂ : List (ℕ × ℕ)) :
    monoVal len (k₁ ++ k₂) = monoVal len k₁ * monoVal len k₂ := by simp [monoVal, List.prod_append]

def kernelL (n a : ℕ) (τ : CTerm) : Option (List CTerm) :=
  let k := (rootsL τ.forest).length
  if checkF n τ.forest then
    if a == 2 ^ n - 1 then
      some ((jumpL (k - 1) τ.forest).map fun q => ⟨τ.coef * q.1, τ.key, q.2⟩)
    else if decide (1 ≤ k ∧ k ≤ 4) then
      some ((List.range k).flatMap fun j =>
        (gPoly k (k - j)).flatMap fun ce =>
          (jumpL j τ.forest).map fun q =>
            ⟨τ.coef * ce.1 * q.1, if ce.2 = 0 then τ.key else τ.key ++ [(a, ce.2)], q.2⟩)
    else none
  else none

inductive BTree where
  | leaf (x : ℕ)
  | bin (a : ℕ) (l r : BTree)

def BTree.code : BTree → ℕ
  | .leaf x => 2 ^ x
  | .bin a _ _ => a

def BTree.wfB (n : ℕ) (H : Finset (Finset (Fin n))) : BTree → Bool
  | .leaf x => decide (x < n)
  | .bin a l r =>
    decide (a < 2 ^ n ∧ l.code < 2 ^ n ∧ r.code < 2 ^ n ∧ l.code ≠ r.code ∧
      (l.code ||| r.code) = a ∧ childClusters H (decC n a) = {decC n l.code, decC n r.code}) &&
      l.wfB n H && r.wfB n H

def BTree.prod2 (L R : List CTerm) : List CTerm :=
  L.flatMap fun τ₁ => R.map fun τ₂ => ⟨τ₁.coef * τ₂.coef, τ₁.key ++ τ₂.key, τ₁.forest ++ τ₂.forest⟩

def BTree.outL (n : ℕ) : BTree → Option (List CTerm)
  | .leaf x => some [⟨1, [], [2 ^ x]⟩]
  | .bin a l r => match l.outL n, r.outL n with
    | some L, some R => flatMapO (kernelL n a) (prod2 L R)
    | _, _ => none

def coefSum (P : List (ℚ × List (ℕ × ℕ))) (k : List (ℕ × ℕ)) : ℚ :=
  ((P.filter fun p => decide (p.2 = k)).map (·.1)).sum

def polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (P.map (·.2) ++ Q.map (·.2)).dedup.all fun k => decide (coefSum P k = coefSum Q k)

noncomputable def evalPoly {n : ℕ} (len : Finset (Fin n) → ℝ) (P : List (ℚ × List (ℕ × ℕ))) : ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

@[simp] theorem evalPoly_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : evalPoly len [] = 0 := rfl

@[simp] theorem evalPoly_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (p : ℚ × List (ℕ × ℕ))
    (P : List (ℚ × List (ℕ × ℕ))) :
    evalPoly len (p :: P) = (p.1 : ℝ) * monoVal len p.2 + evalPoly len P := rfl

def collectM (MP : List (ℕ × ℚ × List (ℕ × ℕ))) (um : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  (MP.filter fun p => p.1 == um).map (·.2)

def certsB (n : ℕ) (R : Option (List CTerm))
    (targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  match R with
  | some M =>
      let MP := M.map fun τ => (famMask n (unrootL n τ.forest), τ.coef, τ.key)
      targets.all fun t => polyEqB (collectM MP (famMask n t.1)) t.2
  | none => false

theorem unrootedDist_sub_of_certsB {n : ℕ} {H : Finset (Finset (Fin n))} (hH : IsHierarchy H)
    (T : BTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : certsB n (T.outL n) targets = true)
    (σ : SpeciesTree (Fin n)) (hsub : σ.clusters ⊆ H)
    {u : List ℕ} {P : List (ℚ × List (ℕ × ℕ))} (ht : (u, P) ∈ targets) :
    σ.unrootedDist id (decF n u) =
      evalPoly (fun A => if A ∈ σ.clusters then σ.length A else 0) P := by
  set len : Finset (Fin n) → ℝ := fun A => if A ∈ σ.clusters then σ.length A else 0
  have heq : ∀ K' B H', forestDist K' len id B H' = csum (childClusters K' B)
      (forestDist K' len id) (fun F => populationKernel len B (F ∪ sampledForest id B) H') :=
    fun K' B H' => by rw [forestDist]; rfl
  have herase : ∀ {K : Finset (Finset (Fin n))}, IsHierarchy K → ∀ {D : Finset (Fin n)},
      D ≠ univ → len D = 0 → ∀ A G, forestDist (K.erase D) len id A G = forestDist K len id A G := by
    intro K hK D hDu hlen A
    induction A using Finset.strongInduction with
    | H A ih =>
    intro G; rw [heq, heq]
    refine (csum_congr (fun B hB => funext fun H' => ih B (mem_childClusters.1 hB).2.1 H') fun _ => rfl).trans ?_
    have hch_iff : ∀ E, E ∈ childClusters (K.erase D) A ↔
        E ∈ (childClusters K A).erase D ∨ (D ∈ childClusters K A ∧ E ∈ childClusters K D) := fun E => by
      simp only [mem_erase (s := childClusters K A), mem_childClusters]
      constructor
      · rintro ⟨hE, hEA, hmax⟩
        obtain ⟨hED, hEH⟩ := mem_erase.1 hE
        by_cases hc : ∃ C ∈ K, E ⊂ C ∧ C ⊂ A
        · obtain ⟨C, hC, hEC, hCA⟩ := hc
          obtain rfl : C = D := by by_contra hne; exact hmax C (mem_erase.2 ⟨hne, hC⟩) hEC hCA
          exact Or.inr ⟨⟨hC, hCA, fun C' hC' h1 h2 =>
              hmax C' (mem_erase.2 ⟨(ne_of_ssubset h1).symm, hC'⟩) (hEC.trans h1) h2⟩,
            ⟨hEH, hEC, fun C' hC' h1 h2 =>
              hmax C' (mem_erase.2 ⟨ne_of_ssubset h2, hC'⟩) h1 (h2.trans hCA)⟩⟩
        · exact Or.inl ⟨hED, hEH, hEA, fun C hC hEC hCA => hc ⟨C, hC, hEC, hCA⟩⟩
      · rintro (⟨hED, hEH, hEA, hmax⟩ | ⟨⟨hDH, hDA, hDmax⟩, hEH, hED, hmax⟩)
        · exact ⟨mem_erase.2 ⟨hED, hEH⟩, hEA, fun C hC => hmax C (mem_of_mem_erase hC)⟩
        · refine ⟨mem_erase.2 ⟨ne_of_ssubset hED, hEH⟩, hED.trans hDA, fun C hC hEC hCA => ?_⟩
          obtain ⟨hCD, hCH⟩ := mem_erase.1 hC; obtain ⟨e, he⟩ := hK.2.2.1 E hEH
          rcases hK.subset_or_subset_of_mem hCH hDH (hEC.subset he) (hED.subset he) with h | h
          · exact hmax C hCH hEC (lt_of_le_of_ne h hCD)
          · exact hDmax C hCH (lt_of_le_of_ne h (Ne.symm hCD)) hCA
    by_cases hD : D ∈ childClusters K A
    · obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
      have hch : childClusters (K.erase D) A = childClusters K D ∪ (childClusters K A).erase D := by
        ext E; simp [hch_iff, hD, or_comm]
      have hdisj : Disjoint (childClusters K D) ((childClusters K A).erase D) :=
        disjoint_left.2 fun E hE hE' =>
          (mem_childClusters.1 (mem_of_mem_erase hE')).2.2 D hDH (mem_childClusters.1 hE).2.1 hDA
      have hφD : ∀ x, forestDist K len id D x = csum (childClusters K D)
          (forestDist K len id) (fun F => if F ∪ sampledForest id D = x then 1 else 0) := fun x => by
        rw [heq]; refine csum_congr (fun _ _ => rfl) fun F => ?_
        rw [populationKernel_ne_univ _ hDu, hlen, kingmanTransition_zero, Matrix.one_apply]
      have hsmono : sampledForest (id : Fin n → Fin n) D ⊆ sampledForest id A := fun C hC => by
        obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC; exact mem_sampledForest.2 ⟨l, hDA.subset hl, rfl⟩
      rw [hch, csum_union hdisj]
      have hmid : csum (childClusters K D) (forestDist K len id) (fun F₁ =>
          csum ((childClusters K A).erase D) (forestDist K len id)
            (fun F₂ => populationKernel len A (F₁ ∪ F₂ ∪ sampledForest id A) G)) =
        ∑ x, forestDist K len id D x * csum ((childClusters K A).erase D) (forestDist K len id)
          (fun F₂ => populationKernel len A (x ∪ F₂ ∪ sampledForest id A) G) := by
        simp_rw [hφD]; unfold csum; simp_rw [sum_mul, mul_assoc]; rw [sum_comm]
        refine sum_congr rfl fun f _ => ?_
        simp_rw [← mul_sum, ite_mul, one_mul, zero_mul]
        rw [sum_ite_eq, ite_eq_left (mem_univ _)]
        congr 1; refine sum_congr rfl fun f₂ _ =>
          congrArg (_ * ·) (congrArg (fun S => populationKernel len A S G) ?_)
        ext C; simp only [mem_union]; have := @hsmono C; tauto
      rw [hmid, ← csum_singleton]
      conv_rhs => rw [← insert_erase hD, insert_eq]
      exact (csum_union (disjoint_singleton_left.2 (notMem_erase D _)) _
        (fun F => populationKernel len A (F ∪ sampledForest id A) G)).symm
    · rw [show childClusters (K.erase D) A = childClusters K A by ext E; simp [hch_iff, hD]]
  have hsub0 : ∀ {K : Finset (Finset (Fin n))}, IsHierarchy K → σ.clusters ⊆ K →
      ∀ G, forestDist K len id univ G = forestDist σ.clusters len id univ G := by
    intro K; induction K using Finset.strongInduction with
    | H K ih =>
    intro hK hk G
    by_cases he : K = σ.clusters; · rw [he]
    obtain ⟨D, hDK, hD0⟩ := exists_of_ssubset (hk.ssubset_of_ne (Ne.symm he))
    have hDu : D ≠ univ := fun e => hD0 (e ▸ σ.univ_mem)
    exact (herase hK hDu (ite_eq_right hD0) univ G).symm.trans <| ih (K.erase D) (erase_ssubset hDK)
      ⟨mem_erase.2 ⟨hDu.symm, hK.1⟩,
        fun x => mem_erase.2 ⟨fun e => hD0 (e.symm ▸ σ.singleton_mem x), hK.2.1 x⟩,
        fun A hA => hK.2.2.1 A (mem_of_mem_erase hA),
        fun A hA B hB => hK.2.2.2 A (mem_of_mem_erase hA) B (mem_of_mem_erase hB)⟩
      (subset_erase.2 ⟨hk, hD0⟩) G
  have hcongr : ∀ {A : Finset (Fin n)}, A ∈ σ.clusters → ∀ G,
      forestDist σ.clusters len id A G = forestDist σ.clusters σ.length id A G := by
    intro A; induction A using Finset.strongInduction with
    | H A ih =>
    intro hA G; rw [forestDist.eq_1 _ len, forestDist.eq_1 _ σ.length]
    refine sum_congr rfl fun f _ => ?_
    rw [show populationKernel (L := Fin n) len A = populationKernel σ.length A by
      unfold populationKernel; split_ifs with hAu <;> [rfl; (dsimp only [len]; rw [ite_eq_left hA])]]
    exact congrArg (· * _) (prod_congr rfl fun B _ =>
      ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _)
  have outL_spec : ∀ (T : BTree), T.wfB n H = true → ∀ M, T.outL n = some M →
      ∀ G, forestDist H len id (decC n T.code) G =
        (M.map fun τ => if decF n τ.forest = G then τ.val len else 0).sum := by
    have hdp : ∀ {k j : ℕ}, 1 ≤ k → k ≤ 4 → 1 ≤ j → j ≤ k → ∀ t : ℝ,
        deathProb k j t = ((gPoly k j).map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum := by
      have hpow : ∀ (m : ℕ) {k j : ℕ}, 1 ≤ k → k ≤ 4 → 1 ≤ j → j ≤ k →
          deathPow m k j = ((gPoly k j).map fun ce => (ce.1 : ℝ) * (-(ce.2 : ℝ)) ^ m).sum := by
        intro m; induction m with
        | zero =>
          intro k j hk1 hk4 hj1 hjk
          interval_cases k <;> interval_cases j <;> simp [deathPow, gPoly] <;> norm_num
        | succ m ih =>
          intro k j hk1 hk4 hj1 hjk; rw [deathPow_succ]
          rcases eq_or_lt_of_le hk1 with rfl | hk2
          · obtain rfl : j = 1 := by omega
            simp [gPoly, zero_pow (Nat.succ_ne_zero m)]
          · have hprev : deathPow m (k - 1) j =
                ((gPoly (k - 1) j).map fun ce => (ce.1 : ℝ) * (-(ce.2 : ℝ)) ^ m).sum := by
              rcases eq_or_lt_of_le hjk with rfl | hlt
              · rw [deathPow_eq_zero_of_lt (by omega)]; interval_cases j <;> simp [gPoly]
              · exact ih (by omega) (by omega) hj1 (by omega)
            rw [hprev, ih hk1 hk4 hj1 hjk]; simp_rw [pow_succ']
            interval_cases k <;> interval_cases j <;>
              simp only [gPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                show Nat.choose 2 2 = 1 from rfl, show Nat.choose 3 2 = 3 from rfl,
                show Nat.choose 4 2 = 6 from rfl] <;> push_cast <;> ring
      intro k j hk1 hk4 hj1 hjk t
      have hs : ∀ L : List (ℚ × ℕ), HasSum
          (fun m : ℕ => t ^ m / (m.factorial : ℝ) * ((L.map fun ce => (ce.1 : ℝ) * (-(ce.2 : ℝ)) ^ m).sum))
          ((L.map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum) := fun L => by
        induction L with
        | nil => simp
        | cons ce L ih =>
          simp only [List.map_cons, List.sum_cons, mul_add]
          refine HasSum.add ?_ ih
          have h1 := (hasSum_exp_mul (-(ce.2 : ℝ)) t).mul_left (ce.1 : ℝ)
          rw [show -(ce.2 : ℝ) * t = (ce.2 : ℕ) * (-t) by ring, Real.exp_nat_mul] at h1
          exact h1.congr_fun fun m => by ring
      exact (hasSum_deathProb k j t).unique
        ((hs (gPoly k j)).congr_fun fun m => by rw [hpow m hk1 hk4 hj1 hjk])
    intro T; induction T with
    | leaf x =>
      intro hwf M hM G
      simp only [BTree.wfB, decide_eq_true_eq] at hwf
      simp only [BTree.outL, Option.some.injEq] at hM; subst hM
      simp only [BTree.code, show decC n (2 ^ x) = {⟨x, hwf⟩} by ext j; simp [decC, Nat.testBit_two_pow, Fin.ext_iff, eq_comm],
        forestDist_id_singleton hH len ⟨x, hwf⟩ G,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, CTerm.val, monoVal_nil,
        Rat.cast_one, one_mul, decF_cons, show decF n [] = ∅ from rfl, insert_empty_eq]
      by_cases hG : G = {{⟨x, hwf⟩}} <;> simp [hG, eq_comm]
    | bin a l r ihl ihr =>
      intro hwf M hM G
      simp only [BTree.wfB, Bool.and_eq_true, decide_eq_true_eq] at hwf
      obtain ⟨⟨⟨ha, hl, hr, hlr, hor, hch⟩, hwfl⟩, hwfr⟩ := hwf
      simp only [BTree.code]
      simp only [BTree.outL] at hM; split at hM; swap; · simp at hM
      rename_i L R hL hR
      have hBC : decC n l.code ≠ decC n r.code := fun e => hlr ((decC_inj hl hr).1 e)
      have hBH : decC n l.code ∈ H := (mem_childClusters.1 (hch ▸ mem_insert_self _ _)).1
      have hCH : decC n r.code ∈ H := (mem_childClusters.1 (hch ▸ mem_insert_of_mem (mem_singleton_self _))).1
      have hu : decC n l.code ∪ decC n r.code = decC n a := (hor ▸ decC_or n l.code r.code).symm
      have hdrop : ∀ F₁ F₂, forestDist H len id (decC n l.code) F₁ *
          forestDist H len id (decC n r.code) F₂ *
          populationKernel len (decC n a) (F₁ ∪ F₂ ∪ sampledForest id (decC n a)) G =
          forestDist H len id (decC n l.code) F₁ * forestDist H len id (decC n r.code) F₂ *
          populationKernel len (decC n a) (F₁ ∪ F₂) G := fun F₁ F₂ => by
        by_cases h1 : forestDist H len id (decC n l.code) F₁ = 0; · simp [h1]
        by_cases h2 : forestDist H len id (decC n r.code) F₂ = 0; · simp [h2]
        have sB := (forestDist_support hH len id hBH h1).2.1
        have sC := (forestDist_support hH len id hCH h2).2.1
        refine congrArg (_ * ·) (congrArg (fun S => populationKernel len (decC n a) S G) ?_)
        exact union_eq_left.2 fun D hD => by
          obtain ⟨x, hx, rfl⟩ := mem_sampledForest.1 hD
          rcases mem_union.1 (hu ▸ hx) with hxB | hxC
          · exact mem_union_left _ (sB (mem_sampledForest.2 ⟨x, hxB, rfl⟩))
          · exact mem_union_right _ (sC (mem_sampledForest.2 ⟨x, hxC, rfl⟩))
      have sc : ∀ (E : List CTerm) (ψ : Finset (Finset (Fin n)) → ℝ),
          ∑ x, (E.map fun τ => if decF n τ.forest = x then τ.val len else 0).sum * ψ x =
            (E.map fun τ => τ.val len * ψ (decF n τ.forest)).sum := fun E ψ => by
        induction E with
        | nil => simp
        | cons _ _ ih => simp [List.map_cons, List.sum_cons, add_mul, sum_add_distrib, ih, ite_mul]
      have kspec : ∀ {τ : CTerm} {K : List CTerm}, kernelL n a τ = some K →
          τ.val len * populationKernel len (decC n a) (decF n τ.forest) G =
            (K.map fun τ' => if decF n τ'.forest = G then τ'.val len else 0).sum := fun {τ K} hkL => by
        unfold kernelL at hkL; dsimp only at hkL
        split_ifs at hkL with hcf hau hc'
        all_goals
          cases hkL
          have ⟨hv, hnd, hF⟩ : Valid n τ.forest ∧ τ.forest.Nodup ∧ IsForest (decF n τ.forest) := by
            simp only [checkF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq,
              Bool.or_eq_true, beq_iff_eq] at hcf
            refine ⟨hcf.1.1.1, hcf.1.1.2, fun A hA => ?_, fun A hA B hB => ?_⟩
            · obtain ⟨c, hc'', rfl⟩ := mem_decF.1 hA
              obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (hcf.1.2 c hc'')
              have hin : i < n := by by_contra hn; simp [testBit_false (hcf.1.1.1 c hc'') (not_lt.1 hn)] at hi
              exact ⟨⟨i, hin⟩, by simp [decC, hi]⟩
            · obtain ⟨c, hc'', rfl⟩ := mem_decF.1 hA; obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
              rcases hcf.2 c hc'' d hd with (h1 | h2) | h3
              · exact Or.inl ((decC_subset_iff (hcf.1.1.1 c hc'')).2 h1)
              · exact Or.inr (Or.inl ((decC_subset_iff (hcf.1.1.1 d hd)).2 (Nat.and_comm d c ▸ h2)))
              · refine Or.inr (Or.inr (disjoint_left.2 fun i hia hib => ?_))
                simp only [decC, mem_filter, mem_univ, true_and] at hia hib
                simpa [Nat.testBit_and, hia, hib] using congrArg (·.testBit i) h3
        · rw [beq_iff_eq.1 hau, decC_full, populationKernel_univ, kingmanAbsorption_apply hF,
            card_roots_decF hv hnd, jumpMatrix_pow_decF _ _ hv hnd hF, ← List.sum_map_mul_left, List.map_map]
          exact congrArg List.sum (List.map_congr_left fun q _ => by
            simp only [Function.comp_apply, CTerm.val]; split_ifs <;> push_cast <;> ring)
        · rw [beq_iff_eq] at hau; rw [decide_eq_true_eq] at hc'
          have hk := card_roots_decF hv hnd
          rw [populationKernel_ne_univ _ (mt (decC_eq_univ_iff ha).1 hau)]
          have hktr : kingmanTransition (len (decC n a)) (decF n τ.forest) G =
              ∑ j ∈ range #(roots (decF n τ.forest)),
                deathProb #(roots (decF n τ.forest)) (#(roots (decF n τ.forest)) - j) (len (decC n a)) *
                  (jumpMatrix ^ j) (decF n τ.forest) G := by
            rw [kingmanTransition_apply hF]
            have hzero : ∀ j < #(roots (decF n τ.forest)),
                #(roots (decF n τ.forest)) - j ≠ #(roots G) → (jumpMatrix ^ j) (decF n τ.forest) G = 0 := by
              intro j hj hne; by_contra h
              have := (jumpMatrix_pow_support hF h).2.2.2; rw [ite_eq_left hj] at this; exact hne this.symm
            by_cases hr : 1 ≤ #(roots G) ∧ #(roots G) ≤ #(roots (decF n τ.forest))
            · rw [sum_eq_single (#(roots (decF n τ.forest)) - #(roots G))]
              · congr 2; omega
              · intro j hj hne; rw [hzero j (mem_range.1 hj) (by omega), mul_zero]
              · intro h; exfalso; rw [mem_range] at h; omega
            · rw [show deathProb _ (#(roots G)) _ * (jumpMatrix ^ _) (decF n τ.forest) G = 0 by
                by_cases hgt : #(roots (decF n τ.forest)) < #(roots G)
                · rw [deathProb_eq_zero_of_lt hgt, zero_mul]
                · suffices (jumpMatrix ^ _) (decF n τ.forest) G = 0 by rw [this, mul_zero]
                  by_contra h; have := (jumpMatrix_pow_support hF h).2.2.2; split_ifs at this <;> omega]
              exact (sum_eq_zero fun j hj => by
                rw [hzero j (mem_range.1 hj) (by have := mem_range.1 hj; omega), mul_zero]).symm
          have sr : ∀ (k : ℕ) (f : ℕ → ℝ), ∑ j ∈ range k, f j = ((List.range k).map f).sum := fun k f => by
            rw [sum_eq_multiset_sum, range_val, ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
          rw [hktr, hk, sr, ← List.sum_map_mul_left, sum_map_flatMap]
          congr 1; refine List.map_congr_left fun j hj => ?_
          rw [List.mem_range] at hj
          rw [sum_map_flatMap, hdp hc'.1 hc'.2 (by omega) (by omega),
            jumpMatrix_pow_decF j _ hv hnd hF G, ← List.sum_map_mul_right, ← List.sum_map_mul_left]
          congr 1; refine List.map_congr_left fun ce _ => ?_
          rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, List.map_map]
          congr 1; refine List.map_congr_left fun q _ => ?_
          by_cases h0 : ce.2 = 0 <;>
            simp only [Function.comp_apply, CTerm.val, h0, ↓reduceIte, monoVal_append, monoVal_cons,
              monoVal_nil, pow_zero] <;> split_ifs <;> push_cast <;> ring
      have sfm : ∀ {P : List CTerm} {N : List CTerm}, flatMapO (kernelL n a) P = some N →
          (N.map fun τ' => if decF n τ'.forest = G then τ'.val len else 0).sum =
            (P.map fun τ => τ.val len * populationKernel len (decC n a) (decF n τ.forest) G).sum := by
        intro P; induction P with
        | nil => intro N hN; simp only [flatMapO, Option.some.injEq] at hN; subst hN; simp
        | cons τ P ih =>
          intro N hN; simp only [flatMapO] at hN; split at hN; swap; · simp at hN
          rename_i x y hx hy; cases hN
          rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, ← kspec hx, ih hy]
      rw [forestDist_of_childClusters_eq_pair hch hBC G]
      simp_rw [hdrop, mul_assoc, ← mul_sum, ihl hwfl L hL, ihr hwfr R hR]
      conv_lhs =>
        arg 2; ext F₁; arg 2
        rw [sc R (fun F₂ => populationKernel len (decC n a) (F₁ ∪ F₂) G)]
      rw [sc L, sfm hM]; unfold BTree.prod2; rw [sum_map_flatMap]
      congr 1; refine List.map_congr_left fun τ₁ _ => ?_
      rw [← List.sum_map_mul_left, List.map_map]
      congr 1; refine List.map_congr_left fun τ₂ _ => ?_
      simp only [Function.comp_apply, CTerm.val, monoVal_append,
        show decF n (τ₁.forest ++ τ₂.forest) = decF n τ₁.forest ∪ decF n τ₂.forest by simp [decF]]
      rw [mul_assoc]; push_cast; ring
  unfold certsB at hc; split at hc; swap; · simp at hc
  rename_i M hM
  simp only [List.all_eq_true] at hc
  have hpoly := hc (u, P) ht
  have hf := outL_spec T hwf M hM
  rw [htop, decC_full] at hf
  have hdu : ∀ F, decF n (unrootL n F) = unroot (decF n F) := fun F => by
    have hu : ∀ c, c % 2 ^ n = 2 ^ n - 1 ↔ decC n c = univ := fun c => by
      rw [← decC_mod n c, decC_eq_univ_iff (Nat.mod_lt _ (Nat.two_pow_pos n))]
    have dc : ∀ a, decC n ((2 ^ n - 1) ^^^ a) = (decC n a)ᶜ := fun _ => by ext i; simp [decC, Nat.testBit_xor]
    ext A; simp only [unrootL, decF, List.map_append, List.map_map, List.toFinset_append,
      mem_union, List.mem_toFinset, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
      Function.comp_apply, hu, dc, mem_unroot]
    exact ⟨fun h => h.imp (fun ⟨c, ⟨hc, hne⟩, e⟩ => ⟨⟨c, hc, e⟩, e ▸ hne⟩)
        (fun ⟨c, ⟨hc, hne⟩, e⟩ => ⟨⟨c, hc, (compl_eq_comm.1 e).symm⟩, (compl_eq_comm.1 e).symm ▸ hne⟩),
      fun h => h.imp (fun ⟨⟨c, hc, e⟩, hne⟩ => ⟨c, ⟨hc, e.symm ▸ hne⟩, e⟩)
        (fun ⟨⟨c, hc, e⟩, hne⟩ => ⟨c, ⟨hc, e.symm ▸ hne⟩, compl_eq_comm.2 e.symm⟩)⟩
  have tb_iff : ∀ {l : List ℕ} {i : ℕ}, (famMask n l).testBit i = true ↔ i < 2 ^ n ∧ decC n i ∈ decF n l := by
    have tbm : ∀ {l : List ℕ} {i : ℕ}, (famMask n l).testBit i = true ↔ ∃ c ∈ l, c % 2 ^ n = i := by
      intro l i; induction l with
      | nil => simp [famMask]
      | cons c l ih =>
        rw [famMask, List.foldr_cons, ← famMask]
        simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, ih,
          List.mem_cons, exists_eq_or_imp]
    intro l i; rw [tbm, mem_decF]; exact ⟨fun ⟨c, hc, e⟩ =>
        e ▸ ⟨Nat.mod_lt _ (Nat.two_pow_pos n), c, hc, (decC_mod n c).symm⟩,
      fun ⟨hi, c, hc, e⟩ => ⟨c, hc, (decC_inj (Nat.mod_lt _ (Nat.two_pow_pos n)) hi).1 ((decC_mod n c).trans e)⟩⟩
  have feq : ∀ a b : List ℕ, decF n a = decF n b ↔ famMask n a = famMask n b := fun a b =>
    ⟨fun h => Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 (by rw [tb_iff, tb_iff, h]), fun h => by
      have sub : ∀ {x y}, famMask n x = famMask n y → decF n x ⊆ decF n y := fun he A hA => by
        obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA; rw [← decC_mod]
        exact (tb_iff.1 (he ▸ tb_iff.2 ⟨Nat.mod_lt _ (Nat.two_pow_pos n), mem_decF.2 ⟨c, hc, (decC_mod n c).symm⟩⟩)).2
      exact Subset.antisymm (sub h) (sub h.symm)⟩
  have ite_add : ∀ (p : Prop) [Decidable p] (a b : ℝ),
      (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) :=
    fun _ _ _ _ => by split_ifs <;> ring
  have hun : ∀ L : List CTerm,
      (∑ G, if unroot G = decF n u then
        (L.map fun τ => if decF n τ.forest = G then τ.val len else 0).sum else 0) =
      evalPoly len (collectM (L.map fun τ => (famMask n (unrootL n τ.forest), τ.coef, τ.key))
        (famMask n u)) := fun L => by
    induction L with
    | nil => simp [collectM]
    | cons τ L ih =>
      simp only [List.map_cons, List.sum_cons, ite_add, sum_add_distrib, ih]
      rw [sum_eq_single (decF n τ.forest)
        (fun G _ hG => by rw [ite_eq_right (Ne.symm hG), ite_self])
        (fun h => absurd (mem_univ _) h), ite_eq_left rfl, ← hdu]
      by_cases hm : famMask n (unrootL n τ.forest) = famMask n u
      · rw [ite_eq_left ((feq _ _).2 hm)]; simp [collectM, hm, CTerm.val]
      · rw [ite_eq_right (mt (feq _ _).1 hm)]; simp [collectM, hm]
  simp only [polyEqB, List.all_eq_true, List.mem_dedup, decide_eq_true_eq] at hpoly
  let Q := collectM (M.map fun τ => (famMask n (unrootL n τ.forest), τ.coef, τ.key)) (famMask n u)
  let S := (Q.map (·.2) ++ P.map (·.2)).toFinset
  have ecs : ∀ (R : List (ℚ × List (ℕ × ℕ))), (∀ p ∈ R, p.2 ∈ S) →
      evalPoly len R = ∑ k ∈ S, (coefSum R k : ℝ) * monoVal len k := fun R hS => by
    induction R with
    | nil => simp [evalPoly, coefSum]
    | cons p R ih =>
      rw [evalPoly_cons, ih fun q hq => hS q (List.mem_cons_of_mem _ hq)]
      have hcs : ∀ k, coefSum (p :: R) k = (if p.2 = k then p.1 else 0) + coefSum R k :=
        fun k => by by_cases h : p.2 = k <;> simp [coefSum, h]
      simp only [hcs, Rat.cast_add, add_mul, sum_add_distrib]
      congr 1; simp [apply_ite (fun x : ℚ => (x : ℝ)), ite_mul, hS p List.mem_cons_self]
  trans ∑ G, if unroot G = decF n u then forestDist H len id univ G else 0
  · unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
    exact sum_congr rfl fun G _ => by
      split_ifs <;> [exact ((hsub0 hH hsub G).trans (hcongr σ.univ_mem G)).symm; rfl]
  · simp_rw [hf]
    rw [hun M,
      ecs Q (fun p hp => by simp [S]; exact Or.inl ⟨p.1, hp⟩),
      ecs P (fun p hp => by simp [S]; exact Or.inr ⟨p.1, hp⟩)]
    exact sum_congr rfl fun k hk => by rw [hpoly k (List.mem_toFinset.1 hk)]

end ADR11
