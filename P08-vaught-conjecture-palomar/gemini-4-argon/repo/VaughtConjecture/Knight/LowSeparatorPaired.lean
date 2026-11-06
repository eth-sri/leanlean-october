/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyNormalization
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # The LOW separator on the paired-slot catalogue (grades `K ≥ 2`)

The scalar separator argument of newapproach18 new41 §2 on the existing canonical paired-slot
catalogue (`CanonicalPairedProfiles.inventory`), for a complete field type `X` with a designated
cutoff field `b` and a designated set `N` of non-top donor fields:

* **The partner profile** (`partner`): from a canonical complete profile `s` with
  `h := R_K(M(s)) < s b`, lower only the cutoff field to `h` and normalize.  The partner is
  canonical (`partner_mem`), **its cutoff is exactly `h`** (`partner_cutoff`): `h` is the
  `K`-endpoint `ω·bl + K` of the block `bl` hosting the non-top maximum in `s`'s own canonical
  code (`cutoffCut_eq_endpoint`), and inserting that endpoint into the inventory changes neither
  the orbit flags (its offset is `K`, so it witnesses no orbit) nor the keys below its own key,
  while removing the old cutoff value — which lies at or above the next block — changes nothing
  below `ω·bl + K + 1` (`rank_congr_below`); so its paired code has block `bl` and offset `K`.
  This is represented-endpoint fixation on the actual inventory, not an assumption that
  normalization fixes arbitrary unused endpoints.  All future fields are retained in every
  comparison, since `X` is the complete field type.
* **Prefix agreement** `t ∧ h = s ∧ h` (`partner_cap`, by `normalize_cap` at the grid cut `h`),
  and **the common cut** `κ_K(s, t) = h` (`cut_partner`), `κ` being `SourcePrefixRows.cut` on the
  paired source grid, which coincides with `PairedSlotComparison.largestCommonCut` on canonical
  profiles (`largestCommonCut_eq_cut`).
* **Strict comparison activates LOW** (`activation_of_cut_lt`, `activation_of_chart_lt`): for
  any profile `a`, `κ(a, t) < κ(a, s)` forces `κ(a, t) = h < κ(a, s)` (the ultrametric
  identity), hence every non-top donor field of `a` equals that of `s` (all lie below `h`),
  `M(a) = M(s)`, and `a b > h`: `M(a) < a b`.  A monotone chart reading `κ(a, t)` strictly below
  `κ(a, s)` gives the same.

The family section instantiates this on KVC's `LowOnly.Family`: the partner state is admissible
and canonical, and the strict comparison at an admitted serving state activates its LOW
relation; a chart through `K` reading the private owner and low source as `⊤` then reads every
designated donor top as `⊤` (`donor_top_readback`).  No physical receiver is used: the actual
chart equations `σ (κ(a, t)) < σ (κ(a, s))`, `σ (a c) = ⊤`, `σ (a r) = ⊤` are hypotheses. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowSeparator

open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SharpWitnessComposition
  SourcePrefixRows

/-! ## The non-top donor maximum and the rounded frontier -/

section Scalar

variable {X : Type*} [Fintype X] (K : ℕ) (N : X → Prop) [DecidablePred N] (b : X)

/-- The non-top donor maximum of a complete profile. -/
def donorMax (s : X → ExtOrd) : ExtOrd := (Finset.univ.filter N).sup s

theorem le_donorMax (s : X → ExtOrd) {d : X} (hd : N d) : s d ≤ donorMax N s :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

theorem donorMax_le {s : X → ExtOrd} {c : ExtOrd} (h : ∀ d, N d → s d ≤ c) : donorMax N s ≤ c :=
  Finset.sup_le fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_congr {s a : X → ExtOrd} (h : ∀ d, N d → a d = s d) :
    donorMax N a = donorMax N s :=
  Finset.sup_congr rfl fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_ne_top {s : X → ExtOrd} (hs : ∀ d, s d ≠ ⊤) : donorMax N s ≠ ⊤ :=
  ne_of_lt ((Finset.sup_lt_iff bot_lt_top).mpr fun d _ => lt_top_iff_ne_top.mpr (hs d))

/-- The non-top maximum is bottom or attained. -/
theorem donorMax_cases (s : X → ExtOrd) :
    donorMax N s = ⊥ ∨ ∃ d, N d ∧ s d = donorMax N s := by
  by_cases hne : (Finset.univ.filter N).Nonempty
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup _ hne s
    exact Or.inr ⟨d, (Finset.mem_filter.mp hd).2, he.symm⟩
  · exact Or.inl (by simp [donorMax, Finset.not_nonempty_iff_eq_empty.mp hne])

/-- The rounded frontier `R_K(M(s))`. -/
def cutoffCut (s : X → ExtOrd) : ExtOrd := extVisibilityReplace (donorMax N s) K K

theorem donorMax_le_cutoffCut (s : X → ExtOrd) : donorMax N s ≤ cutoffCut K N s :=
  TopSupport.le_evr_self _ _

/-- The partner: lower only the cutoff field to the rounded frontier, then normalize. -/
def partner [DecidableEq X] (s : X → ExtOrd) : X → ExtOrd :=
  PairedSlotEncoding.normalize K (Function.update s b (cutoffCut K N s))

/-! ## The frontier is a grid endpoint of the canonical code -/

theorem cutoffCut_eq_endpoint {s : X → ExtOrd}
    (hs : s ∈ CanonicalPairedProfiles.inventory X K) :
    cutoffCut K N s = ⊥ ∨
      ∃ (m₀ : Ordinal.{0}) (d₀ : X), s d₀ = ofOrd m₀ ∧
        m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀ ∧
        cutoffCut K N s = ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  rcases ExtOrd.cases (donorMax N s) with hM | hM | ⟨m₀, hM⟩
  · exact Or.inl (by unfold cutoffCut; rw [hM]; rfl)
  · exact absurd hM (donorMax_ne_top N hs.2)
  · rcases donorMax_cases N s with h | ⟨d₀, -, hd₀M⟩
    · exact absurd (h.symm.trans hM) (ofOrd_ne_bot m₀).symm
    · have hm₀ : s d₀ = ofOrd m₀ := hd₀M.trans hM
      have hcode : encode K (values s) m₀ = ofOrd m₀ := by
        have h := congrFun hs.1 d₀
        rwa [PairedSlotEncoding.normalize_ofOrd hm₀, hm₀] at h
      set bl := block K (values s) m₀
      set off := offset K (values s) m₀
      have hdec : m₀ = Ordinal.omega0 * bl + off := (ofOrd_inj.mp hcode).symm
      have hlim : limitPart m₀ = Ordinal.omega0 * bl := by rw [hdec]; exact limitPart_mul_add _ _
      have hfin : finitePart m₀ = off := by rw [hdec]; exact finitePart_mul_add _ _
      have hoff : off ≤ K := offset_le K (values s) m₀
      refine Or.inr ⟨m₀, d₀, hm₀, hdec, ?_⟩
      unfold cutoffCut; rw [hM]
      change extVisibilityReplace (ofOrd m₀) K K = ofOrd (Ordinal.omega0 * bl + K)
      rcases lt_or_eq_of_le hoff with hlt | heq
      · rw [extVisibilityReplace_of_finitePart_lt (hfin ▸ hlt) K, hlim]
      · rw [extVisibilityReplace_of_le_finitePart (by rw [hfin, heq]) K, hdec, heq]

/-! ## The partner's cutoff is the frontier: represented-endpoint fixation -/

section Partner

variable [DecidableEq X]

theorem encode_endpoint {s : X → ExtOrd} {m₀ : Ordinal.{0}} {d₀ : X} (hm₀ : s d₀ = ofOrd m₀)
    (hdec : m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀)
    (hsb : ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) < s b) :
    encode K (values (Function.update s b (ofOrd (Ordinal.omega0 * block K (values s) m₀ + K))))
      (Ordinal.omega0 * block K (values s) m₀ + K) =
      ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  classical
  set S := values s with hSdef
  set bl := block K S m₀
  set off := offset K S m₀
  set h₀ : Ordinal.{0} := Ordinal.omega0 * bl + K with hh₀
  set T := values (Function.update s b (ofOrd h₀)) with hTdef
  set S' : Finset Ordinal.{0} := insert h₀ S with hS'def
  have hoff : off ≤ K := offset_le K S m₀
  have hm₀S : m₀ ∈ S := mem_values.mpr ⟨d₀, hm₀⟩
  have hh₀lim : limitPart h₀ = Ordinal.omega0 * bl := limitPart_mul_add _ _
  have hh₀fin : finitePart h₀ = K := finitePart_mul_add _ _
  have hm₀lim : limitPart m₀ = Ordinal.omega0 * bl := by rw [hdec]; exact limitPart_mul_add _ _
  have hm₀fin : finitePart m₀ = off := by rw [hdec]; exact finitePart_mul_add _ _
  have horb (c) : Orbit K S' c ↔ Orbit K S c :=
    ⟨fun ⟨hf, e, he, hej, hec⟩ => (Finset.mem_insert.mp he).elim
      (fun h => by rw [h, hh₀fin] at hej; omega) (fun he => ⟨hf, e, he, hej, hec⟩),
      fun ⟨hf, e, he, hej, hec⟩ => ⟨hf, e, Finset.mem_insert_of_mem he, hej, hec⟩⟩
  have hkey (c) : key K S' c = key K S c := by
    by_cases ho : Orbit K S c
    · simp only [key, ite_eq_left ho, ite_eq_left ((horb c).mpr ho)]
    · simp only [key, ite_eq_right ho, ite_eq_right fun h => ho ((horb c).mp h)]
  have horb₀ : Orbit K S h₀ ↔ Orbit K S m₀ :=
    ⟨fun ⟨_, e, he, hej, hec⟩ => ⟨hm₀fin ▸ hoff, e, he, hej, hec.trans (hh₀lim.trans hm₀lim.symm)⟩,
      fun ⟨_, e, he, hej, hec⟩ => ⟨hh₀fin ▸ le_rfl, e, he, hej, hec.trans (hm₀lim.trans hh₀lim.symm)⟩⟩
  have hkey₀ : key K S h₀ = key K S m₀ := by
    by_cases ho : Orbit K S m₀
    · simp only [key, ite_eq_left ho, ite_eq_left (horb₀.mpr ho), hh₀lim, hm₀lim]
    · have hoffK : off = K := by_contra fun hne =>
        ho (orbit_of_invisible hm₀S (hm₀fin ▸ lt_of_le_of_ne hoff hne))
      rw [hdec, hoffK]
  have hrank' : PairedSlotEncoding.rank K S' h₀ = PairedSlotEncoding.rank K S m₀ := by
    unfold PairedSlotEncoding.rank
    rw [hkey h₀, hkey₀]
    have himg : PairedSlotEncoding.keys K S' =
        insert (key K S h₀) (PairedSlotEncoding.keys K S) := by
      change S'.image (key K S') = insert (key K S h₀) (S.image (key K S))
      rw [hS'def, Finset.image_insert, hkey h₀]
      exact congrArg _ (Finset.image_congr fun c _ => hkey c)
    rw [himg, Finset.filter_insert, ite_eq_right (by rw [hkey₀]; exact lt_irrefl _)]
  set h' : Ordinal.{0} := Ordinal.omega0 * bl + ((K + 1 : ℕ) : Ordinal.{0}) with hh'
  have hh'fin : K ≤ finitePart h' := by rw [finitePart_mul_add]; exact Nat.le_succ K
  have hh₀h' : h₀ < h' :=
    (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (Nat.lt_succ_self K))
  have heq (c) (hc : c < h') : c ∈ T ↔ c ∈ S' := by
    rw [hTdef, mem_values, hS'def, Finset.mem_insert, hSdef, mem_values]
    constructor
    · rintro ⟨d, hd⟩
      by_cases hdb : d = b
      · subst hdb; rw [Function.update_self] at hd; exact Or.inl (ofOrd_inj.mp hd).symm
      · rw [Function.update_of_ne hdb] at hd; exact Or.inr ⟨d, hd⟩
    · rintro (rfl | ⟨d, hd⟩)
      · exact ⟨b, by rw [Function.update_self]⟩
      · by_cases hdb : d = b
        · subst hdb
          have hc' : c < h₀ + 1 := by rwa [hh', Nat.cast_succ, ← add_assoc, ← hh₀] at hc
          exact absurd (ofOrd_lt_ofOrd.mp (hd ▸ hsb)) (not_lt.mpr (Order.lt_add_one_iff.mp hc'))
        · exact ⟨d, by rw [Function.update_of_ne hdb]; exact hd⟩
  have hrankT : PairedSlotEncoding.rank K T h₀ = PairedSlotEncoding.rank K S' h₀ :=
    rank_congr_below hh'fin heq hh₀h'
  have horbT : Orbit K T h₀ ↔ Orbit K S' h₀ :=
    orbit_congr_below hh'fin heq (by rw [hh₀lim]; exact le_self_add.trans_lt hh₀h')
  have hblock : block K T h₀ = bl := by
    change block K T h₀ = block K S m₀
    unfold block; rw [hrankT, hrank']
    by_cases ho : Orbit K S m₀
    · rw [ite_eq_left (((horbT.trans (horb h₀)).trans horb₀).mpr ho), ite_eq_left ho]
    · rw [ite_eq_right fun h => ho (((horbT.trans (horb h₀)).trans horb₀).mp h), ite_eq_right ho]
  have hoffT : offset K T h₀ = K := by unfold offset; split_ifs <;> [exact hh₀fin; rfl]
  unfold encode; rw [hblock, hoffT]

end Partner

/-- The paired source grid of the complete field type. -/
abbrev grid : Finset ExtOrd := sourceGrid K (Fintype.card X)

/-! ## The partner: canonical, cutoff `h`, prefix agreement, common cut `h` -/

section PartnerProfile

variable [DecidableEq X] {s : X → ExtOrd} (hs : s ∈ CanonicalPairedProfiles.inventory X K)
  (hb : ¬ N b) (hlt : cutoffCut K N s < s b)

include hs hlt in
/-- **The common cut of `s` and its partner is the frontier**: `κ_K(s, t) = h`. -/
theorem cut_partner : cut (grid (X := X) K) s (partner K N b s) = cutoffCut K N s := by
  have hbot : (⊥ : ExtOrd) ∈ grid (X := X) K := sourceGrid_bot _ _
  apply le_antisymm
  · apply le_of_not_gt fun hgt => ?_
    have hcut : partner K N b s b = cutoffCut K N s := by
      unfold partner
      rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, hm₀, hdec, hend⟩
      · rw [h0]
        exact (PairedSlotEncoding.normalize_bot_iff K _ b).mpr (by rw [Function.update_self])
      · rw [PairedSlotEncoding.normalize_ofOrd (by rw [Function.update_self, hend]), hend]
        exact encode_endpoint K b hm₀ hdec (hend ▸ hlt)
    have hag := agree_cut hbot s (partner K N b s) b
    rw [hcut, min_eq_left hgt.le] at hag
    exact lt_irrefl _ (hag ▸ lt_min hlt hgt)
  · refine le_cut ?_ fun d => ?_
    · rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, hm₀, -, hend⟩
      · rw [h0]; exact hbot
      · rw [hend]
        have h1 := block_le_twice_card (j := K) (mem_values.mpr ⟨d₀, hm₀⟩)
        have h2 := values_card_le s
        exact sourceGrid_endpoint (by omega)
    · rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, hm₀, hdec, hend⟩
      · rw [h0, min_eq_right bot_le, min_eq_right bot_le]
      · unfold partner; rw [hend]
        refine (CanonicalPairedProfiles.normalize_cap X K hs (fun e => ?_) d).symm
        by_cases heb : e = b
        · subst heb; rw [Function.update_self, min_self, min_eq_right (hend ▸ hlt.le)]
        · rw [Function.update_of_ne heb]

end PartnerProfile

end Scalar

/-! ## The family instance: KVC's gate-free LOW family -/

section Family

open LowOnly

variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

/-- The non-top donor fields among the complete fields. -/
def donorField : LowOnly.Field P C → Prop
  | .inl d => F.p d ≠ ⊤
  | .inr _ => False

instance : DecidablePred (donorField F) := Classical.decPred _

/-- The cutoff field. -/
abbrev cutoffField : LowOnly.Field P C := Sum.inr (Sum.inr ())

/-- The family's non-top maximum is the donor maximum of the complete profile. -/
theorem maximum_eq_donorMax (S : State P C) :
    F.maximum S = donorMax (donorField F) S.profile := by
  apply le_antisymm
  · unfold LowOnly.Family.maximum LowOnly.nonTopMax
    refine Finset.sup_le fun d hd => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact le_donorMax (donorField F) S.profile (d := Sum.inl d) hd
  · refine Finset.sup_le fun x hx => ?_
    have hx' : donorField F x := (Finset.mem_filter.mp hx).2
    rcases x with d | d | d
    · exact LowOnly.le_nonTopMax S.u hx'
    · exact hx'.elim
    · exact hx'.elim

/-- The partner state: only the cutoff is lowered to the frontier, then normalized. -/
def partnerState (S : State P C) : State P C :=
  (⟨S.u, S.v, cutoffCut K (donorField F) S.profile⟩ : State P C).normalize K

theorem partnerState_profile (S : State P C) :
    (partnerState F S).profile =
      partner K (donorField F) (cutoffField (P := P) (C := C)) S.profile := by
  funext d
  unfold partnerState partner
  rw [State.profile_normalize]
  congr 1
  ext (e | e | e) <;> rfl

theorem partnerState_mem {S : State P C} (hcan : S.profile ∈
      CanonicalPairedProfiles.inventory (LowOnly.Field P C) K) :
    (partnerState F S).profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K := by
  rw [partnerState_profile]
  apply CanonicalPairedProfiles.normalize_mem_inventory
  intro d
  by_cases hdb : d = cutoffField
  · subst hdb; rw [Function.update_self]
    exact TopSupport.evr_ne_top (donorMax_ne_top (donorField F) hcan.2) K K
  · rw [Function.update_of_ne hdb]; exact hcan.2 d

theorem partnerState_admissible {S : State P C} (hS : F.Admissible K S)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) (hK : 1 ≤ K) :
    F.Admissible K (partnerState F S) := by
  have hm : F.maximum S < S.b :=
    (maximum_eq_donorMax F S).symm ▸ (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hlt
  exact F.normalize_admissible hK
    { lawfulP := hS.lawfulP
      lawfulC := hS.lawfulC
      shared := hS.shared
      futureP := hS.futureP
      futureC := hS.futureC
      cutoff := by rw [min_self]; exact TopSupport.selfVis_evr_self K _
      low := fun hj _ d hd => (max_le_max hlt.le le_rfl).trans (hS.low hj hm d hd) }

/-- **The separator readback**: at an admitted serving state whose chart reads the partner cut
strictly below the diagonal cut and reads the private owner and low source as `⊤`, every
designated donor top reads `⊤`. -/
theorem serving_readback {S A : State P C} (hA : F.Admissible K A)
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop K) σ)
    (h : σ (cut (grid (X := LowOnly.Field P C) K) A.profile (partnerState F S).profile) <
      σ (cut (grid (X := LowOnly.Field P C) K) A.profile S.profile))
    (hc : σ (A.v F.gap.c) = ⊤) (hr : σ (A.v F.gap.r.1) = ⊤) (d : Cell P.scheme)
    (hd : F.p d = ⊤) : σ (A.u d) = ⊤ := by
  rw [partnerState_profile] at h
  have hlt_cut : cut (grid (X := LowOnly.Field P C) K) A.profile
      (partner K (donorField F) cutoffField S.profile) <
      cut (grid (X := LowOnly.Field P C) K) A.profile S.profile :=
    lt_of_not_ge fun hle => not_lt.mpr (hσ.mono hle) h
  have hbot : (⊥ : ExtOrd) ∈ grid (X := LowOnly.Field P C) K := sourceGrid_bot _ _
  have h1 := cut_triangle hbot A.profile S.profile
    (partner K (donorField F) cutoffField S.profile)
  rw [cut_partner K (donorField F) cutoffField hcan hlt] at h1
  have hu : cutoffCut K (donorField F) S.profile <
      cut (grid (X := LowOnly.Field P C) K) A.profile S.profile :=
    lt_of_not_ge fun hn => absurd ((min_eq_left hn ▸ h1).trans_lt hlt_cut) (lt_irrefl _)
  have hag := agree_cut hbot A.profile S.profile
  have heq : donorMax (donorField F) A.profile = donorMax (donorField F) S.profile :=
    donorMax_congr (donorField F) fun e he =>
      (eq_of_cap_eq_lt (hag e).symm
        (((le_donorMax (donorField F) S.profile he).trans
          (donorMax_le_cutoffCut K (donorField F) S.profile)).trans_lt hu)).symm
  have hab : cutoffCut K (donorField F) S.profile < A.b := by
    have hgt : cutoffCut K (donorField F) S.profile <
        min S.b (cut (grid (X := LowOnly.Field P C) K) A.profile S.profile) := lt_min hlt hu
    exact (hag cutoffField ▸ hgt).trans_le (min_le_left _ _)
  have hm : F.maximum A < A.b := by
    rw [maximum_eq_donorMax, heq]
    exact (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hab
  have hlow : max A.b (min (A.v F.gap.c) (extVisibilityReplace (A.v F.gap.r.1) K K)) ≤ A.u d :=
    hA.low le_rfl hm d hd
  have htop := hσ.mono ((le_max_right _ _).trans hlow)
  rw [hσ.mono.map_min, hσ.comm_gTop _ le_rfl, hc, hr, extVisibilityReplace_top, min_self] at htop
  exact top_le_iff.mp htop

end Family

