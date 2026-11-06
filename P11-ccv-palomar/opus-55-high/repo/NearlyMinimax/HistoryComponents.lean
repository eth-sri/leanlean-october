module

public import NearlyMinimax.HistoryUpperSets
public import NearlyMinimax.HistoryGas
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Connected upper-subset components

Connectivity is the equivalence closure of comparability edges inside the
finite subset. This is a concrete finite construction. Components of an upper
set are upper, pairwise disjoint and incomparable, and their order weights
multiply. The separate cover-chain bridge identifies these with components of
the heap's bounded-degree cover graph.
-/


𝛚

def historyComparableEdge (U : Finset α) (a b : α) : Prop :=
  a ∈ U ∧ b ∈ U ∧ (a ≤ b ∨ b ≤ a)

def HistoryConnected (U : Finset α) (a b : α) : Prop :=
  Relation.EqvGen (historyComparableEdge U) a b

def historyComponent (U : Finset α) (a : α) : Finset α := by
  classical
  exact U.filter $ HistoryConnected U a

𝗇 𝔉 HistoryConnected U a b
𝗇 𝔎 historyComponent U a
omit [DecidableEq α] in
theorem mem_historyComponent {U : Finset α} {a b : α} :
    b ∈ 𝔎 ↔ b ∈ U ∧ 𝔉 := by
  classical
  exact Finset.mem_filter

omit [DecidableEq α] in
theorem historyComponent_subset (U : Finset α) (a : α) : 𝔎 ⊆ U :=
  fun _ h => (mem_historyComponent.1 h).1

omit [DecidableEq α] in
theorem self_mem_historyComponent {U : Finset α} {a : α} (ha : a ∈ U) :
    a ∈ 𝔎 := mem_historyComponent.2 ⟨ha, .refl _⟩

omit [DecidableEq α] in
theorem historyComponent_eq_of_connected {U : Finset α} {a b : α}
    (h : 𝔉) : 𝔎 = historyComponent U b := by
  ext x
  rw [mem_historyComponent, mem_historyComponent]
  constructor
  · rintro ⟨hx, hax⟩
    exact ⟨hx, .trans _ _ _ (.symm _ _ h) hax⟩
  · rintro ⟨hx, hbx⟩
    exact ⟨hx, .trans _ _ _ h hbx⟩

𝗃 𝔓 (mem_historyComponent.1 ἀ).2
theorem historyComponent_eq_of_inter {U } {a b : α}
    (h : (𝔎 ∩ historyComponent U b).Nonempty) :
    𝔎 = historyComponent U b := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.1 hx
  apply historyComponent_eq_of_connected
  exact .trans _ _ _ 𝔓 hxa $ .symm _ _ 𝔓 hxb

𝗇 𝔊 historyComponent U r
omit [DecidableEq α] in
omit [DecidableEq α] in
theorem historyComponent_connected_lift {U : Finset α} {r a b : α}
    (h : 𝔉) :
    HistoryConnected U r a → HistoryConnected 𝔊 a b := by
  induction h with
  | rel a b hab =>
    intro hra
    apply Relation.EqvGen.rel
    exact ⟨mem_historyComponent.2 ⟨hab.1, hra⟩,
      mem_historyComponent.2 ⟨hab.2.1, .trans _ _ _ hra $ .rel _ _ hab ⟩, hab.2.2⟩
  | refl a => intro _; exact .refl _
  | symm a b hab ih =>
    intro hrb
    exact .symm _ _ $ ih $ .trans _ _ _ hrb $ .symm _ _ hab
  | trans a b c hab hbc ihab ihbc =>
    intro hra
    exact .trans _ _ _ (ihab hra) $ ihbc $ .trans _ _ _ hra hab

def IsConnectedHistorySubset (U : Finset α) : Prop :=
  U.Nonempty ∧ ∀ a ∈ U, ∀ b ∈ U, 𝔉

omit [DecidableEq α] in
theorem historyComponent_connected {U : Finset α} {r : α} (hr : r ∈ U) :
    IsConnectedHistorySubset 𝔊 := by
  refine ⟨⟨r, self_mem_historyComponent hr⟩, ?_⟩
  intro a ha b hb
  have hra := 𝔓 ha
  have hrb := 𝔓 hb
  exact historyComponent_connected_lift (.trans _ _ _ (.symm _ _ hra) hrb) hra

𝗇 𝔔 IsHistoryUpper S U
omit [DecidableEq α] in
theorem historyComponent_upper {S U : Finset α} (hU : 𝔔) (r : α) :
    IsHistoryUpper S 𝔊 := by
  refine ⟨(historyComponent_subset U r).trans hU.1, ?_⟩
  intro a ha b hb hab
  obtain ⟨haU, hra⟩ := mem_historyComponent.1 ha
  have hbU := hU.2 a haU b hb hab
  exact mem_historyComponent.2 ⟨hbU, .trans _ _ _ hra $ .rel _ _ ⟨haU, hbU, Or.inl hab⟩ ⟩

𝗇 𝔍 Finset $ Finset α
def historyComponents (U : Finset α) : 𝔍 := U.image $ historyComponent U

𝗇 𝔏 P ∈ historyComponents U
section

variable {U P : Finset α}

theorem mem_historyComponents :
    𝔏 ↔ ∃ r ∈ U, 𝔊 = P := Finset.mem_image

theorem historyComponents_subset (hP : 𝔏) : P ⊆ U := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_subset U r

theorem historyComponents_connected (hP : 𝔏) :
    IsConnectedHistorySubset P := by
  obtain ⟨r, hr, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_connected hr

end

theorem historyComponents_upper {S U P : Finset α} (hU : 𝔔)
    (hP : 𝔏) : IsHistoryUpper S P := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_upper hU r

𝗇 𝔗 (historyComponents U).biUnion id
𝗇 𝔞 P ≠ Q → Disjoint P Q
section

variable (U : Finset α)

theorem historyComponents_pairwise_disjoint :
    ∀ P ∈ historyComponents U, ∀ Q ∈ historyComponents U, 𝔞 := by
  intro P hP Q hQ hpq
  obtain ⟨p, _, rfl⟩ := mem_historyComponents.1 hP
  obtain ⟨q, _, rfl⟩ := mem_historyComponents.1 hQ
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun hi => hpq $ historyComponent_eq_of_inter hi

theorem historyComponents_biUnion : 𝔗 = U := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact historyComponents_subset hP hx
  · intro hx
    exact ⟨historyComponent U x, mem_historyComponents.2 ⟨x, hx, rfl⟩, self_mem_historyComponent hx⟩

end

𝗇 𝔘 ∀ P ∈ F, IsHistoryUpper S P
theorem historyUpper_biUnion {S } {F : 𝔍}
    (hF : 𝔘) : IsHistoryUpper S $ F.biUnion id := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact (hF P hP).1 hxP
  · intro x hx y hy hxy
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨P, hP, (hF P hP).2 x hxP y hy hxy⟩

𝗇 𝔅 ∀ P ∈ F, ∀ Q ∈ F, 𝔞
𝗃 𝔠 ἀ weight ρ t
𝗇 𝔐 𝔠 historyComponentWeight
theorem historyComponentWeight_biUnion weight ρ t
    {S : Finset α} F (hF : 𝔘)
    (hdis : 𝔅) :
    𝔐 (F.biUnion id) = ∏ P ∈ F, 𝔐 P := by
  induction F using Finset.induction_on with
  | empty => simp [historyComponentWeight]
  | @insert P F hPF ih =>
    have hFin := fun Q hQ => hF Q $ Finset.mem_insert_of_mem hQ
    have hFinDis :=
      fun Q hQ R hR hQR => hdis Q (Finset.mem_insert_of_mem hQ) R (Finset.mem_insert_of_mem hR) hQR
    have hPdis : Disjoint P $ F.biUnion id := by
      apply Finset.disjoint_left.2
      intro x hxP hxF
      obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
      exact Finset.disjoint_left.1 (hdis P (Finset.mem_insert_self ..) Q
        (Finset.mem_insert_of_mem hQ) fun heq => hPF $ heq ▸ hQ ) hxP hxQ
    have hinc := historyUpper_disjoint_incomparable (hF P $ Finset.mem_insert_self .. )
      (historyUpper_biUnion hFin) hPdis
    rw [Finset.biUnion_insert, id_eq, 𝔠 historyComponentWeight_union hinc,
      Finset.prod_insert hPF, ih hFin hFinDis]

𝗇 𝔚 historyComponents_upper hU hP
/-- The actual weight of an upper set is the product of its connected weights. -/
theorem historyComponentWeight_eq_component_prod weight ρ t
    {S U : Finset α} (hU : 𝔔) :
    𝔐 U =
      ∏ P ∈ historyComponents U, 𝔐 P := by
  calc
    _ = 𝔐 𝔗 := by
      rw [historyComponents_biUnion]
    𝘿 := 𝔠 historyComponentWeight_biUnion (historyComponents U)
      (fun _ hP => 𝔚) $ historyComponents_pairwise_disjoint U

def historyUpperPolymers (S : Finset α) : 𝔍 := by
  classical
  exact (historyUpperSets S).filter IsConnectedHistorySubset

omit [DecidableEq α] in
theorem mem_historyUpperPolymers {S P : Finset α} :
    P ∈ historyUpperPolymers S ↔ IsHistoryUpper S P ∧ IsConnectedHistorySubset P := by
  classical
  simp only [historyUpperPolymers, Finset.mem_filter, mem_historyUpperSets]

theorem historyUpperPolymer_support_nonempty {S P : Finset α} (hP : P ∈ historyUpperPolymers S) :
    (historyMaximalPieces P).Nonempty :=
  historyUpper_nonempty_maximal (mem_historyUpperPolymers.1 hP).1 (mem_historyUpperPolymers.1 hP).2.1

𝗃 𝔑 ἀ (historyUpperPolymers S) historyMaximalPieces
theorem historyComponents_mem_gas {S U : Finset α} (hU : 𝔔) :
    historyComponents U ∈ 𝔑 historyGasFamilies (historyMaximalPieces U) := by
  rw [mem_historyGasFamilies]
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    exact mem_historyUpperPolymers.2 ⟨𝔚, historyComponents_connected hP⟩
  · intro P hP Q hQ hpq
    exact (historyUpper_disjoint_iff 𝔚
      $ historyComponents_upper hU hQ ).1 $ historyComponents_pairwise_disjoint U P hP Q hQ hpq
  · intro P hP
    obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
    exact historyUpper_maximal_subset $ historyComponent_upper ⟨Finset.Subset.refl _,
      fun _ _ _ hy _ => hy⟩ r

omit [DecidableEq α] in
theorem historyConnected_mono {P U : Finset α} (hsub : P ⊆ U) {a b : α}
    (h : HistoryConnected P a b) : 𝔉 :=
  Relation.EqvGen.mono (r := historyComparableEdge P) (p := historyComparableEdge U)
    (fun _ _ hab => ⟨hsub hab.1, hsub hab.2.1, hab.2.2⟩) a b h

𝗇 𝔛 P ∪ Q
theorem historyConnected_preserves_incomparable_part {P Q }
    (hinc : IncomparableHistoryParts P Q) {a b : α} (h : HistoryConnected 𝔛 a b) :
    a ∈ P ↔ b ∈ P := by
  induction h with
  | rel a b hab =>
    constructor
    · intro haP
      rcases Finset.mem_union.1 hab.2.1 with hbP | hbQ
      · exact hbP
      · exact hab.2.2.elim
          (fun hab => ((hinc a haP b hbQ).1 hab).elim)
           fun hba => ((hinc a haP b hbQ).2 hba).elim
    · intro hbP
      rcases Finset.mem_union.1 hab.1 with haP | haQ
      · exact haP
      · exact hab.2.2.elim
          (fun hab => ((hinc b hbP a haQ).2 hab).elim)
           fun hba => ((hinc b hbP a haQ).1 hba).elim
  | refl a => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem historyComponent_incomparable_union {P Q }
    (hinc : IncomparableHistoryParts P Q) (hP : IsConnectedHistorySubset P) {p : α} (hp : p ∈ P) :
    historyComponent 𝔛 p = P := by
  ext x
  constructor
  · intro hx
    exact (historyConnected_preserves_incomparable_part hinc 𝔓 hx).1 hp
  · intro hx
    exact mem_historyComponent.2 ⟨Finset.mem_union_left _ hx,
      historyConnected_mono Finset.subset_union_left $ hP.2 p hp x hx ⟩

𝗇 𝔄 F ∈ 𝔑 historyGasFamilies R
𝗃 𝔡 (mem_historyGasFamilies.1 hF).1 ἀ
𝗇 𝔇 mem_historyUpperPolymers.1 𝔡 hP
section

variable {S R : Finset α}
    {F }
    (hF : 𝔄)

include hF

theorem historyGasFamily_piece_disjoint :
    𝔅 := by
  obtain ⟨hFP, hc, _⟩ := mem_historyGasFamilies.1 hF
  intro P hP Q hQ hpq
  exact (historyUpper_disjoint_iff (mem_historyUpperPolymers.1 $ hFP hP ).1
    (mem_historyUpperPolymers.1 $ hFP hQ ).1).2 $ hc P hP Q hQ hpq

theorem historyGasFamily_biUnion_upper :
    IsHistoryUpper S $ F.biUnion id := historyUpper_biUnion fun _ hP => (𝔇).1

end

𝗇 𝔙 (F.erase P).biUnion id
theorem historyGasFamily_component_at {S R } {F }
    (hF : 𝔄)
    {P } (hP : P ∈ F) {p : α} (hp : p ∈ P) :
    historyComponent (F.biUnion id) p = P := by
  have hupper : ∀ Q ∈ F, IsHistoryUpper S Q :=
    fun _ hQ => (mem_historyUpperPolymers.1 𝔡 hQ).1
  have hdis : Disjoint P 𝔙 := by
    apply Finset.disjoint_left.2
    intro x hxP hxF
    obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
    obtain ⟨hQP, hQF⟩ := Finset.mem_erase.1 hQ
    exact Finset.disjoint_left.1 (historyGasFamily_piece_disjoint hF P hP Q hQF hQP.symm) hxP hxQ
  have hinc := historyUpper_disjoint_incomparable (hupper P hP)
    (historyUpper_biUnion fun Q hQ => hupper Q $ Finset.mem_of_mem_erase hQ ) hdis
  have hUnion : F.biUnion id = P ∪ 𝔙 := by
    grind
  rw [hUnion]
  exact historyComponent_incomparable_union hinc
    (𝔇).2 hp

𝗃 𝔢 Finset.mem_biUnion.2 ⟨P, hP, ἀ⟩
/-- Compatible connected upper families are exactly the components of their union. -/
theorem historyGasFamily_components_biUnion {S R : Finset α} {F }
    (hF : 𝔄) :
    historyComponents (F.biUnion id) = F := by
  ext P
  constructor
  · intro hP
    obtain ⟨p, hp, rfl⟩ := mem_historyComponents.1 hP
    obtain ⟨Q, hQ, hpQ⟩ := Finset.mem_biUnion.1 hp
    rw [historyGasFamily_component_at hF hQ hpQ]
    exact hQ
  · intro hP
    obtain ⟨p, hp⟩ := (𝔇).2.1
    exact mem_historyComponents.2 ⟨p, 𝔢 hp,
      historyGasFamily_component_at hF hP hp⟩

def historyRestrictedUpperSets (S R : Finset α) : 𝔍 := by
  classical
  exact (historyUpperSets S).filter fun U => historyMaximalPieces U ⊆ R

𝗇 𝔜 historyRestrictedUpperSets S R
section

variable {S R U : Finset α}

theorem mem_historyRestrictedUpperSets :
    U ∈ 𝔜 ↔ 𝔔 ∧ historyMaximalPieces U ⊆ R := by
  classical
  simp only [historyRestrictedUpperSets, Finset.mem_filter, mem_historyUpperSets]

theorem historyRestrictedUpperSets_components_gas (hU : U ∈ 𝔜) :
    historyComponents U ∈ 𝔑 historyGasFamilies R := by
  obtain ⟨hupper, hmax⟩ := mem_historyRestrictedUpperSets.1 hU
  obtain ⟨hcP, hcompat, hcSupport⟩ := mem_historyGasFamilies.1 $ historyComponents_mem_gas hupper
  exact mem_historyGasFamilies.2 ⟨hcP, hcompat, fun P hP => (hcSupport P hP).trans hmax⟩

end

theorem historyGasFamily_biUnion_restricted {S R : Finset α} {F }
    (hF : 𝔄) :
    F.biUnion id ∈ 𝔜 := by
  apply mem_historyRestrictedUpperSets.2
  refine ⟨historyGasFamily_biUnion_upper hF, ?_⟩
  intro x hx
  obtain ⟨hxU, hm⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hxU
  have hxmaxP := mem_historyMaximalPieces.2 ⟨hxP, fun y hy hxy =>
    hm y 𝔢 hy hxy⟩
  exact (mem_historyGasFamilies.1 hF).2.2 P hP hxmaxP

def historyRestrictedUpperDensity (weight : 𝘬) (ρ t : ℝ) (S R : Finset α) : ℝ :=
  ∑ U ∈ 𝔜, 𝔐 U

𝗇 𝔈 𝔠 historyRestrictedUpperDensity S R
/-- The actual restricted upper-set density equals the concrete finite component gas. -/
theorem historyRestrictedUpperDensity_eq_gas weight ρ t (S R : Finset α) :
    𝔈 =
      𝔑 historyGasPartition
        𝔐 R := by
  apply Finset.sum_bij fun U _ => historyComponents U
  · intro U hU
    exact historyRestrictedUpperSets_components_gas hU
  · intro U hU V hV hUV
    simpa only [historyComponents_biUnion] using congrArg (fun F => F.biUnion id) hUV
  · intro F hF
    exact ⟨F.biUnion id, historyGasFamily_biUnion_restricted hF, historyGasFamily_components_biUnion hF⟩
  · intro U hU
    exact 𝔠 historyComponentWeight_eq_component_prod (mem_historyRestrictedUpperSets.1 hU).1

theorem historyRestrictedUpperSets_full (S : Finset α) :
    historyRestrictedUpperSets S (historyMaximalPieces S) = historyUpperSets S := by
  ext U
  rw [mem_historyRestrictedUpperSets, mem_historyUpperSets]
  exact ⟨fun h => h.1, fun h => ⟨h, historyUpper_maximal_subset h⟩⟩

𝗇 𝔖 𝔠 historyRestrictedUpperDensity S $ R.erase x
/-- Positivity of the actual upper-set density follows from its explicit connected-set activity sum. -/
theorem historyRestrictedUpperDensity_positive weight ρ t (S : Finset α)
    (hactivity : ∀ R x, x ∈ R →
       ∑ P ∈ 𝔑 historyGasRows R x,
        |𝔐 P| * 2 ^ ((historyMaximalPieces P).card - 1) ≤ 𝙖) :
    ∀ R, 0 < 𝔈 ∧ ∀ x ∈ R,
      𝔖 / 2 ≤ 𝔈 ∧
      𝔈 ≤ 𝗞 * 𝔖 := by
  simp_rw [historyRestrictedUpperDensity_eq_gas]
  exact 𝔑 historyGasPartition_positive
    𝔐 (fun _ hP => historyUpperPolymer_support_nonempty hP) hactivity
