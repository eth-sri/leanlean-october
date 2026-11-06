module

public import NearlyMinimax.HistoryCanonicalDeletion
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-! Marked local updates have identical folded states along any two actual
linear extensions of one labelled dependency heap. -/
𝚰
𝚩

𝗇 𝔔 update y state
𝗇 𝔅 ∀ y ∈ before, ∀ state, update x 𝔔 = update y (update x state)
𝗇 𝔊 update x state
𝗇 𝔍 fun state y => 𝔔
𝗇 𝔎 fun s y => update y s
𝗇 𝔒 update x initial
theorem historyFold_move_to_front (update : ι → X → X)
    before after x
    (hcomm : 𝔅)
    initial :
    (before ++ x :: after).foldl 𝔍 initial =
      (before ++ after).foldl 𝔍 𝔒 := by
  have hfold : ∀ state, update x (before.foldl 𝔎 state) =
      before.foldl 𝔎 𝔊 := by
    induction before with
    | nil => intro state; rfl
    | cons y ys ih =>
      intro state
      simp
      rw [ih fun z hz => hcomm z $ List.mem_cons_of_mem y hz ]
      rw [hcomm y List.mem_cons_self]
  simp_all

𝗇 𝔄 fun x y => ¬ y ≤ x
𝗇 𝔐 fun state x => 𝔊
/-- Finite heap linear extensions preserve the actual marked update fold.
Only incomparable actions must commute. -/
theorem historyFold_linear_extension_invariant {ι X } [PartialOrder ι]
    (dependent : ι → ι → Prop) (update : ι → X → X)
    (hcomp : ∀ x y, dependent x y → 𝗪₂ ∨ y ≤ x)
    (hcomm : ∀ x y, ¬ dependent x y → ∀ state,
      update y 𝔊 = update x 𝔔)
    {l l' : List ι} (hperm : l.Perm l')
    (hl : l.Pairwise 𝔄)
    (hl' : l'.Pairwise 𝔄) initial :
    l.foldl 𝔐 initial =
      l'.foldl 𝔐 initial := by
  induction l' generalizing l initial with
  | nil =>
    have he := List.perm_nil.mp hperm
    subst l
    rfl
  | cons x xs ih =>
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp $ hperm.mem_iff.mpr List.mem_cons_self
    obtain ⟨hbefore, hafter, hcross⟩ := List.pairwise_append.mp hl
    have htailperm :=
      (List.perm_middle.symm.trans hperm).cons_inv
    have htail :=
      hl.sublist $ List.Sublist.append (List.Sublist.refl before) $ List.Sublist.cons x $ List.Sublist.refl after
    have hmove : 𝔅 := by
      intro y hy state
      have hymem : y ∈ xs := by
        grind
      have hyx := (List.pairwise_cons.mp hl').1 y hymem
      grind
    rw [historyFold_move_to_front update before after x hmove initial]
    exact ih htailperm htail hl'.of_cons 𝔒

𝗇 𝔇 List.ofFn fun i => (word.get i, marks i)
𝗇 𝔉 J → E → X → X
def historyWordMarkedState (update : 𝔉)
    (initial : X) (word : List J) (marks : Fin word.length → E) : X :=
  historyWordState (fun p : J × E => update p.1 p.2) initial
    𝔇

𝗇 𝔈 fun i => (⟨i⟩ : 𝗔₂)
𝗇 𝔏 update (wordHeapLabel x) (marks x.position) state
theorem historyWordMarkedState_eq_heapFold
    dependent (update : 𝔉)
    initial word marks :
    historyWordMarkedState update initial word marks =
      (List.ofFn 𝔈).foldl
        (fun state x => 𝔏) initial := by
  unfold historyWordMarkedState historyWordState
  have heq : 𝔇 =
      (List.ofFn 𝔈).map
         fun x => (wordHeapLabel x, marks x.position) := by
    aesop
  rw [heq, List.foldl_map]

𝗇 𝔑 ⟨i⟩
𝗇 𝔓 historyHeapMarkEquiv e marks
/-- Any actual labelled heap isomorphism transports all marks and the raw
folded state exactly. Representative invariance is a proved conclusion. -/
theorem historyHeapMarkEquiv_state [MeasurableSpace E]
    (dependent : 𝙁)
    (hsymm : 𝘆₁)
    (update : 𝔉)
    (hcomm : 𝚙)
    (e : 𝚀)
    (he : 𝚠₁)
    initial marks :
    historyWordMarkedState update initial v 𝔓 =
      historyWordMarkedState update initial u marks := by
  classical
  let l := List.ofFn fun i => (𝔑 : WordHeapPiece u dependent)
  let l' := List.ofFn fun i => e.symm 𝔑
  have hl'nd : l'.Nodup := List.nodup_ofFn.mpr fun _ _ h =>
    congrArg WordHeapPiece.position $ e.symm.injective h
  have hp := (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr fun _ _ h => congrArg WordHeapPiece.position h ) hl'nd).mpr (by
    intro x
    constructor
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨𝚟₁, by
        have hx : ⟨𝚟₁⟩ = e x := 𝖦₄
        rw [hx, e.symm_apply_apply]⟩
    grind)
  have hl : l.Pairwise 𝔄 := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    have hh := wordHeap_reachable_position_le hle
    grind
  have hl' : l'.Pairwise 𝔄 := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    simp only [l'] at hle
    have hh := wordHeap_reachable_position_le $ e.monotone hle
    simp at hh
    grind
  let action := fun (x : WordHeapPiece u dependent) state =>
    𝔏
  have hfold := historyFold_linear_extension_invariant
    (fun x y => dependent (wordHeapLabel x) $ wordHeapLabel y ) action
    (fun _ _ => wordHeap_dependent_comparable hsymm)
    (fun x y h state => hcomm _ _ h _ _ state) hp hl hl' initial
  rw [historyWordMarkedState_eq_heapFold dependent update initial u marks]
  rw [hfold]
  rw [historyWordMarkedState_eq_heapFold dependent update initial v 𝔓]
  have hmap : l' = (List.ofFn fun i => 𝔑 ).map e.symm := by
    aesop
  rw [hmap, List.foldl_map]
  congr 1
  funext state x
  have hlabel := he $ e.symm x
  have hmark := historyHeapMarkEquiv_position e marks $ e.symm x
  simp at hlabel hmark
  simp only [action, hlabel, hmark]
