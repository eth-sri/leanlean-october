module

public import NearlyMinimax.HistoryHeapFold
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact raw-state compatibility of actual independent marked canonical
append, derived from the genuine heap-coordinate transport. -/
𝚯
𝚨
𝚰
𝚩
𝚲

𝗇 𝔄 HistoryShape 𝖴
𝗇 𝔈 𝙁
𝗇 𝔉 𝗠₁
𝗇 𝔓 𝚈₂
𝗇 𝔛 Fin 𝔉 → E
def historyCanonicalWordMarks (dependent : 𝔈)
    (g : 𝔄)
    (marks : 𝔛) : Fin g.out.length → E :=
  fun i => marks $ Fin.cast 𝔓 i

𝗇 𝔇 fun i => (𝘤₂ i, marks i)
𝗇 𝔠 historyCanonicalWordMarks dependent g marks
𝗇 𝔊 List.ofFn fun i => (g.out.get i, 𝔠 i)
𝗇 𝔎 J → E → X → X
𝗇 𝔒 historyWordMarkedState update initial g.out 𝔠
𝗇 𝔗 historyMarkedRawState dependent update initial
theorem historyMarkedRawState_eq_wordMarkedState dependent
    (update : 𝔎) initial
    g
    marks :
    𝔗 𝗬 =
      𝔒 := by
  have hm : List.ofFn 𝔇 =
      (𝘞₁).map
        𝔇 := by
    aesop
  have ht : List.ofFn 𝔇 =
      𝔊 := by
    apply List.ext_getElem $ by simp ; exact historyShapeLength_out dependent g
    intro i hi hi'
    simp only [List.getElem_ofFn]
    congr 1
  have hh := congrArg (fun l =>
    l.foldl (fun state p => update p.1 p.2 state) initial) $ hm.symm.trans ht
  rw [List.foldl_map] at hh
  exact hh

𝗇 𝔅 g.out ++ [j]
𝗇 𝔏 𝘨₂
def historyAppendWordMarks (dependent : 𝔈)
    (j : J) (g : 𝔄)
    [MeasurableSpace E] (fresh : E)
    (marks : 𝔛) : Fin (𝔅).length → E :=
  fun i => historyFiniteMarkAppendEquiv 𝔉 𝔏
    $ Fin.cast (by rw [historyShapeLength_out]; simp) i

𝗃 𝔡 ἀ dependent j g fresh marks
𝗇 𝔖 𝔡 historyAppendWordMarks
𝗇 𝔍 𝔖
𝗇 𝔐 𝘼
𝗃 𝔘 ἀ dependent hsymm j g
𝗇 𝔑 𝔘 historyCanonicalAppendHeapIso
𝗇 𝔔 𝗡₁ g
𝗇 𝔜 Fin.cast hlen.symm x.position
theorem historyCanonicalAppend_word_marks (dependent : 𝔈)
    (hsymm : 𝔐)
    j (g : 𝔄)
    [MeasurableSpace E] (fresh : E)
    marks :
    historyCanonicalWordMarks dependent 𝔔
      (𝔘 historyCanonicalMarkAppendEquiv 𝔏) =
      historyHeapMarkEquiv 𝔑
        𝔍 := by
  let e := 𝔑
  let hlen : 𝔉 + 1 = (𝔅).length := by
    rw [historyShapeLength_out]; simp
  have hc x :
      𝔘 historyCanonicalAppendCoordinates 𝔜 =
      Fin.cast (historyShapeLength_out dependent 𝔔).symm 𝚟₁ := by
    rfl
  have hm (x : WordHeapPiece 𝔅 dependent) :=
    MeasurableEquiv.piCongrLeft_apply_apply
      𝔘 historyCanonicalAppendCoordinates
      (β := 𝚓) (historyFiniteMarkAppendEquiv _ 𝔏) 𝔜
  ext i
  let x := e.symm ⟨i⟩
  have hx : 𝚟₁ = i := by simp only [x, e.apply_symm_apply]
  have hh := hm x
  rw [hc x, hx] at hh
  have ht := historyHeapMarkEquiv_position e 𝔍 x
  rw [hx] at ht
  exact hh.trans ht.symm

𝗇 𝔚 (historyPrefixHeapEmbedding g.out dependent j x).position
@[simp] theorem historyAppendWordMarks_old (dependent : 𝔈)
    j (g : 𝔄)
    [MeasurableSpace E] (fresh : E)
    marks x :
    𝔖
      𝔚 =
      𝔠 x.position := by
  unfold historyAppendWordMarks historyCanonicalWordMarks
  have he : Fin.cast (by rw [historyShapeLength_out]; simp)
      𝔚 =
      (Fin.cast 𝔓 x.position).castSucc := by
    rfl
  simp_all

𝗇 𝔞 (wordHeapAppendedPiece g.out dependent j).position
@[simp] theorem historyAppendWordMarks_fresh (dependent : 𝔈)
    j (g : 𝔄)
    [MeasurableSpace E] (fresh : E)
    marks :
    𝔖 𝔞 = fresh := by
  unfold historyAppendWordMarks
  have he : Fin.cast (by rw [historyShapeLength_out]; simp)
      𝔞 = Fin.last 𝔉 := by
    apply Fin.ext
    exact 𝔓
  simp_all

𝗇 𝔙 ⟨i, hiold⟩
𝗇 𝔟 (𝔅).get
theorem historyAppendWordMarkedState (dependent : 𝔈)
    j (g : 𝔄)
    [MeasurableSpace E] fresh
    (marks : 𝔛)
    (update : 𝔎) initial :
    historyWordMarkedState update initial 𝔅
      𝔍 =
      update j fresh 𝔒 := by
  have ht : (List.ofFn fun i =>
      (𝔟 i, 𝔖 i) ) =
      𝔊 ++ [(j, fresh)] := by
    apply List.ext_getElem 𝖢₄
    intro i hi hi'
    by_cases hiold : i < g.out.length
    · rw [List.getElem_append_left 𝖧₄ ]
      simp only [List.getElem_ofFn]
      have hg : 𝔟 ⟨i, 𝖤₄⟩ = g.out.get 𝔙 := by
        simp_all
      rw [hg]
      exact congrArg (fun a => (g.out.get 𝔙, a))
        $ 𝔡 historyAppendWordMarks_old ⟨𝔙⟩
    · have hieq : i = g.out.length := by
        grind
      subst i
      rw [List.getElem_append_right 𝖢₄ ]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_ofFn]
      have hg : 𝔟 ⟨g.out.length, 𝖢₄⟩ = j := by
        simp
      rw [hg]
      exact congrArg (fun a => (j, a)) 𝔡 historyAppendWordMarks_fresh
  unfold historyWordMarkedState historyWordState
  simp_all

/-- Actual canonical marked append applies exactly the fresh local update
once, even when the canonical representative reorders old occurrences. -/
theorem historyMarkedRawState_append (dependent : 𝔈)
    (hsymm : 𝔐)
    [MeasurableSpace E] (update : 𝔎)
    (hcomm : 𝚙)
    initial j h fresh :
    𝔗
      (𝙯₁ 𝘥₂) =
      update j fresh (𝔗 h) := by
  obtain ⟨g, marks⟩ := h
  change 𝔗
      ⟨𝔔, 𝔘 historyCanonicalMarkAppendEquiv 𝔏⟩ = _
  rw [historyMarkedRawState_eq_wordMarkedState,
    historyCanonicalAppend_word_marks,
    historyHeapMarkEquiv_state dependent hsymm update hcomm
      𝔑
      𝔘 historyCanonicalAppendHeapIso_label,
    historyAppendWordMarkedState, historyMarkedRawState_eq_wordMarkedState]
