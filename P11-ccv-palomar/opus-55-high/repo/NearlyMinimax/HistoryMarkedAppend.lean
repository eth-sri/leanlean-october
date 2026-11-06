module

public import NearlyMinimax.HistoryCoordinateTransport
public import NearlyMinimax.HistoryMaximalDelete
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Actual independent mark insertion and canonical append coordinates
-/

𝚯
𝚨

𝚲

𝗇 𝔄 𝘼
𝗇 𝔓 𝖴
𝗇 𝔅 HistoryShape 𝔓
𝗇 𝔇 g.out ++ [j]
𝗇 𝔈 𝙁
𝗇 𝔉 𝗡₁ g
𝗇 𝔛 WordHeapPiece 𝔇 dependent
𝗇 𝔜 (𝔉).out
𝗇 𝔔 𝔛 ≃o WordHeapPiece 𝔜 dependent
omit [Fintype J] [LinearOrder J] in
/-- The canonical appended word carries the same actual labelled dependency heap. -/
theorem historyCanonicalAppendHeapIso_exists (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    ∃ e : 𝔔,
      𝚠₁ := by
  have hmk : (Quotient.mk _ 𝔇 : 𝔅) =
      𝔉 := by
    exact congrArg 𝗡₁ $ Quotient.out_eq g
  have hr : Relation.EqvGen (IndependentHistoryExchange 𝔓)
      𝔇 𝔜 :=
    Quotient.exact $ hmk.trans (Quotient.out_eq _).symm
  exact historyShapeRelation_heapIso dependent hsymm hr

𝗃 𝔘 ἀ dependent hsymm j g
/-- Choose once an actual representative coordinate transport, not a law or score bound. -/
def historyCanonicalAppendHeapIso (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    𝔔 :=
  (𝔘 historyCanonicalAppendHeapIso_exists).choose

𝗇 𝔗 𝔘 historyCanonicalAppendHeapIso
omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendHeapIso_label (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) (x : 𝔛) :
    wordHeapLabel (𝔗 x) = wordHeapLabel x :=
  (𝔘 historyCanonicalAppendHeapIso_exists).choose_spec x

𝗇 𝔚 𝗉
𝗃 𝔞 Fin ἀ → E
/-- Insert one genuinely independent mark at the last finite coordinate. -/
def historyFiniteMarkAppendEquiv (n : ℕ) [MeasurableSpace E] :
    E × 𝔞 n ≃ᵐ 𝔞 𝔚 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 𝔚 => E) $ Fin.last n ).symm

𝗇 𝔊 fun _ => π
𝗇 𝔙 π.prod $ Measure.pi 𝔊
theorem historyFiniteMarkAppendEquiv_preserving (n : ℕ) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n )
      𝔙 $ Measure.pi 𝔊 :=
  (measurePreserving_piFinSuccAbove 𝔊 $ Fin.last n ).symm _

𝗇 𝔍 𝗠₁
𝗇 𝔖 Fin $ historyShapeLength dependent 𝔉
/-- The real position bijection from old coordinates plus a fresh last coordinate to the canonical append. -/
def historyCanonicalAppendCoordinates (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    Fin (𝔍 + 1) ≃ 𝔖 :=
  (finCongr $ by rw [historyShapeLength_out]; simp ).trans
    $ (historyHeapCoordinateEquiv 𝔗).trans
      $ finCongr (historyShapeLength_out dependent 𝔉).symm

𝗇 𝔎 𝔘 historyCanonicalAppendCoordinates
𝗇 𝔐 𝚓
/-- Actual independent insertion followed by the actual canonical heap-coordinate permutation. -/
def historyCanonicalMarkAppendEquiv (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) [MeasurableSpace E] :
    E × 𝔞 𝔍 ≃ᵐ
      (𝔖 → E) :=
  (historyFiniteMarkAppendEquiv 𝔍).trans
    $ MeasurableEquiv.piCongrLeft 𝔐 𝔎

/-- The actual canonical append adds precisely one independent pi mark. -/
theorem historyCanonicalMarkAppendEquiv_preserving (dependent : 𝔈)
    (hsymm : 𝔄)
    j (g : 𝔅) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving 𝔘 historyCanonicalMarkAppendEquiv
      𝔙
      $ Measure.pi 𝔊 :=
  (measurePreserving_piCongrLeft 𝔊 𝔎).comp
    $ historyFiniteMarkAppendEquiv_preserving _ π

𝗇 𝔑 wordHeapAppendedPiece g.out dependent j
/-- The actual maximal piece corresponding to the freshly appended update. -/
def historyCanonicalAppendedPiece (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    WordHeapPiece 𝔜 dependent :=
  𝔗 𝔑

𝗇 𝔒 𝔘 historyCanonicalAppendedPiece
omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendedPiece_maximal (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    𝔒 ∈ historyMaximalPieces Finset.univ := by
  let e := 𝔗
  have hx : e 𝔑 ∈ historyMaximalPieces
      ((Finset.univ : Finset 𝔛).map e.toEquiv.toEmbedding) := by
    rw [historyMaximalPieces_orderIso_map]
    exact Finset.mem_map.2 ⟨_, wordHeapAppendedPiece_maximal g.out dependent j, rfl⟩
  rw [Finset.map_univ_equiv e.toEquiv] at hx
  exact hx

omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyCanonicalAppendedPiece_label (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    wordHeapLabel 𝔒 = j :=
  (𝔘 historyCanonicalAppendHeapIso_label _).trans
    $ wordHeapAppendedPiece_label g.out dependent j

/-- The freshly added coordinate in the canonical marked-history fiber. -/
def historyCanonicalFreshCoordinate (dependent : 𝔈)
    (hsymm : 𝔄)
    (j : J) (g : 𝔅) :
    𝔖 :=
  Fin.cast (historyShapeLength_out dependent 𝔉).symm
    (𝔒).position

theorem historyCanonicalAppendCoordinates_last dependent
    hsymm
    (j : J) g :
    𝔘 historyCanonicalAppendCoordinates (Fin.last 𝔍) =
      𝔘 historyCanonicalFreshCoordinate := by
  let hlen : 𝔍 + 1 = (𝔇).length := by
    rw [historyShapeLength_out]; simp
  have hl : (finCongr hlen) (Fin.last 𝔍) =
      (𝔑).position := by
    apply Fin.ext
    exact historyShapeLength_out dependent g
  unfold historyCanonicalAppendCoordinates historyCanonicalFreshCoordinate historyCanonicalAppendedPiece
  simp_all

𝗇 𝔏 𝘨₂
@[simp] theorem historyFiniteMarkAppendEquiv_last (n : ℕ) [MeasurableSpace E]
    (fresh : E) marks :
    historyFiniteMarkAppendEquiv n 𝔏 (Fin.last n) = fresh := by
  have hh := congrArg Prod.fst
    $ (MeasurableEquiv.piFinSuccAbove 𝔐 $ Fin.last n ).apply_symm_apply 𝔏
  exact hh

/-- The canonical maximal-piece mark is exactly the independent fresh mark, including after reordering. -/
@[simp] theorem historyCanonicalMarkAppendEquiv_fresh (dependent : 𝔈)
    (hsymm : 𝔄)
    j (g : 𝔅) [MeasurableSpace E]
    (fresh : E) marks :
    𝔘 historyCanonicalMarkAppendEquiv 𝔏
      𝔘 historyCanonicalFreshCoordinate = fresh := by
  rw [← historyCanonicalAppendCoordinates_last]
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    𝔎
    (β := 𝔐) (historyFiniteMarkAppendEquiv _ 𝔏) $ Fin.last _
  aesop
