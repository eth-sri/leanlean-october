module
public import Glennie.Compact.NativeFlatBlock0
public import Glennie.Compact.NativeFlatBlock1
public import Glennie.Compact.NativeFlatBlock2
public import Glennie.Compact.NativeFlatBlock3
public import Glennie.Compact.NativeFlatBlock4
@[expose] public section
namespace Glennie.Compact.NativeFlatRank20
open Glennie.Compact.FlatBase Glennie.Compact.FlowFamily Glennie.Compact.Rank20Certificate
section
theorem jacobianEntry_flatBase_all (r n : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r n = JQ r n := by
  have cols (b : Fin 5) (i : Fin 4) :
      jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r ⟨4*b.val+i.val, by omega⟩ =
        JQ r ⟨4*b.val+i.val, by omega⟩ := by
    fin_cases b
    · exact NativeFlatBlock0.columns r i
    · exact NativeFlatBlock1.columns r i
    · exact NativeFlatBlock2.columns r i
    · exact NativeFlatBlock3.columns r i
    · exact NativeFlatBlock4.columns r i
  have h := cols ⟨n.val / 4, by omega⟩ ⟨n.val % 4, by omega⟩
  simpa only [show 4*(n.val / 4)+n.val%4 = n.val by omega] using h
end
end Glennie.Compact.NativeFlatRank20
