module

public import OverfullWork.CleanedSourceVAL

@[expose] public section


/-! # Deletions and degree-order swaps for joint cut normalization

The swap uses only weak VAL along the current independent complement.
The strict objective is the actual sum of its vertex degrees.
-/
namespace OverfullWork.JointCutNormalizationTools
open SimpleGraph Finset OddCutDeficit FixedCoreBudgetTransport
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem independent_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y:Set V))
    (hPair : ∀u∈Y,∀v∈Y,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hWeak : ∀u∈Y,∀v,G.Adj u v → G.maxDegree+2≤G.degree u+G.degree v)
    (y x : V) (hy : y∈Y) (_hx : x∉Y) (hInv : G.degree x<G.degree y) :
    G.IsIndepSet (↑(insert x (Y.erase y)):Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab hAdj
  rcases mem_insert.mp ha with he|ha
  · subst a
    rcases mem_insert.mp hb with he|hb
    · exact hab he.symm
    · have hLight:=hPair y hy b (mem_erase.mp hb).2 (mem_erase.mp hb).1.symm
      have hVal:=hWeak b (mem_erase.mp hb).2 x hAdj.symm
      omega
  · rcases mem_insert.mp hb with he|hb
    · subst b
      have hLight:=hPair y hy a (mem_erase.mp ha).2 (mem_erase.mp ha).1.symm
      have hVal:=hWeak a (mem_erase.mp ha).2 x hAdj
      omega
    · exact hInd (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab hAdj

theorem swap_card_and_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (y x : V) (hy : y∈Y) (hx : x∉Y) (hInv : G.degree x<G.degree y) :
    (insert x (Y.erase y)).card=Y.card ∧
      (∑v∈insert x (Y.erase y),G.degree v)<∑v∈Y,G.degree v := by
  have hxE:x∉Y.erase y:=fun hh=>hx (mem_erase.mp hh).2
  have hCard:(insert x (Y.erase y)).card=Y.card:=by
    rw [card_insert_of_notMem hxE,card_erase_of_mem hy]
    have hp:0<Y.card:=card_pos.mpr ⟨y,hy⟩
    omega
  have hOld:=sum_erase_add Y (fun v=>G.degree v) hy
  have hNew:=sum_insert hxE (f:=fun v=>G.degree v)
  exact ⟨hCard,by omega⟩

theorem budget_mono_of_equal_card_and_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y Z : Finset V) (hCard : Z.card=Y.card)
    (hSum : (∑v∈Z,G.degree v)≤∑v∈Y,G.degree v) :
    deficitMass G G.maxDegree Zᶜ+(∑v∈Z,G.degree v)≤
      deficitMass G G.maxDegree Yᶜ+(∑v∈Y,G.degree v) := by
  have hCY:=(card_add_card_compl Y)
  have hCZ:=(card_add_card_compl Z)
  have hCore:Zᶜ.card=Yᶜ.card:=by omega
  have hOld:=DegreeOrderedIndependentCut.budget_add_total_degree G Yᶜ
  have hNew:=DegreeOrderedIndependentCut.budget_add_total_degree G Zᶜ
  simp only [compl_compl] at hOld hNew
  rw [hCore] at hNew
  omega

theorem degree_sum_strictly_decreases_on_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (w v : V) (hw : w∈Y) (hEdge : G.Adj w v) :
    (∑u∈Y,(G.deleteEdges {s(w,v)}).degree u)<∑u∈Y,G.degree u := by
  classical
  let H:=G.deleteEdges {s(w,v)}
  have hLe:H≤G:=deleteEdges_le _
  have hDeg:∀u,H.degree u≤G.degree u:=fun u=>H.degree_le_of_le hLe
  have hSub:H.neighborFinset w⊆G.neighborFinset w:=by
    intro u hu
    exact (mem_neighborFinset G w u).mpr (hLe ((mem_neighborFinset H w u).mp hu))
  have hStrict:H.degree w<G.degree w:=by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    apply card_lt_card
    apply (ssubset_iff_of_subset hSub).mpr
    refine ⟨v,(mem_neighborFinset G w v).mpr hEdge,?_⟩
    intro hv
    have hAdj: H.Adj w v:=(mem_neighborFinset H w v).mp hv
    exact (deleteEdges_adj.mp hAdj).2 (by simp)
  exact sum_lt_sum (fun u _=>hDeg u) ⟨w,hw,hStrict⟩

end OverfullWork.JointCutNormalizationTools
