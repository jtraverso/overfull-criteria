module

public import OverfullWork.PaperSmallCutGeometry

@[expose] public section


/-! # Claim 4.5: two omitted core vertices in a critical-source round

The nonstopping condition is the actual source degree inequality, not
an assumption that the matching residue has no overfull subset. We work
before cleanup and transfer proved bounds at unchanged maximum degree.
-/
namespace OverfullWork.PaperTwoCoreRoundPreservation
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency
open NormalizedAlmostStoppingRun LargeCentreMatchingStep PaperTopDegreeMatching
open PaperSmallCutGeometry PaperOneCoreRoundPreservation
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem critical_degree_two_no_common_neighbour (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (x w v : V) (hxD : G.degree x<G.maxDegree)
    (hwD : G.degree w<G.maxDegree) (hxw : x≠w) (hxTwo : G.degree x=2)
    (hxv : G.Adj x v) (hwv : G.Adj w v) : False := by
  have hNonmax:∀u∈({x,w}:Finset V),G.degree u<G.maxDegree:=by
    intro u hu
    rcases mem_insert.mp hu with he|hu
    · exact he ▸ hxD
    · exact mem_singleton.mp hu ▸ hwD
  have hCol:=CriticalIndependentPairMatching.strict_column_bound G hc {x,w} hNonmax hxv
  have hSub:({x,w}:Finset V)⊆(G.neighborFinset v).filter (fun u=>u∈({x,w}:Finset V)):=by
    intro u hu
    refine mem_filter.mpr ⟨?_,hu⟩
    rcases mem_insert.mp hu with he|hu
    · exact (mem_neighborFinset G v u).mpr (he ▸ hxv.symm)
    · exact (mem_neighborFinset G v u).mpr (mem_singleton.mp hu ▸ hwv.symm)
  have hCard:=card_le_card hSub
  rw [card_pair hxw] at hCard
  omega

theorem pair_complement_cut_one_below (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (x v p q : V) (hx : x∉Z) (hv : v∉Z) (hxv : x≠v)
    (hInd : H.IsIndepSet (Z:Set V)) (hNoX : ∀u∈Z,¬H.Adj x u)
    (hxTwo : 2≤H.degree x) (hPair : H.maxDegree<H.degree x+H.degree v)
    (hVal : ∀u∈Z,H.Adj v u → H.maxDegree+1≤H.degree v+H.degree u)
    (hDegrees : ∀u∈Z,H.Adj v u → 2≤H.degree u+(if u=p ∨ u=q then 1 else 0))
    (hGuard : H.degree x=2 → H.Adj x v → ¬∃u∈Z,H.Adj v u) :
    H.maxDegree≤cutEdges H (insert x (insert v Z))+1 := by
  have hxOff:x∉insert v Z:=by simp only [mem_insert];tauto
  have hInsert:=cut_insert_identity H (insert v Z) x hxOff
  rw [inside_insert_of_no_neighbours H Z x v hNoX] at hInsert
  by_cases hEdge:∃u∈Z,H.Adj v u
  · by_cases hvMax:H.degree v=H.maxDegree
    · have hCut:=cut_insert_independent_two_exceptions H Z v p q hv hInd hDegrees
      rw [hvMax] at hCut
      by_cases hAdj:H.Adj x v
      · rw [if_pos hAdj] at hInsert
        have hxThree:3≤H.degree x:=by
          by_contra hn
          exact hGuard (by omega) hAdj hEdge
        omega
      · rw [if_neg hAdj] at hInsert
        omega
    · have hvLess:H.degree v<H.maxDegree:=lt_of_le_of_ne (H.degree_le_maxDegree v) hvMax
      have hCut:=cut_insert_independent_one_below H Z v hv hInd hEdge hvLess hVal
      split_ifs at hInsert <;>omega
  · have hNb:Plantholt.nbIn H Z v=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hAdj,huZ⟩:=mem_filter.mp hu
      have hvu:H.Adj v u:=by simpa only [mem_neighborFinset] using hAdj
      exact hEdge ⟨u,huZ,hvu⟩
    have hCut:=cut_insert_identity H Z v hv
    rw [hNb,card_empty] at hCut
    split_ifs at hInsert <;>omega

/-- The matching residue has the high-degree core used by Claim 4.5.
No degree claim is inferred for an arbitrary cleanup of that residue. -/
theorem round_other_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u)) (r : Round G c x y z)
    {v : V} (hv : v∈c.set) (hvx : v≠x) :
    (G\r.matching).maxDegree≤(G\r.matching).degree v+B := by
  have hHigh:=LargeCentreCriticalGeometry.other_degree_lower G c hx hLarge hv hvx
  have hSum:(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  have hOne:=r.degree_le_one v
  have hDrop:(G\r.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  omega

theorem two_omission_round_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (r : Round G c x y z)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hRoom : 2*B+3*K+4≤G.maxDegree)
    (S : Finset V) (hOdd : Odd S.card) (hTwo : (c.set\S).card=2) :
    internalEdges (G\r.matching) S≤(G\r.matching).maxDegree*(S.card/2) := by
  let R:=G\r.matching
  have hSum:∀u,R.degree u+r.matching.degree u=G.degree u:=by
    intro u
    simpa only [R,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original u
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hAnchor:R.degree x=G.degree x:=by
    have hh:=hSum x
    rw [r.core_degrees x hx,if_pos rfl] at hh
    omega
  have hHigh:∀v∈c.set,v≠x → R.maxDegree≤R.degree v+B:=by
    intro v hv hvx
    exact round_other_degree_lower G c hx hLarge r hv hvx
  have hComp:Sᶜ.card≤K+2:=by
    have hh:=complement_card_le_missing_add c.set S
    have hk:=c.complement_small
    omega
  by_contra hOver
  have hOF:R.maxDegree*(S.card/2) < internalEdges R S:=by
    change ¬(internalEdges R S≤R.maxDegree*(S.card/2)) at hOver
    omega
  have hCutSmall:cutEdges R S<R.maxDegree:=by
    by_contra hn
    have hBound:=(odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree S hOdd).mpr
      (show R.maxDegree≤cutEdges R S+deficitMass R R.maxDegree S by omega)
    omega
  by_cases hxS:x∈S
  · obtain ⟨u,v,huv,hMissing⟩:=card_eq_two.mp hTwo
    have hu:u∈c.set\S:=by rw [hMissing];simp
    have hv:v∈c.set\S:=by rw [hMissing];simp
    have hux:u≠x:=fun he=>(mem_sdiff.mp hu).2 (he.symm ▸ hxS)
    have hvx:v≠x:=fun he=>(mem_sdiff.mp hv).2 (he.symm ▸ hxS)
    have hU:=hHigh u (mem_sdiff.mp hu).1 hux
    have hV:=hHigh v (mem_sdiff.mp hv).1 hvx
    have hCut:=pair_degrees_le_cut_add R S u v
      (mem_compl.mpr (mem_sdiff.mp hu).2) (mem_compl.mpr (mem_sdiff.mp hv).2) huv
    omega
  · have hxMissing:x∈c.set\S:=mem_sdiff.mpr ⟨hx,hxS⟩
    have hRest:( (c.set\S).erase x).card=1:=by rw [card_erase_of_mem hxMissing,hTwo]
    obtain ⟨v,hRestEq⟩:=card_eq_one.mp hRest
    have hvRest:v∈(c.set\S).erase x:=by rw [hRestEq];simp
    have hvx:v≠x:=(mem_erase.mp hvRest).1
    have hvX:v∈c.set:=(mem_sdiff.mp (mem_erase.mp hvRest).2).1
    have hvOff:v∈Sᶜ:=mem_compl.mpr (mem_sdiff.mp (mem_erase.mp hvRest).2).2
    have hMissing:c.set\S={x,v}:=by
      rw [←insert_erase hxMissing,hRestEq]
    let Z:=Sᶜ∩c.setᶜ
    have hT:Sᶜ=insert x (insert v Z):=by
      ext u
      have hm:(u∈c.set ∧ u∉S)↔u=x ∨ u=v:=by
        simpa only [mem_sdiff,mem_insert,mem_singleton] using iff_of_eq (congrArg (u∈·) hMissing)
      simp only [Z,mem_compl,mem_inter,mem_insert]
      tauto
    have hxZ:x∉Z:=by simp only [Z,mem_inter,mem_compl];tauto
    have hvZ:v∉Z:=by simp only [Z,mem_inter,mem_compl];tauto
    have hInd:R.IsIndepSet (Z:Set V):=by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab hAdj
      exact c.independent (mem_compl.mp (mem_inter.mp ha).2)
        (mem_compl.mp (mem_inter.mp hb).2) hab hAdj.1
    have hNoX:∀u∈Z,¬R.Adj x u:=by
      intro u hu hAdj
      have huY:u∈c.setᶜ:=(mem_inter.mp hu).2
      have huOff:u∈Sᶜ:=(mem_inter.mp hu).1
      have hVal:=Overfull.deg_add hc hAdj.1
      have hXSum:=hSum x
      have hUSum:=hSum u
      have hUOne:=r.degree_le_one u
      have hVHigh:=hHigh v hvX hvx
      have hCut:=triple_degrees_le_cut_add R S x v u (mem_compl.mpr hxS) hvOff huOff
        hvx.symm (fun he=>(mem_compl.mp huY) (he.symm ▸ hx))
        (fun he=>(mem_compl.mp huY) (he.symm ▸ hvX))
      omega
    have hPair:R.maxDegree<R.degree x+R.degree v:=by
      have hOld:=hNonstop v hvX hvx
      have hVSum:=hSum v
      have hOne:=r.degree_le_one v
      omega
    have hxTwo:2≤R.degree x:=by rw [hAnchor];exact OddLowSmallCases.critical_two_le_degree G hc x
    have hVal:∀u∈Z,R.Adj v u → R.maxDegree+1≤R.degree v+R.degree u:=by
      intro u _ hAdj
      have hOld:=Overfull.deg_add hc hAdj.1
      have hVSum:=hSum v
      have hUSum:=hSum u
      have hOneV:=r.degree_le_one v
      have hOneU:=r.degree_le_one u
      omega
    have hDegrees:∀u∈Z,R.Adj v u → 2≤R.degree u+(if u=y ∨ u=z then 1 else 0):=by
      intro u hu _
      have hTwoU:=OddLowSmallCases.critical_two_le_degree G hc u
      have hUSum:=hSum u
      rw [r.complementary_degrees u (mem_inter.mp hu).2] at hUSum
      split_ifs at hUSum ⊢ <;>omega
    have hGuard:R.degree x=2 → R.Adj x v → ¬∃u∈Z,R.Adj v u:=by
      intro hxTwo hAdj ⟨u,hu,hvu⟩
      have huD:=CriticalIndependentPairMatching.complement_nonmaximum G hc c hx hLarge u (mem_inter.mp hu).2
      exact critical_degree_two_no_common_neighbour G hc x u v hxD huD
        (fun he=>(mem_compl.mp (mem_inter.mp hu).2) (he.symm ▸ hx))
        (by omega) hAdj.1 hvu.1.symm
    have hCut:=pair_complement_cut_one_below R Z x v y z hxZ hvZ hvx.symm
      hInd hNoX hxTwo hPair hVal hDegrees hGuard
    rw [←hT,NearTightOddSetGeometry.cutEdges_compl] at hCut
    have hBound:=(odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree S hOdd).mpr
      (odd_budget_of_one_below R S hOdd (by omega))
    omega

end OverfullWork.PaperTwoCoreRoundPreservation
