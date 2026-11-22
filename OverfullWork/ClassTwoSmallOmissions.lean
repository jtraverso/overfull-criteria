module

public import OverfullWork.ClassTwoCoreSupersets

@[expose] public section


/-! # Small core omissions from a ready class-two source

Weak VAL on Y supplies the degree sums and active minimum degree. The
full maximum-neighbour inequality supplies the degree-two guard. No
criticality of the source or residue is used. Degree ordering is retained
explicitly in the source certificate; it is not inferred after cleanup.
-/
namespace OverfullWork.ClassTwoSmallOmissions
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency
open NormalizedAlmostStoppingRun ClassTwoMatchingRound PaperTopDegreeMatching
open PaperSmallCutGeometry PaperOneCoreRoundPreservation CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem one_core_round_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x y z : V}
    (hD : 4≤G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : CoreRound G c.set x y z)
    (v w : V) (hv : v∈c.set) (hw : w∈c.setᶜ) :
    internalEdges (G\r.matching) (insert w (c.set.erase v))≤
      (G\r.matching).maxDegree*((insert w (c.set.erase v)).card/2) := by
  let R:=G\r.matching
  have hSum:∀u,R.degree u+r.matching.degree u=G.degree u:=by
    intro u
    simpa only [R,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original u
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hNonmax:R.degree w<R.maxDegree:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using
      ClassTwoCleanupRound.residue_complement_nonmaximum G c.set hReady.1 c.light_pairs hD hTop r w hw
  have hInd:R.IsIndepSet (↑(c.setᶜ):Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact c.independent (mem_compl.mp ha) (mem_compl.mp hb) hab hAdj.1
  apply one_core_nonoverfull_from_source_bounds R c.set c.odd hInd v w y z hv hw hNonmax
  · have hOrder:=c.ordered w hw v hv
    have hV:=hSum v
    have hW:=hSum w
    have hOne:=r.degree_le_one v
    omega
  · intro u hu hAdj
    have hVAL:=weak_VAL G c.setᶜ hReady u (mem_erase.mp hu).2 v hAdj.1.symm
    have hV:=hSum v
    have hU:=hSum u
    have hOneV:=r.degree_le_one v
    have hOneU:=r.degree_le_one u
    omega
  · intro u hu hAdj
    have hTwo:=active_degree_at_least_two G c.setᶜ hReady u (mem_erase.mp hu).2
      ((G.degree_pos_iff_exists_adj u).mpr ⟨v,hAdj.1.symm⟩)
    have hU:=hSum u
    rw [r.complementary_degrees u (mem_erase.mp hu).2] at hU
    split_ifs at hU ⊢ <;>omega

theorem pair_complement_cut_one_below (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (x v p q : V) (hx : x∉Z) (hv : v∉Z) (hxv : x≠v)
    (hInd : H.IsIndepSet (Z:Set V)) (hNoX : ∀u∈Z,¬H.Adj x u)
    (hxTwo : 2≤H.degree x) (hPair : H.maxDegree<H.degree x+H.degree v)
    (hVal : ∀u∈Z,H.Adj v u → H.maxDegree+1≤H.degree v+H.degree u)
    (hDegrees : ∀u∈Z,H.Adj v u → 2≤H.degree u+(if u=p ∨ u=q then 1 else 0))
    (hGuard : H.degree x=2 → H.Adj x v → ∀u∈Z,H.Adj v u → 2≤H.degree u) :
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
        by_cases hxEq:H.degree x=2
        · have hStrong:=PaperOneCoreCut.cut_insert_independent_lower H Z v hv hInd hEdge (by
            intro u hu hA
            have hh:=hGuard hxEq hAdj u hu hA
            omega)
          omega
        · omega
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

theorem round_other_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u)) (r : CoreRound G c.set x y z)
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
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hy : y∈c.setᶜ) (r : CoreRound G c.set x y z)
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
      have hVal:=weak_VAL G c.setᶜ hReady u huY x hAdj.1.symm
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
    have hxTwo:2≤R.degree x:=by rw [hAnchor];exact selected_anchor_degree_at_least_two G c hReady r hx hy
    have hVal:∀u∈Z,R.Adj v u → R.maxDegree+1≤R.degree v+R.degree u:=by
      intro u hu hAdj
      have hOld:=weak_VAL G c.setᶜ hReady u (mem_inter.mp hu).2 v hAdj.1.symm
      have hVSum:=hSum v
      have hUSum:=hSum u
      have hOneV:=r.degree_le_one v
      have hOneU:=r.degree_le_one u
      omega
    have hDegrees:∀u∈Z,R.Adj v u → 2≤R.degree u+(if u=y ∨ u=z then 1 else 0):=by
      intro u hu hAdj
      have hTwoU:=active_degree_at_least_two G c.setᶜ hReady u (mem_inter.mp hu).2
        ((G.degree_pos_iff_exists_adj u).mpr ⟨v,hAdj.1.symm⟩)
      have hUSum:=hSum u
      rw [r.complementary_degrees u (mem_inter.mp hu).2] at hUSum
      split_ifs at hUSum ⊢ <;>omega
    have hGuard:R.degree x=2 → R.Adj x v → ∀u∈Z,R.Adj v u → 2≤R.degree u:=by
      intro _ hAdj u hu hvu
      by_contra hNot
      have huY:u∈c.setᶜ:=(mem_inter.mp hu).2
      have hLower:=active_degree_at_least_two G c.setᶜ hReady u huY
        ((G.degree_pos_iff_exists_adj u).mpr ⟨v,hvu.1.symm⟩)
      have hUSum:=hSum u
      have hOne:=r.degree_le_one u
      have huTwo:G.degree u=2:=by omega
      exact degree_two_forbids_nonmaximum_common_neighbour G c.setᶜ hReady u x v huY huTwo hxD
        (fun he=>(mem_compl.mp huY) (he.symm ▸ hx)) hvu.1.symm hAdj.1
    have hCut:=pair_complement_cut_one_below R Z x v y z hxZ hvZ hvx.symm
      hInd hNoX hxTwo hPair hVal hDegrees hGuard
    rw [←hT,NearTightOddSetGeometry.cutEdges_compl] at hCut
    have hBound:=(odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree S hOdd).mpr
      (odd_budget_of_one_below R S hOdd (by omega))
    omega

end OverfullWork.ClassTwoSmallOmissions
