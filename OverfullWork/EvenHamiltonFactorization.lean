module

public import OverfullWork.EvenPathClosure
public import OverfullWork.AddColourMatching
public import OverfullWork.RobustHamiltonDecomposition
public import OverfullWork.ColouredLayerSum

@[expose] public section


/-! Colour the even Hamilton factors used in CMS §5.2, Case 1. -/
namespace OverfullWork.EvenHamiltonFactorization

open Finset SimpleGraph MultiGraph PathGraphRealization DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One of the two colours of a spanning path is absent exactly at both
endpoints. The handshaking identity forces the endpoint colours to agree. -/
theorem spanning_path_endpoint_colour {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hSpan : ∀ w, w ∈ p.support)
    (huv : u ≠ v) (hEven : Even (Fintype.card V)) :
    ∃ (C : (ofSimpleGraph (pathGraph p)).EdgeColoring 2) (i : Fin 2),
      ∀ w, (C.colourGraph i).degree w = if w = u ∨ w = v then 0 else 1 := by
  let Q := ofSimpleGraph (pathGraph p)
  have hdeg (w : V) : Q.degree w = if w = u ∨ w = v then 1 else 2 := by
    rw [show Q.degree w = (pathGraph p).degree w from degree_ofSimpleGraph _ _]
    by_cases hu : w = u
    · subst w
      simpa using degree_start p hp huv
    by_cases hv : w = v
    · subst w
      simpa using degree_end p hp huv
    · simpa only [hu,hv,or_self,if_false] using degree_internal p hp (hSpan w) hu hv
  obtain ⟨C⟩ := ofSimpleGraph_colouring (pathGraph p) 2
    (TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two _
      (PathGraphRealization.isAcyclic p hp) (degree_le_two p hp))
  have hP := C.missingPalette_card_add_degree u
  have hdu : Q.degree u = 1 := by simp [hdeg]
  change (C.missingPalette u).card + Q.degree u = 2 at hP
  obtain ⟨i,hi⟩ := card_pos.mp (show 0 < (C.missingPalette u).card by omega)
  have hU : (C.colourGraph i).degree u = 0 := (mem_filter.mp hi).2
  have hInternal (w : V) (hu : w ≠ u) (hv : w ≠ v) : (C.colourGraph i).degree w = 1 :=
    EvenPathClosure.full_two_colour_degree C w (by
      change Q.degree w = 2
      rw [hdeg,if_neg (not_or.mpr ⟨hu,hv⟩)]) i
  have hV : (C.colourGraph i).degree v = 0 := by
    by_contra hn
    have hSet : C.missingSet univ i = {u} := by
      ext w
      simp only [MultiGraph.EdgeColoring.missingSet,mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro hw
        by_contra hwu
        have hwv : w ≠ v := fun hh => hn (hh ▸ hw)
        exact Nat.one_ne_zero ((hInternal w hwu hwv).symm.trans hw)
      · rintro rfl
        exact hU
    have hSum := C.missing_card_add_degree_sum univ i
    rw [hSet,card_singleton,card_univ,(C.colourGraph i).sum_degrees_eq_twice_edgeCount] at hSum
    obtain ⟨k,hk⟩ := hEven
    omega
  refine ⟨C,i,?_⟩
  intro w
  by_cases hu : w = u
  · subst w; simpa using hU
  by_cases hv : w = v
  · subst w; simpa using hV
  · simpa only [hu,hv,or_self,if_false] using hInternal w hu hv

/-- A spanning path on a positive even number of vertices contains a
perfect matching, realized as a simple spanning subgraph of the host. -/
theorem one_factor_of_spanning_path {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hSpan : ∀ w, w ∈ p.support)
    (huv : u ≠ v) (hEven : Even (Fintype.card V)) :
    ∃ J : SimpleGraph V, J ≤ G ∧ ∀ w, J.degree w = 1 := by
  obtain ⟨C,i,hMiss⟩ := spanning_path_endpoint_colour p hp hSpan huv hEven
  obtain ⟨j,hji⟩ := exists_ne i
  let J := (C.colourGraph j).supportGraph
  have hDeg (w : V) : (C.colourGraph j).degree w = 1 := by
    by_cases hw : w = u ∨ w = v
    · have hDeg : (ofSimpleGraph (pathGraph p)).degree w = 1 := by
        rw [degree_ofSimpleGraph]
        rcases hw with rfl | rfl
        · exact degree_start p hp huv
        · exact degree_end p hp huv
      have hSum := C.sum_colour_degree w
      rw [Fin.sum_univ_two,hDeg] at hSum
      have h0 := hMiss w
      rw [if_pos hw] at h0
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · rw [not_or] at hw
      exact EvenPathClosure.full_two_colour_degree C w
        (by rw [degree_ofSimpleGraph]; exact degree_internal p hp (hSpan w) hw.1 hw.2) j
  refine ⟨J,?_,?_⟩
  · intro w z h
    have hm : 0 < (C.colourGraph j).mult s(w,z) := h
    have hh := hm.trans_le (C.col_le_mult s(w,z) j)
    apply PathGraphRealization.le_original p
    change 0 < (if (pathGraph p).Adj w z then 1 else 0) at hh
    split_ifs at hh with hx
    · exact hx
    · omega
  · intro w
    rw [← degree_ofSimpleGraph J]
    rw [of_supportGraph _ (fun t => by
      induction t using Sym2.inductionOn with
      | hf a b =>
        exact ((C.colourGraph j).mult_pair_le_degree a b).trans (le_of_eq (hDeg a)))]
    exact hDeg w

/-- Split a spanning two-regular cycle on an even vertex set into two
colours by closing a Hamilton path in its common missing colour. -/
theorem two_colourings_of_even_hamilton_multigraph (M : MultiGraph V)
    (hCycle : HasSpanningCycle M.supportGraph.Adj) (hReg : M.IsRegularOfDegree 2)
    (hEven : Even (Fintype.card V)) :
    Nonempty (M.EdgeColoring 2) := by
  let G := M.supportGraph
  obtain ⟨T,x,hN,hMem,hHead,hChain⟩ := hCycle
  have hT : T ≠ [] := by intro h; simp [h] at hHead
  have hTChain : T.IsChain G.Adj := (List.isChain_append.mp hChain).1
  let u := T.head hT
  let v := T.getLast hT
  have hx : u = x := Option.some.inj (by simpa only [u,List.head?_eq_some_head hT] using hHead)
  have hvx : G.Adj v x := (List.isChain_append.mp hChain).2.2 v
    (by simp [v,List.getLast?_eq_some_getLast hT]) x (by simp)
  have huv : u ≠ v := (hx ▸ hvx).ne.symm
  let p := Walk.ofSupport T hT hTChain
  have hs : p.support = T := Walk.support_ofSupport hT hTChain
  have hp : p.IsPath := (Walk.isPath_def p).mpr (hs.symm ▸ hN)
  obtain ⟨C,i,hMiss⟩ := spanning_path_endpoint_colour p hp (fun w => hs.symm ▸ hMem w) huv hEven
  let Q := ofSimpleGraph (pathGraph p)
  have hLe (e : Sym2 V) : Q.mult e ≤ M.mult e := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      change (if (pathGraph p).Adj a b then 1 else 0) ≤ M.mult s(a,b)
      split_ifs with he
      · exact PathGraphRealization.le_original p he
      · exact Nat.zero_le _
  let P : M.PartialColouring 2 := ⟨Q,C,hLe⟩
  have hAvailable : ∀ w, P.available.degree w = if w = u ∨ w = v then 1 else 0 := by
    intro w
    have h := P.available_degree w
    change _ + Q.degree w = M.degree w at h
    rw [show Q.degree w = (pathGraph p).degree w from degree_ofSimpleGraph _ _,
      hReg] at h
    by_cases hu : w = u
    · subst w
      rw [degree_start p hp huv] at h
      rw [if_pos (Or.inl rfl)]
      omega
    by_cases hv : w = v
    · subst w
      rw [degree_end p hp huv] at h
      rw [if_pos (Or.inr rfl)]
      omega
    · simp only [hu,hv,or_self,if_false]
      rw [degree_internal p hp (hs.symm ▸ hMem w) hu hv] at h
      omega
  let P' := P.addMatching i P.available (fun _ => le_rfl) (by
    intro w
    change (C.colourGraph i).degree w + P.available.degree w ≤ 1
    rw [hMiss,hAvailable]
    split <;> decide)
  have hGraph : P'.graph = M := add_subtract_of_le M Q hLe
  change Nonempty (M.EdgeColoring 2)
  rw [← hGraph]
  exact ⟨P'.colouring⟩

/-- The same construction on a simple Hamilton factor. -/
theorem two_colourings_of_even_hamilton_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (hCycle : HasSpanningCycle G.Adj) (hReg : ∀ v, G.degree v = 2)
    (hEven : Even (Fintype.card V)) :
    Nonempty ((ofSimpleGraph G).EdgeColoring 2) := by
  apply two_colourings_of_even_hamilton_multigraph (ofSimpleGraph G) _ _ hEven
  · obtain ⟨T,x,hN,hMem,hHead,hChain⟩ := hCycle
    refine ⟨T,x,hN,hMem,hHead,hChain.imp (fun a b hab => ?_)⟩
    change 0 < (if G.Adj a b then 1 else 0)
    simp [hab]
  · intro v
    rw [degree_ofSimpleGraph,hReg]

/-- The Hamilton decomposition supplied by CMS Theorem 5.5 can be
turned into a full colour palette on an even vertex set. -/
theorem colourable_of_hamilton_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (P : HamiltonDecomposition G k) (hEven : Even (Fintype.card V)) :
    Nonempty ((ofSimpleGraph G).EdgeColoring (2*k)) := by
  let L := fun i => ofSimpleGraph (P.factor i)
  have hL : ∀ i, Nonempty ((L i).EdgeColoring 2) := fun i =>
    two_colourings_of_even_hamilton_cycle (P.factor i) (P.spanning i) (P.degrees i) hEven
  let C := fun i => Classical.choice (hL i)
  have hSum : CanonicalPairTriangle.sumCopies univ L = ofSimpleGraph G := by
    apply ext_mult
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      change (∑ i : Fin k, (if (P.factor i).Adj a b then 1 else 0 : ℕ)) =
        if G.Adj a b then 1 else 0
      by_cases hg : G.Adj a b
      · obtain ⟨i,hi,hU⟩ := P.partition a b hg
        simp only [if_pos hg]
        rw [sum_eq_single i]
        · simp [hi]
        · intro j _ hj
          exact if_neg (fun h => hj (hU j h))
        · simp
      · simp [hg,show ∀ i, ¬ (P.factor i).Adj a b from fun i h => hg (P.factor_le i h)]
  have hC := ColouredLayerSum.colouring L C
  rw [hSum,Nat.mul_comm] at hC
  exact ⟨hC⟩

end OverfullWork.EvenHamiltonFactorization
