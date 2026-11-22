module

public import OverfullWork.CyclicSpanningLinkage

@[expose] public section


/-! Enumerate the parallel-copy matching as prescribed pairs in CMS §5.2. -/
namespace OverfullWork.EvenHamiltonFactorization

open Finset SimpleGraph MultiGraph
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A matching of copies supplies every prescribed pair exactly once.
Its degree is the indicator of membership among the endpoints. -/
theorem exists_matching_endpoint_enumeration (J : MultiGraph V)
    (hDeg : ∀ v, J.degree v ≤ 1) :
    ∃ a b : Fin J.edgeCount → V,
      Function.Injective a ∧ Function.Injective b ∧ (∀ i j, a i ≠ b j) ∧
      (∀ i, 0 < J.mult s(a i,b i)) ∧
      ∀ x, J.degree x = if ∃ i, x = a i ∨ x = b i then 1 else 0 := by
  let G := J.supportGraph
  have hSimple := J.of_supportGraph (J.mult_le_one_of_degrees hDeg)
  have hCard : Fintype.card (Fin J.edgeCount) = Fintype.card G.edgeSet := by
    rw [Fintype.card_fin,G.card_edgeSet,← edgeCount_ofSimpleGraph, hSimple]
  let e : Fin J.edgeCount ≃ G.edgeSet := Fintype.equivOfCardEq hCard
  have hChoose (i : Fin J.edgeCount) : ∃ a b, (e i).val = s(a,b) := by
    induction (e i).val using Sym2.inductionOn with
    | hf a b => exact ⟨a,b,rfl⟩
  choose a b h using hChoose
  have hAdj (i : Fin J.edgeCount) : G.Adj (a i) (b i) := by
    simpa only [SimpleGraph.mem_edgeSet] using ((h i) ▸ (e i).property : s(a i,b i) ∈ G.edgeSet)
  have hMatch := J.supportGraph_isMatching hDeg
  have hEq (i j : Fin J.edgeCount) (hij : s(a i,b i) = s(a j,b j)) : i = j :=
    e.injective (Subtype.ext ((h i).trans (hij.trans (h j).symm)))
  refine ⟨a,b,?_,?_,?_,hAdj,?_⟩
  · intro i j heq
    have hw : b i = b j := hMatch _ _ _ (hAdj i) (heq.symm ▸ hAdj j)
    exact hEq i j (by rw [heq,hw])
  · intro i j heq
    have hw : a i = a j := hMatch _ _ _ (hAdj i).symm (heq.symm ▸ (hAdj j).symm)
    exact hEq i j (by rw [heq,hw])
  · intro i j heq
    have hw : b i = a j := hMatch _ _ _ (hAdj i) (heq.symm ▸ (hAdj j).symm)
    have hij := hEq i j (by rw [heq,hw,Sym2.eq_swap])
    exact (hAdj i).ne (by simpa only [hij] using heq)
  · intro x
    by_cases hx : ∃ i, x = a i ∨ x = b i
    · rw [if_pos hx]
      obtain ⟨i,rfl | rfl⟩ := hx
      · exact le_antisymm (hDeg _) ((hAdj i).trans_le (J.mult_pair_le_degree (a i) (b i)))
      · exact le_antisymm (hDeg _) (((hAdj i).symm).trans_le (J.mult_pair_le_degree (b i) (a i)))
    · rw [if_neg hx,degree_eq_sum_mult]
      apply sum_eq_zero
      intro y _
      by_contra hy
      have hxy : G.Adj x y := Nat.pos_of_ne_zero hy
      let z : G.edgeSet := ⟨s(x,y),by simpa only [SimpleGraph.mem_edgeSet] using hxy⟩
      obtain ⟨i,hi⟩ := e.surjective z
      have hPair : s(x,y) = s(a i,b i) :=
        (congrArg Subtype.val hi).symm.trans (h i)
      rw [Sym2.eq_iff] at hPair
      exact hx ⟨i,hPair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩

end OverfullWork.EvenHamiltonFactorization
