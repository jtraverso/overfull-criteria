module

public import OverfullWork.Saturation

@[expose] public section


/-! # Packing a prescribed number of edges into capacities at most two

Edges may overlap the original graph: this is the bounded parallel
completion, not an asserted simple saturation of the original graph.
-/
namespace OverfullWork.CapacityPacking
open SimpleGraph Finset
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nonadjacent_pair (J : SimpleGraph V) [DecidableRel J.Adj] (S : Finset V)
    (hdeg : ∀ v,J.degree v≤2) (hsize : 4≤S.card) :
    ∃ u∈S,∃ v∈S,u≠v ∧ ¬J.Adj u v := by
  obtain ⟨u,hu⟩:=card_pos.mp (show 0<S.card by omega)
  by_contra hn
  have hall : ∀ v∈S,u≠v → J.Adj u v := by
    intro v hv hne
    by_contra hno
    exact hn ⟨u,hu,v,hv,hne,hno⟩
  have hsub : S.erase u⊆J.neighborFinset u := by
    intro v hv
    obtain ⟨hvu,hv⟩:=mem_erase.mp hv
    rw [mem_neighborFinset]
    exact hall v hv hvu.symm
  have hc:=card_le_card hsub
  rw [card_erase_of_mem hu,card_neighborFinset_eq_degree] at hc
  have hd:=hdeg u
  omega

/-- A six-unit reserve suffices to avoid loops and repeated added edges. -/
theorem exists_packing (a : V → ℕ) (ha : ∀ v,a v≤2) (q : ℕ)
    (hsize : 2*q+6≤∑ v,a v) :
    ∃ J : SimpleGraph V, (∀ v,J.degree v≤a v) ∧ J.edgeSet.ncard=q := by
  classical
  let candidates:=(univ : Finset (SimpleGraph V)).filter
    (fun J => (∀ v,J.degree v≤a v) ∧ J.edgeSet.ncard≤q)
  have hempty : (⊥ : SimpleGraph V)∈candidates := by
    simp [candidates]
  obtain ⟨J,hJ,hmax⟩:=candidates.exists_max_image (fun H => H.edgeSet.ncard) ⟨⊥,hempty⟩
  obtain ⟨_,hcap,hq⟩:=mem_filter.mp hJ
  have hexact : J.edgeSet.ncard=q := by
    by_contra hn
    let b : V → ℕ:=fun v => a v-J.degree v
    let S:=univ.filter (fun v => 0<b v)
    have hb : ∀ v,b v≤2:=fun v => (Nat.sub_le _ _).trans (ha v)
    have htotal : (∑ v,b v)+2*J.edgeSet.ncard=∑ v,a v := by
      rw [Saturation.edges_ncard,←J.sum_degrees_eq_twice_card_edges,←sum_add_distrib]
      apply sum_congr rfl
      intro v _
      exact Nat.sub_add_cancel (hcap v)
    have hsupport : 4≤S.card := by
      have hle : (∑ v,b v)≤2*S.card := by
        calc
          _ ≤ ∑ v : V,if 0<b v then 2 else 0 := by
            apply sum_le_sum
            intro v _
            have h:=hb v
            split_ifs <;> omega
          _ = _ := by
            simp only [S,card_eq_sum_ones,sum_filter,mul_sum]
            apply sum_congr rfl
            intro v _
            split_ifs <;> omega
      omega
    obtain ⟨u,hu,v,hv,huv,hno⟩:=nonadjacent_pair J S (fun v => (hcap v).trans (ha v)) hsupport
    have huCap : J.degree u<a u:=by have hh:=(mem_filter.mp hu).2;dsimp [b] at hh;omega
    have hvCap : J.degree v<a v:=by have hh:=(mem_filter.mp hv).2;dsimp [b] at hh;omega
    have hnewdeg : ∀ w,(J⊔edge u v).degree w≤a w := by
      intro w
      have hh:=Saturation.degree_sup_edge_le J u v w
      by_cases hw : w=u ∨ w=v
      · rw [if_pos hw] at hh
        rcases hw with rfl|rfl <;> omega
      · rw [if_neg hw] at hh
        exact hh.trans (by simpa using hcap w)
    have hnewcard : (J⊔edge u v).edgeSet.ncard=J.edgeSet.ncard+1 := by
      rw [edgeSet_sup,edgeSet_edge_of_ne huv,Set.union_singleton]
      exact Set.ncard_insert_of_notMem hno
    have hmem : J⊔edge u v∈candidates:=mem_filter.mpr ⟨mem_univ _,hnewdeg,by omega⟩
    have hm:=hmax (J⊔edge u v) hmem
    omega
  exact ⟨J,hcap,hexact⟩

end OverfullWork.CapacityPacking
