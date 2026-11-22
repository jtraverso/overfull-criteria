module

public import OverfullWork.SparseDeficitCore
public import OverfullWork.RobustExpansionLifting

@[expose] public section


/-! # Robust expansion from a sparse set of degree exceptions

These are finite structural consequences of an explicit deficit bound.
The bound is an input; no critical average-degree theorem or colouring
theorem for robust expanders is assumed or concluded.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsRobustAt.mono {G : SimpleGraph V} [DecidableRel G.Adj]
    {r r' t t' : ℕ} (h : IsRobustAt G r t) (hr : r'≤r) (ht : t≤t') :
    IsRobustAt G r' t' := by
  intro S hSlo hShi
  have hh:=h S (by omega) (by omega)
  have hs : neighbourhood G r S⊆neighbourhood G r' S := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,hr.trans (mem_filter.mp hx).2⟩
  have hc:=card_le_card hs
  omega

theorem exception_count_le_of_mass_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (D t k : ℕ) (hmass : totalDeficit G D<(t+1)*(k+1)) :
    (exceptions G D t).card≤k := by
  have htail:=exception_count_le_mass G D t
  by_contra hn
  have hmul:=Nat.mul_le_mul_left (t+1) (show k+1≤(exceptions G D t).card by omega)
  omega

/-- Remove the few exceptional vertices, prove dense minimum-degree
expansion there, and then reinsert the exceptions with an explicit cost. -/
theorem isRobustAt_of_sparse_exceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (t m r r' s : ℕ)
    (hmargin : Fintype.card V+2*m+2*t+(exceptions G G.maxDegree t).card≤2*G.maxDegree)
    (hr : 0<r) (hrs : r≤s) (hrm : r≤m)
    (hscale : 4*r*Fintype.card V≤m*s)
    (hbudget : (exceptions G G.maxDegree t).card+r'≤r) :
    IsRobustAt G r' (s+(exceptions G G.maxDegree t).card) := by
  let U:=exceptions G G.maxDegree t
  let S:=Uᶜ
  have hk:=card_le_univ U
  have hScard : S.card=Fintype.card V-U.card:=by simp only [S,card_compl,card_univ]
  have hHcard : Fintype.card (S : Set V)=Fintype.card V-U.card:=by
    simpa only [Finset.coe_sort_coe,Fintype.card_coe] using hScard
  have hlo : G.maxDegree-t-U.card≤(G.induce (S : Set V)).minDegree := by
    have hgood : ∀v : (S : Set V),G.maxDegree≤G.degree v.val+t := by
      intro v
      apply degree_add_threshold_of_not_exception G G.maxDegree t v.val
      have hv : v.val∈Uᶜ:=v.property
      exact mem_compl.mp hv
    by_cases hne : Nonempty (S : Set V)
    · have : Nonempty (S : Set V):=hne
      apply (G.induce (S : Set V)).le_minDegree_of_forall_le_degree
      intro v
      have hsplit:=degree_add_card_le_neighboursIn_add_order G S v.val
      have hdeg : (G.induce (S : Set V)).degree v=PrunedCore.neighboursIn G S v.val := by
        rw [←card_neighborSet_eq_degree]
        let E : (G.induce (S : Set V)).neighborSet v ≃
            ↥((G.neighborFinset v.val).filter fun x=>x∈S) :=
          { toFun:=fun w=>⟨w.val.val,mem_filter.mpr
              ⟨(mem_neighborFinset G _ _).mpr w.property,w.val.property⟩⟩
            invFun:=fun w=>⟨⟨w.val,(mem_filter.mp w.property).2⟩,
              (mem_neighborFinset G _ _).mp (mem_filter.mp w.property).1⟩
            left_inv:=fun _=>rfl
            right_inv:=fun _=>rfl }
        exact (Fintype.card_congr E).trans (by simp only [Fintype.card_coe];rfl)
      have hg:=hgood v
      rw [hdeg]
      omega
    · have hs : S=∅ := by
        apply eq_empty_of_forall_notMem
        intro x hx
        exact hne ⟨⟨x,hx⟩⟩
      have hu : U=univ := by
        have he:=congrArg (fun T : Finset V=>Tᶜ) hs
        simpa only [S,compl_compl,compl_empty] using he
      have hd:=G.maxDegree_le_of_forall_degree_le (Fintype.card V)
        (fun v=>(G.degree_lt_card_verts v).le)
      rw [hu,card_univ]
      omega
  have hHmargin : Fintype.card (S : Set V)+2*m≤2*(G.induce (S : Set V)).minDegree := by
    rw [hHcard]
    change Fintype.card V+2*m+2*t+U.card≤2*G.maxDegree at hmargin
    omega
  have hHscale : 4*r*Fintype.card (S : Set V)≤m*s := by
    have hc : Fintype.card (S : Set V)≤Fintype.card V:=by rw [hHcard];omega
    exact (Nat.mul_le_mul_left (4*r) hc).trans hscale
  have hH:=isRobustAt_of_minDegree_margin (G.induce (S : Set V)) m r s
    hHmargin hr hrs hrm hHscale
  have hpay : Fintype.card V-S.card+r'≤r := by
    rw [hScard]
    change U.card+r'≤r at hbudget
    omega
  have hres:=isRobustAt_of_induced G S r r' s hH hpay
  have hleft : Fintype.card V-S.card=U.card:=by rw [hScard];omega
  simpa only [hleft,U] using hres

/-- A first-moment deficit bound supplies the exceptional-set budget.
The result is expansion only, with no implicit extension of colourings. -/
theorem isRobustAt_of_deficit_mass (G : SimpleGraph V) [DecidableRel G.Adj]
    (t k m r r' s : ℕ)
    (hmass : totalDeficit G G.maxDegree<(t+1)*(k+1))
    (hmargin : Fintype.card V+2*m+2*t+k≤2*G.maxDegree)
    (hr : 0<r) (hrs : r≤s) (hrm : r≤m)
    (hscale : 4*r*Fintype.card V≤m*s) (hbudget : k+r'≤r) :
    IsRobustAt G r' (s+k) := by
  have hk:=exception_count_le_of_mass_lt G G.maxDegree t k hmass
  have h:=isRobustAt_of_sparse_exceptions G t m r r' s (by omega)
    hr hrs hrm hscale (by omega)
  exact h.mono le_rfl (by omega)

end OverfullWork.RobustExpansion
