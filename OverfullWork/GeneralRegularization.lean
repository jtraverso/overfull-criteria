module

public import OverfullWork.LooplessRealization

@[expose] public section


/-! # Regular completion without any degree-gap assumption

This supplies a regular multigraph, not a factorization. The multiplicity
and parallel excess are tracked as functions of the original deficits.
-/
namespace OverfullWork.GeneralRegularization
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000

/-- Complete arbitrary balanced even deficits on the same vertex set. -/
theorem exists_completion (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v,G.degree v≤D)
    (heven : Even (∑ v : V,(D-G.degree v)))
    (hbalance : ∀ v,2*(D-G.degree v)≤∑ w : V,(D-G.degree w)) :
    ∃ M : MultiGraph V,M.IsRegularOfDegree D ∧
      (∀ u v,G.Adj u v → 1≤M.mult s(u,v)) ∧
      (∀ v,M.parallelExcess v≤D-G.degree v) ∧
      ∀ u v,M.mult s(u,v)≤(if G.Adj u v then 1 else 0)+min (D-G.degree u) (D-G.degree v) := by
  classical
  obtain ⟨J,hJ⟩:=LooplessRealization.exists_realization (fun v => D-G.degree v) heven hbalance
  let M:=(MultiGraph.ofSimpleGraph G).addCopies J
  refine ⟨M,?_,?_,?_,?_⟩
  · intro v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_ofSimpleGraph,hJ]
    exact Nat.add_sub_of_le (hdeg v)
  · intro u v huv
    change 1≤(if s(u,v)∈G.edgeSet then 1 else 0)+J.mult s(u,v)
    simp only [mem_edgeSet,if_pos huv]
    omega
  · intro v
    have hs : M.parallelExcess v≤J.degree v := by
      rw [MultiGraph.degree_eq_sum_mult]
      apply sum_le_sum
      intro w _
      change (if s(v,w)∈G.edgeSet then 1 else 0)+J.mult s(v,w)-1≤J.mult s(v,w)
      split_ifs <;> omega
    exact hs.trans (hJ v).le
  · intro u v
    have hu:=J.mult_pair_le_degree u v
    have hv : J.mult s(u,v)≤J.degree v := by
      calc
        _ = J.mult s(v,u):=by rw [Sym2.eq_swap]
        _ ≤ J.degree v:=J.mult_pair_le_degree v u
    rw [hJ] at hu hv
    change (if s(u,v)∈G.edgeSet then 1 else 0)+J.mult s(u,v)≤_
    simp only [mem_edgeSet]
    exact Nat.add_le_add_left (le_min hu hv) _

/-- The same-order completion condition is necessary as well. -/
theorem completion_iff (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v,G.degree v≤D) :
    (∃ M : MultiGraph V,M.IsRegularOfDegree D ∧
      ∀ u v,G.Adj u v → 1≤M.mult s(u,v)) ↔
      Even (∑ v : V,(D-G.degree v)) ∧
      ∀ v,2*(D-G.degree v)≤∑ w : V,(D-G.degree w) := by
  constructor
  · rintro ⟨M,hreg,hcontains⟩
    have hsub : ∀ e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e := by
      intro e
      induction e using Sym2.inductionOn with
      | hf u v =>
        change (if s(u,v)∈G.edgeSet then 1 else 0)≤_
        simp only [mem_edgeSet]
        split_ifs with h
        · exact hcontains u v h
        · exact Nat.zero_le _
    apply (LooplessRealization.realization_iff (fun v => D-G.degree v)).mp
    refine ⟨M.subtractCopies (MultiGraph.ofSimpleGraph G),?_⟩
    intro v
    have hh:=MultiGraph.degree_subtract_add M (MultiGraph.ofSimpleGraph G) hsub v
    rw [hreg v,MultiGraph.degree_ofSimpleGraph] at hh
    omega
  · rintro ⟨heven,hbalance⟩
    obtain ⟨M,hreg,hcontains,_,_⟩:=exists_completion G D hdeg heven hbalance
    exact ⟨M,hreg,hcontains⟩

/-- Arbitrary even-order graphs without overfull sets admit regular
completion. The gap bound only controls its multiplicity and excess. -/
theorem exists_even_bounded_completion (G : SimpleGraph V) [DecidableRel G.Adj]
    (m r : ℕ) (hm : 1≤m) (hcard : Fintype.card V=2*m)
    (hno : ¬G.HasOverfullSubgraph) (hgap : G.maxDegree-G.minDegree≤r) :
    ∃ M : MultiGraph V,M.IsRegularOfDegree G.maxDegree ∧
      (∀ e,M.mult e≤r+1) ∧ (∀ v,M.parallelExcess v≤r) ∧
      ∀ u v,G.Adj u v → 1≤M.mult s(u,v) := by
  obtain ⟨M,hreg,hcontains,hexcess,hpair⟩:=exists_completion G G.maxDegree
    G.degree_le_maxDegree (EvenDeficit.total_even G m hcard)
    (EvenDeficit.balanced_of_no_overfull G m hm hcard hno)
  have hdef (v : V) : G.maxDegree-G.degree v≤r:=by
    have hh:=G.minDegree_le_degree v
    omega
  refine ⟨M,hreg,?_,fun v => (hexcess v).trans (hdef v),hcontains⟩
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hh:=hpair u v
    have hd:=hdef u
    have hmin:=min_le_left (G.maxDegree-G.degree u) (G.maxDegree-G.degree v)
    split_ifs at hh <;> omega

/-- Odd graphs below the whole-graph overfull bound can also be
regularized, with one new vertex, without restricting the degree gap. -/
theorem exists_odd_bounded_extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (m r : ℕ) (_hm : 1≤m) (hcard : Fintype.card V+1=2*m)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hgap : G.maxDegree-G.minDegree≤r) :
    ∃ M : MultiGraph (Option V),M.IsRegularOfDegree G.maxDegree ∧
      (∀ e,M.mult e≤r+1) ∧ M.HasParallelBudget none r ∧
      ∀ u v,G.Adj u v → 1≤M.mult s(some u,some v) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  let H:=OddOrder.pointExtend G ∅
  have hnone : H.degree none=0:=by simpa using OddOrder.degree_none G ∅
  have hsome (v : V) : H.degree (some v)=G.degree v:=by
    simpa using OddOrder.degree_some G ∅ v
  have hdeg : ∀ w,H.degree w≤G.maxDegree := by
    intro w
    cases w with
    | none => rw [hnone];exact Nat.zero_le _
    | some v => rw [hsome];exact G.degree_le_maxDegree v
  have hmax : H.maxDegree=G.maxDegree:=le_antisymm
    (H.maxDegree_le_of_forall_degree_le _ hdeg) (OddOrder.intoExtension G ∅).maxDegree_mono
  have hcardH : Fintype.card (Option V)=2*m:=by simpa using hcard
  have hsum : (∑ w : Option V,(G.maxDegree-H.degree w))=
      G.maxDegree+(∑ v : V,(G.maxDegree-G.degree v)) := by
    simp only [Fintype.sum_option,hnone,hsome,Nat.sub_zero]
  have hreserve : G.maxDegree≤∑ v : V,(G.maxDegree-G.degree v) := by
    have ht:=MultigraphExtension.total_deficit_identity G
    rw [G.sum_degrees_eq_twice_card_edges] at ht
    have hn : 1≤Fintype.card V:=by omega
    have hs : G.maxDegree*(Fintype.card V-1)+G.maxDegree=Fintype.card V*G.maxDegree := by
      calc
        _ = G.maxDegree*((Fintype.card V-1)+1):=by ring
        _ = _ := by rw [Nat.sub_add_cancel hn,Nat.mul_comm]
    omega
  have heven : Even (∑ w : Option V,(G.maxDegree-H.degree w)) := by
    rw [←hmax]
    exact EvenDeficit.total_even H m hcardH
  have hbal : ∀ w,2*(G.maxDegree-H.degree w)≤∑ z : Option V,(G.maxDegree-H.degree z) := by
    intro w
    rw [hsum]
    have hh : G.maxDegree-H.degree w≤G.maxDegree:=Nat.sub_le _ _
    omega
  obtain ⟨M,hreg,hcontains,hexcess,hpair⟩:=exists_completion H G.maxDegree hdeg heven hbal
  have hdef (v : V) : G.maxDegree-G.degree v≤r := by
    have hh:=G.minDegree_le_degree v
    omega
  refine ⟨M,hreg,?_,?_,?_⟩
  · intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases huv : u=v
      · subst v
        rw [M.loopless s(u,u) (by simp)]
        exact Nat.zero_le _
      · have hh:=hpair u v
        cases u with
        | none =>
          cases v with
          | none => exact False.elim (huv rfl)
          | some v =>
            have hd:=hdef v
            rw [hsome] at hh
            have hm:=min_le_right (G.maxDegree-H.degree none) (G.maxDegree-G.degree v)
            split_ifs at hh <;> omega
        | some u =>
          have hd:=hdef u
          rw [hsome] at hh
          have hm:=min_le_left (G.maxDegree-G.degree u) (G.maxDegree-H.degree v)
          split_ifs at hh <;> omega
  · intro w hw
    cases w with
    | none => exact False.elim (hw rfl)
    | some v =>
      have hh:=hexcess (some v)
      rw [hsome] at hh
      exact hh.trans (hdef v)
  · intro u v huv
    exact hcontains (some u) (some v) huv

/-- Concentrating all deficits at an adjacent pair forces r+1 copies of
that edge in every same-order completion. This explains why multiplicity
two cannot simply be retained when the degree gap increases. -/
theorem two_deficits_force_multiplicity (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (u v : V) (huv : G.Adj u v)
    (hdef : ∀ w,D-G.degree w=if w=u ∨ w=v then r else 0)
    (M : MultiGraph V) (hreg : M.IsRegularOfDegree D)
    (hcontains : ∀ a b,G.Adj a b → 1≤M.mult s(a,b)) :
    M.mult s(u,v)=r+1 := by
  classical
  have hsub : ∀ e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e := by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      change (if s(a,b)∈G.edgeSet then 1 else 0)≤_
      simp only [mem_edgeSet]
      split_ifs with h
      · exact hcontains a b h
      · exact Nat.zero_le _
  let J:=M.subtractCopies (MultiGraph.ofSimpleGraph G)
  have hJ (w : V) : J.degree w=if w=u ∨ w=v then r else 0 := by
    have hh:=MultiGraph.degree_subtract_add M (MultiGraph.ofSimpleGraph G) hsub w
    rw [hreg w,MultiGraph.degree_ofSimpleGraph] at hh
    have hd:=hdef w
    change J.degree w+G.degree w=D at hh
    omega
  have hzero (w : V) (hw : w≠v) : J.mult s(u,w)=0 := by
    by_cases hwu : w=u
    · subst w
      exact J.loopless s(u,u) (by simp)
    · have hh:=J.mult_pair_le_degree w u
      rw [hJ,if_neg (by tauto)] at hh
      have he : J.mult s(u,w)=J.mult s(w,u):=by rw [Sym2.eq_swap]
      omega
  have hmult : J.mult s(u,v)=r := by
    have hh:=J.degree_eq_sum_mult u
    rw [hJ,if_pos (Or.inl rfl)] at hh
    rw [sum_eq_single v (fun w _ hw => hzero w hw) (by simp)] at hh
    exact hh.symm
  have hc:=hcontains u v huv
  change M.mult s(u,v)-(if s(u,v)∈G.edgeSet then 1 else 0)=r at hmult
  simp only [mem_edgeSet,if_pos huv] at hmult
  omega

end OverfullWork.GeneralRegularization
