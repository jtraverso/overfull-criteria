module

public import OverfullWork.AlmostOverfullLayerCompatibility

@[expose] public section


/-! # Actual degree-order normalization of an independent complement

A minimum-weight admissible set has no degree inversion with its
complement: exchanging an inverted pair preserves the strict pair bound
and lowers the finite objective. Criticality then proves independence.
The exact budget identity shows that this construction cannot increase
the original almost-overfull budget.
-/
namespace OverfullWork.DegreeOrderedIndependentCut
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

omit [Fintype V] in
/-- Replacing one selected vertex by a strictly lighter vertex preserves
every strict pair-weight bound. -/
theorem pair_bound_insert_erase (d : V → ℕ) (K : ℕ) (Y : Finset V)
    (hpair : ∀u∈Y,∀v∈Y,u≠v → d u+d v<K)
    {y x : V} (hy : y∈Y) (hxy : d x<d y) :
    ∀u∈insert x (Y.erase y),∀v∈insert x (Y.erase y),u≠v → d u+d v<K := by
  intro u hu v hv huv
  rcases mem_insert.mp hu with rfl|hu
  · rcases mem_insert.mp hv with rfl|hv
    · exact False.elim (huv rfl)
    · obtain ⟨hvy,hvY⟩:=mem_erase.mp hv
      have hh:=hpair y hy v hvY hvy.symm
      omega
  · obtain ⟨huy,huY⟩:=mem_erase.mp hu
    rcases mem_insert.mp hv with rfl|hv
    · have hh:=hpair u huY y hy huy
      omega
    · obtain ⟨_,hvY⟩:=mem_erase.mp hv
      exact hpair u huY v hvY huv

/-- Finite minimization constructs an ordered set of the same size,
without losing admissibility or increasing total weight. -/
theorem exists_ordered_subset (d : V → ℕ) (K : ℕ) (Y : Finset V)
    (hpair : ∀u∈Y,∀v∈Y,u≠v → d u+d v<K) :
    ∃Y' : Finset V,Y'.card=Y.card ∧
      (∀u∈Y',∀v∈Y',u≠v → d u+d v<K) ∧
      (∑v∈Y',d v)≤∑v∈Y,d v ∧
      ∀y∈Y',∀x∉Y',d y≤d x := by
  let C : Finset (Finset V):=univ.filter fun S =>
    S.card=Y.card ∧ ∀u∈S,∀v∈S,u≠v → d u+d v<K
  have hY:Y∈C:=mem_filter.mpr ⟨mem_univ _,rfl,hpair⟩
  obtain ⟨Y',hY',hmin⟩:=C.exists_min_image (fun S => ∑v∈S,d v) ⟨Y,hY⟩
  obtain ⟨hcard,hpairs⟩:=(mem_filter.mp hY').2
  refine ⟨Y',hcard,hpairs,hmin Y hY,?_⟩
  intro y hy x hx
  by_contra hn
  have hxy:d x<d y:=Nat.lt_of_not_ge hn
  let S:=insert x (Y'.erase y)
  have hxErase:x∉Y'.erase y:=fun h => hx (mem_erase.mp h).2
  have hScard:S.card=Y.card:=by
    rw [card_insert_of_notMem hxErase,card_erase_of_mem hy]
    have hp:0<Y'.card:=card_pos.mpr ⟨y,hy⟩
    omega
  have hSpair:∀u∈S,∀v∈S,u≠v → d u+d v<K:=
    pair_bound_insert_erase d K Y' hpairs hy hxy
  have hSC:S∈C:=mem_filter.mpr ⟨mem_univ _,hScard,hSpair⟩
  have hsumS:(∑v∈S,d v)=d x+∑v∈Y'.erase y,d v:=sum_insert hxErase
  have hsumY: (∑v∈Y'.erase y,d v)+d y=∑v∈Y',d v:=sum_erase_add Y' d hy
  have hminimal:=hmin S hSC
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The original degree function supplies the actual ordered partition. -/
theorem exists_degree_ordered_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V)
    (hpair : ∀u∈Y,∀v∈Y,u≠v → G.degree u+G.degree v<G.maxDegree+2) :
    ∃Y' : Finset V,Y'.card=Y.card ∧
      (∀u∈Y',∀v∈Y',u≠v → G.degree u+G.degree v<G.maxDegree+2) ∧
      (∑v∈Y',G.degree v)≤∑v∈Y,G.degree v ∧
      ∀y∈Y',∀x∉Y',G.degree y≤G.degree x :=
  exists_ordered_subset (fun v => G.degree v) (G.maxDegree+2) Y hpair

omit [DecidableEq V] in
/-- This exact identity avoids all truncated subtraction of degree sums. -/
theorem deficit_add_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    deficitMass G G.maxDegree X+(∑v∈X,G.degree v)=G.maxDegree*X.card := by
  rw [deficitMass,←sum_add_distrib]
  calc
    _ = ∑_v∈X,G.maxDegree := sum_congr rfl (fun v _ => Nat.sub_add_cancel (G.degree_le_maxDegree v))
    _ = _ := by simp [Nat.mul_comm]

/-- At a fixed cut size, the almost-budget is ordered by twice the
complementary degree sum. No graph modification is involved. -/
theorem budget_add_total_degree (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    (deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v))+(∑v:V,G.degree v)=
      G.maxDegree*X.card+2*(∑v∈Xᶜ,G.degree v) := by
  have hdef:=deficit_add_degree_sum G X
  have hsum:=sum_add_sum_compl X (fun v => G.degree v)
  omega

/-- Actual normalization of an almost-overfull cut: its odd side keeps
its size, its complement becomes degree-ordered and independent, and its
budget does not increase. -/
theorem exists_ordered_independent_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (X : Finset V) (hodd : Odd X.card)
    (hpair : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (B : ℕ) (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    ∃X' : Finset V,Odd X'.card ∧ X'ᶜ.card=Xᶜ.card ∧
      (∀y∈X'ᶜ,∀x∈X',G.degree y≤G.degree x) ∧
      (∀u∈X'ᶜ,∀v∈X'ᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2) ∧
      G.IsIndepSet (X'ᶜ : Set V) ∧
      deficitMass G G.maxDegree X'+(∑v∈X'ᶜ,G.degree v)≤
        deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) ∧
      deficitMass G G.maxDegree X'+(∑v∈X'ᶜ,G.degree v)≤G.maxDegree+B := by
  obtain ⟨Y,hYcard,hYpair,hYsum,hYorder⟩:=exists_degree_ordered_subset G Xᶜ hpair
  let X':=Yᶜ
  have hX'comp:X'ᶜ=Y:=compl_compl Y
  have hXcard:X'.card=X.card:=by
    have hcardX:X.card+Xᶜ.card=Fintype.card V:=by simp
    have hcardY:Y.card+Yᶜ.card=Fintype.card V:=by simp
    change Yᶜ.card=X.card
    omega
  have hInd:G.IsIndepSet (Y : Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv huv hAdj
    have hp:=hYpair u hu v hv huv
    have hval:=Overfull.deg_add hc hAdj
    omega
  have hnew:=budget_add_total_degree G X'
  have hold:=budget_add_total_degree G X
  rw [hXcard,hX'comp] at hnew
  have hnonincrease:
      deficitMass G G.maxDegree X'+(∑v∈X'ᶜ,G.degree v)≤
        deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) := by
    rw [hX'comp]
    omega
  refine ⟨X',by rwa [hXcard],by rwa [hX'comp],?_,?_,?_,hnonincrease,hnonincrease.trans hbudget⟩
  · intro y hy x hx
    rw [hX'comp] at hy
    exact hYorder y hy x (mem_compl.mp hx)
  · simpa only [hX'comp] using hYpair
  · simpa only [X',coe_compl,compl_compl] using hInd

end OverfullWork.DegreeOrderedIndependentCut
