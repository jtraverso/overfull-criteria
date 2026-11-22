module

public import OverfullWork.AlmostOverfullOriginalGeometry

@[expose] public section


/-! # One pair move normalizes a critical almost-overfull complement

Moving a heavy pair from the complement into the odd set decreases its
actual original-graph budget by at least four. If B < Delta+4, the remaining
complement has total degree below Delta+2, hence no heavy pair. Critical VAL
then makes that complement independent. No residual overfullness or future
layer is an input or an output of this normalization.
-/
namespace OverfullWork.CriticalAlmostPairNormalization
open SimpleGraph Finset OddCutDeficit AlmostOverfullLayerCompatibility
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Two distinct members spend their actual degrees in the set's degree sum. -/
theorem pair_degree_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (u v : V) (hu : u∈Y) (hv : v∈Y) (hne : u≠v) :
    G.degree u+G.degree v≤∑z∈Y,G.degree z := by
  have hs : ({u,v}:Finset V)⊆Y := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact hu
    · exact mem_singleton.mp hz ▸ hv
  have hh:=(sum_le_sum_of_subset_of_nonneg hs (fun _ _ _=>Nat.zero_le _) :
    (∑z∈({u,v}:Finset V),G.degree z)≤∑z∈Y,G.degree z)
  simpa [hne] using hh

/-- Exact degree sum after transferring two vertices into X. -/
theorem complement_sum_insert_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (hu : u∈Xᶜ) (hv : v∈Xᶜ) (hne : u≠v) :
    (∑z∈(insert u (insert v X))ᶜ,G.degree z)+G.degree u+G.degree v=
      ∑z∈Xᶜ,G.degree z := by
  have he : (insert u (insert v X))ᶜ=(Xᶜ.erase u).erase v := by
    ext z
    simp only [mem_compl,mem_insert,mem_erase]
    tauto
  have hv' : v∈Xᶜ.erase u := mem_erase.mpr ⟨hne.symm,hv⟩
  have h1:=sum_erase_add Xᶜ (fun z=>G.degree z) hu
  have h2:=sum_erase_add (Xᶜ.erase u) (fun z=>G.degree z) hv'
  rw [he]
  omega

/-- Both cardinalities change by exactly two, preserving the odd parity. -/
theorem insert_pair_cardinalities (X : Finset V) (u v : V)
    (hu : u∈Xᶜ) (hv : v∈Xᶜ) (hne : u≠v) :
    (insert u (insert v X)).card=X.card+2 ∧
      (insert u (insert v X))ᶜ.card+2=Xᶜ.card := by
  have huX:=mem_compl.mp hu
  have hvX:=mem_compl.mp hv
  have hu' : u∉insert v X := by simp only [mem_insert];tauto
  have hc : (insert u (insert v X)).card=X.card+2 := by
    rw [card_insert_of_notMem hu',card_insert_of_notMem hvX]
  have htotal:=card_add_card_compl X
  have htotal':=card_add_card_compl (insert u (insert v X))
  exact ⟨hc,by omega⟩

/-- The exact original-graph budget identity underlying the pair move. -/
theorem budget_insert_pair_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (hu : u∈Xᶜ) (hv : v∈Xᶜ) (hne : u≠v) :
    (deficitMass G G.maxDegree (insert u (insert v X))+
      (∑z∈(insert u (insert v X))ᶜ,G.degree z))+2*(G.degree u+G.degree v)=
      (deficitMass G G.maxDegree X+(∑z∈Xᶜ,G.degree z))+2*G.maxDegree := by
  have huX:=mem_compl.mp hu
  have hvX:=mem_compl.mp hv
  have hu' : u∉insert v X := by simp only [mem_insert];tauto
  have hd : deficitMass G G.maxDegree (insert u (insert v X))=
      (G.maxDegree-G.degree u)+(G.maxDegree-G.degree v)+deficitMass G G.maxDegree X := by
    unfold deficitMass
    rw [sum_insert hu',sum_insert hvX]
    omega
  have hs:=complement_sum_insert_pair G X u v hu hv hne
  have hdu:=G.degree_le_maxDegree u
  have hdv:=G.degree_le_maxDegree v
  omega

/-- A heavy pair improves the actual budget by four units. -/
theorem budget_drops_four_of_heavy_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (u v : V) (hu : u∈Xᶜ) (hv : v∈Xᶜ) (hne : u≠v)
    (hheavy : G.maxDegree+2≤G.degree u+G.degree v) :
    deficitMass G G.maxDegree (insert u (insert v X))+
      (∑z∈(insert u (insert v X))ᶜ,G.degree z)+4≤
      deficitMass G G.maxDegree X+(∑z∈Xᶜ,G.degree z) := by
  have hh:=budget_insert_pair_identity G X u v hu hv hne
  omega

/-- Critical VAL excludes every edge within a set with no heavy pair. -/
theorem independent_of_no_heavy_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
    (hlight : ∀u∈Y,∀v∈Y,u≠v → G.degree u+G.degree v<G.maxDegree+2) :
    G.IsIndepSet (Y:Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv hne huv
  have hh:=hlight u hu v hv hne
  have hval:=Overfull.deg_add hc huv
  omega

/-- Either X already has no heavy complementary pair, or transferring one
such pair suffices. The output is actual, contains X and keeps its odd parity. -/
theorem normalize_odd_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (X : Finset V) (hodd : Odd X.card)
    (B : ℕ) (hB : B<G.maxDegree+4)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    ∃X' : Finset V,X⊆X' ∧ Odd X'.card ∧ X'ᶜ.card≤Xᶜ.card ∧
      deficitMass G G.maxDegree X'+(∑v∈X'ᶜ,G.degree v)≤G.maxDegree+B ∧
      (∀u∈X'ᶜ,∀v∈X'ᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2) ∧
      G.IsIndepSet (X'ᶜ:Set V) := by
  classical
  by_cases hh : ∃u∈Xᶜ,∃v∈Xᶜ,u≠v ∧ G.maxDegree+2≤G.degree u+G.degree v
  · obtain ⟨u,hu,v,hv,hne,hheavy⟩:=hh
    let X':=insert u (insert v X)
    obtain ⟨hcard,hcompl⟩:=insert_pair_cardinalities X u v hu hv hne
    have hdrop:=budget_drops_four_of_heavy_pair G X u v hu hv hne hheavy
    have hsum:=complement_sum_insert_pair G X u v hu hv hne
    have hsmall : (∑z∈X'ᶜ,G.degree z)+2≤B := by dsimp only [X'];omega
    have hlight : ∀s∈X'ᶜ,∀t∈X'ᶜ,s≠t → G.degree s+G.degree t<G.maxDegree+2 := by
      intro s hs t ht hst
      have hpair:=pair_degree_sum_le G X'ᶜ s t hs ht hst
      omega
    refine ⟨X',?_,?_,?_,?_,hlight,?_⟩
    · exact fun z hz=>mem_insert_of_mem (mem_insert_of_mem hz)
    · obtain ⟨k,hk⟩:=hodd
      exact ⟨k+1,by dsimp only [X'];omega⟩
    · dsimp only [X'];omega
    · dsimp only [X'];omega
    · simpa only [Finset.coe_compl] using independent_of_no_heavy_pair G hc X'ᶜ hlight
  · have hlight : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2 := by
      intro u hu v hv hne
      by_contra hnot
      exact hh ⟨u,hu,v,hv,hne,by omega⟩
    refine ⟨X,subset_refl _,hodd,le_refl _,hbudget,hlight,?_⟩
    simpa only [Finset.coe_compl] using independent_of_no_heavy_pair G hc Xᶜ hlight

/-- A supplied original almost-overfull witness is normalized without a
residual graph hypothesis or an assumed independent complement. -/
theorem normalize_almost_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (B : ℕ) (hB : B<G.maxDegree+4)
    (halmost : HasOddAlmostOverfullSet G B) :
    ∃X : Finset V,Odd X.card ∧
      deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B ∧
      (∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2) ∧
      G.IsIndepSet (Xᶜ:Set V) := by
  obtain ⟨X,hodd,hbudget⟩:=halmost
  obtain ⟨X',_,hodd',_,hbudget',hlight,hind⟩:=normalize_odd_set G hc X hodd B hB hbudget
  exact ⟨X',hodd',hbudget',hlight,hind⟩

omit [DecidableEq V] in
/-- At the sparse integer scales used by the construction and stop
localization, the required pair-normalization budget is automatic. -/
theorem sparse_budget_lt_maxDegree_add_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (qR qS : ℕ) (hqR : 2≤qR) (hqS : 2≤qS) (_hn : 16≤Fintype.card V)
    (hnD : Fintype.card V≤2*G.maxDegree) :
    2*(Fintype.card V/(4096*qR^2))+2+8*(Fintype.card V/(4096*qS^2))<G.maxDegree+4 := by
  let n:=Fintype.card V
  let kR:=n/(4096*qR^2)
  let kS:=n/(4096*qS^2)
  have hkR : 64*kR≤n :=
    (Nat.mul_le_mul_right kR (show 64≤4096*qR^2 by nlinarith [sq_nonneg (qR:ℤ)])).trans
      (Nat.mul_div_le n (4096*qR^2))
  have hkS : 64*kS≤n :=
    (Nat.mul_le_mul_right kS (show 64≤4096*qS^2 by nlinarith [sq_nonneg (qS:ℤ)])).trans
      (Nat.mul_div_le n (4096*qS^2))
  change 2*kR+2+8*kS<G.maxDegree+4
  omega

/-- Uniform normalization. The threshold is independent of the two supplied
integer scales and of the graph and witness. Both graph-order parities apply. -/
theorem above_half_normalize_almost_set (ε : ℝ) (_hε : 0<ε) :
    ∃N : ℕ,∀qR qS : ℕ,2≤qR → 2≤qS →
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let B:=2*(Fintype.card V/(4096*qR^2))+2+8*(Fintype.card V/(4096*qS^2))
        HasOddAlmostOverfullSet G B →
        ∃X : Finset V,Odd X.card ∧
          deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B ∧
          (∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2) ∧
          G.IsIndepSet (Xᶜ:Set V) := by
  refine ⟨16,?_⟩
  intro qR qS hqR hqS V _ _ G _ hn hc hdense
  dsimp only
  intro halmost
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he:0≤ε*(Fintype.card V:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  exact normalize_almost_set G hc _ (sparse_budget_lt_maxDegree_add_four G qR qS hqR hqS hn hnD) halmost

end OverfullWork.CriticalAlmostPairNormalization
