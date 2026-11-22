module

public import OverfullWork.NearTightOddSetGeometry
public import OverfullWork.MaximumMatchingPeeling

@[expose] public section


/-! # Star geometry at a residual overfull odd set

Finite counting from the star part of CMS, Section 4, Claim 4.2(4).
The degree-lowering hypothesis on the actual residue is explicit:
removing a graph of maximum degree two alone does not imply it.
No existence of a removable layer, layout or factorization is assumed.
-/
namespace OverfullWork.TrimmingResidualOddGeometry
open SimpleGraph Finset PrunedCore OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000

/-- A vertex in the complement has at most |Y|-1 neighbours there. -/
theorem degree_add_one_le_boundary_add_complement (R : SimpleGraph V)
    [DecidableRel R.Adj] (X : Finset V) (v : V) (hv : v∈Xᶜ) :
    R.degree v+1≤neighboursIn R X v+Xᶜ.card := by
  have hs:=card_filter_add_card_filter_not (s:=R.neighborFinset v) (fun w => w∈X)
  have hsub : (R.neighborFinset v).filter (fun w => w∉X)⊆Xᶜ.erase v := by
    intro w hw
    obtain ⟨hn,hm⟩:=mem_filter.mp hw
    exact mem_erase.mpr ⟨((mem_neighborFinset R v w).mp hn).ne.symm,mem_compl.mpr hm⟩
  have hc:=card_le_card hsub
  rw [card_erase_of_mem hv] at hc
  rw [card_neighborFinset_eq_degree] at hs
  change neighboursIn R X v+_=R.degree v at hs
  have hp : 0<Xᶜ.card:=card_pos.mpr ⟨v,hv⟩
  omega

/-- The degrees of selected complementary vertices spend the same cut;
the only additional cost is |A|(|Y|+1), including the two lost edges. -/
theorem selected_degree_sum_le_cut_add (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (hH : H.maxDegree≤2) (X A : Finset V) (hA : A⊆Xᶜ) :
    (∑v∈A,G.degree v)≤cutEdges (G\H) X+A.card*(Xᶜ.card+1) := by
  have hrow : ∀v∈A,G.degree v≤neighboursIn (G\H) X v+(Xᶜ.card+1) := by
    intro v hv
    have hdeg:=MaximumMatching.degree_sdiff_add_of_le G H hHG v
    have hh:=(H.degree_le_maxDegree v).trans hH
    have hb:=degree_add_one_le_boundary_add_complement (G\H) X v (hA hv)
    omega
  have hc:=MaximumOddCutPacking.cut_eq_sum_neighboursIn (G\H) X Xᶜ
    disjoint_compl_right (fun _ _ v _ => by by_cases hv:v∈X <;> simp_all)
  have hsum : (∑v∈A,neighboursIn (G\H) X v)≤cutEdges (G\H) X := by
    rw [hc]
    exact sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => Nat.zero_le _)
  calc
    _ ≤ ∑v∈A,(neighboursIn (G\H) X v+(Xᶜ.card+1)) := sum_le_sum hrow
    _ = (∑v∈A,neighboursIn (G\H) X v)+A.card*(Xᶜ.card+1) := by
      rw [sum_add_distrib];simp
    _ ≤ _ := Nat.add_le_add_right hsum _

/-- Actual degree lowering plus residual overfullness forces a small cut. -/
theorem residual_overfull_cut_bound (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hD : 2≤G.maxDegree) (hR : ∀v,(G\H).degree v≤G.maxDegree-2)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\H) X) :
    cutEdges (G\H) X+3≤G.maxDegree := by
  have hi:=internal_cut_deficit_identity (G\H) (G.maxDegree-2) hR X
  obtain ⟨m,hm⟩:=hodd
  have hh : X.card/2=m := by omega
  rw [hm] at hi
  rw [hh] at hof
  have hsub : G.maxDegree-2+2=G.maxDegree := by omega
  nlinarith

/-- Two independent original edges in the small complement would spend
more boundary than residual overfullness permits. -/
theorem no_two_independent_edges (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (hH : H.maxDegree≤2) (hD : 2≤G.maxDegree)
    (hR : ∀v,(G\H).degree v≤G.maxDegree-2) (b : ℕ)
    (hweak : ∀u v,G.Adj u v → G.maxDegree-b≤G.degree u+G.degree v)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\H) X)
    (hroom : 3*b+6*Xᶜ.card+2≤G.maxDegree)
    {a c d e : V} (ha : a∈Xᶜ) (hc : c∈Xᶜ) (hd : d∈Xᶜ) (he : e∈Xᶜ)
    (hac : G.Adj a c) (hde : G.Adj d e)
    (had : a≠d) (hae : a≠e) (hcd : c≠d) (hce : c≠e) : False := by
  let A : Finset V:={a,c,d,e}
  have hA : A⊆Xᶜ := by intro v hv;simp only [A,mem_insert,mem_singleton] at hv;rcases hv with rfl|rfl|rfl|rfl <;> assumption
  have hs:=selected_degree_sum_le_cut_add G H hHG hH X A hA
  have hcard : A.card=4 := by simp [A,hac.ne,hde.ne,had,hae,hcd,hce]
  have hsum : (∑v∈A,G.degree v)=G.degree a+G.degree c+G.degree d+G.degree e := by
    simp [A,hac.ne,hde.ne,had,hae,hcd,hce,Nat.add_assoc]
  rw [hcard,hsum] at hs
  have hcut:=residual_overfull_cut_bound G H hD hR X hodd hof
  have h1:=hweak a c hac
  have h2:=hweak d e hde
  omega

/-- The same cut budget excludes a triangle in the original complement. -/
theorem no_triangle (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (hH : H.maxDegree≤2) (hD : 2≤G.maxDegree)
    (hR : ∀v,(G\H).degree v≤G.maxDegree-2) (b : ℕ)
    (hweak : ∀u v,G.Adj u v → G.maxDegree-b≤G.degree u+G.degree v)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\H) X)
    (hroom : 3*b+6*Xᶜ.card+2≤G.maxDegree)
    {a c d : V} (ha : a∈Xᶜ) (hc : c∈Xᶜ) (hd : d∈Xᶜ)
    (hac : G.Adj a c) (hcd : G.Adj c d) (hda : G.Adj d a) : False := by
  let A : Finset V:={a,c,d}
  have hA : A⊆Xᶜ := by intro v hv;simp only [A,mem_insert,mem_singleton] at hv;rcases hv with rfl|rfl|rfl <;> assumption
  have hs:=selected_degree_sum_le_cut_add G H hHG hH X A hA
  have hcard : A.card=3 := by simp [A,hac.ne,hcd.ne,hda.ne.symm]
  have hsum : (∑v∈A,G.degree v)=G.degree a+G.degree c+G.degree d := by
    simp [A,hac.ne,hcd.ne,hda.ne.symm,Nat.add_assoc]
  rw [hcard,hsum] at hs
  have hcut:=residual_overfull_cut_bound G H hD hR X hodd hof
  have h1:=hweak a c hac
  have h2:=hweak c d hcd
  have h3:=hweak d a hda
  omega

/-- Pairwise-intersecting edges without a triangle all meet one vertex. -/
theorem exists_common_incident_of_no_independent_no_triangle (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y : Finset V) (hY : Y.Nonempty)
    (hp : ∀a∈Y,∀c∈Y,∀d∈Y,∀e∈Y,G.Adj a c → G.Adj d e →
      a=d ∨ a=e ∨ c=d ∨ c=e)
    (ht : ∀a∈Y,∀c∈Y,∀d∈Y,G.Adj a c → G.Adj c d → G.Adj d a → False) :
    ∃v∈Y,∀a∈Y,∀c∈Y,G.Adj a c → a=v ∨ c=v := by
  by_cases hex : ∃a∈Y,∃c∈Y,G.Adj a c
  · obtain ⟨a,ha,c,hc,hac⟩:=hex
    by_cases hstar : ∀u∈Y,∀v∈Y,G.Adj u v → u=a ∨ v=a
    · exact ⟨a,ha,hstar⟩
    · push Not at hstar
      obtain ⟨u,hu,v,hv,huv,hua,hva⟩:=hstar
      have hmeet:=hp a ha c hc u hu v hv hac huv
      have hcw : ∃w∈Y,G.Adj c w ∧ w≠a := by
        rcases hmeet with h|h|h|h
        · exact False.elim (hua h.symm)
        · exact False.elim (hva h.symm)
        · subst u;exact ⟨v,hv,huv,hva⟩
        · subst v;exact ⟨u,hu,huv.symm,hua⟩
      obtain ⟨w,hw,hcw,hwa⟩:=hcw
      refine ⟨c,hc,?_⟩
      intro z hz t ht' hzt
      by_contra hnot
      have hzc : z≠c := by intro h;exact hnot (Or.inl h)
      have htc : t≠c := by intro h;exact hnot (Or.inr h)
      have h1:=hp a ha c hc z hz t ht' hac hzt
      have h2:=hp c hc w hw z hz t ht' hcw hzt
      have hza : z=a ∨ t=a := by rcases h1 with h|h|h|h;exact Or.inl h.symm;exact Or.inr h.symm;exact False.elim (hzc h.symm);exact False.elim (htc h.symm)
      have hzw : z=w ∨ t=w := by rcases h2 with h|h|h|h;exact False.elim (hzc h.symm);exact False.elim (htc h.symm);exact Or.inl h.symm;exact Or.inr h.symm
      rcases hza with hza|hta
      · rcases hzw with hzw|htw
        · exact hwa (hzw.symm.trans hza)
        · have haw : G.Adj a w := by simpa only [hza,htw] using hzt
          exact ht a ha c hc w hw hac hcw haw.symm
      · rcases hzw with hzw|htw
        · have hwa' : G.Adj w a := by simpa only [hzw,hta] using hzt
          exact ht a ha c hc w hw hac hcw hwa'
        · exact hwa (htw.symm.trans hta)
  · obtain ⟨v,hv⟩:=hY
    refine ⟨v,hv,?_⟩
    intro a ha c hc hac
    exact False.elim (hex ⟨a,ha,c,hc,hac⟩)

/-- The original graph induced by the nonempty residual complement is
a star, including the possibility that it has no edges. -/
theorem complement_edges_have_common_vertex (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (hH : H.maxDegree≤2) (hD : 2≤G.maxDegree)
    (hR : ∀v,(G\H).degree v≤G.maxDegree-2) (b : ℕ)
    (hweak : ∀u v,G.Adj u v → G.maxDegree-b≤G.degree u+G.degree v)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\H) X)
    (hroom : 3*b+6*Xᶜ.card+2≤G.maxDegree) (hY : Xᶜ.Nonempty) :
    ∃v∈Xᶜ,∀a∈Xᶜ,∀c∈Xᶜ,G.Adj a c → a=v ∨ c=v := by
  apply exists_common_incident_of_no_independent_no_triangle G Xᶜ hY
  · intro a ha c hc d hd e he hac hde
    by_contra hn
    have had : a≠d := by tauto
    have hae : a≠e := by tauto
    have hcd : c≠d := by tauto
    have hce : c≠e := by tauto
    exact no_two_independent_edges G H hHG hH hD hR b hweak X hodd hof hroom
      ha hc hd he hac hde had hae hcd hce
  · intro a ha c hc d hd hac hcd hda
    exact no_triangle G H hHG hH hD hR b hweak X hodd hof hroom ha hc hd hac hcd hda

end OverfullWork.TrimmingResidualOddGeometry
