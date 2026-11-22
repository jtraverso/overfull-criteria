module

public import OverfullWork.GeneralSparseInternalCompletion

@[expose] public section


/-! # Exceptional Hall completion with actual weighted blocked mass -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Occupied weight is exactly the weighted degree load of a colour.
The ambient weights M are fixed independently of later copy deletions. -/
theorem EdgeColoring.blocked_mass_eq_weighted_degree {H : MultiGraph V} {k : ℕ}
    (C : H.EdgeColoring k) (M : MultiGraph V) (x : V) (T : Finset V) (i : Fin k) :
    M.degreeInto (T\C.missingSet T i) x=
      ∑ v∈T,M.mult s(x,v)*(C.colourGraph i).degree v := by
  have he : T\C.missingSet T i=T.filter (fun v => (C.colourGraph i).degree v≠0) := by
    ext v
    simp only [mem_sdiff,EdgeColoring.missingSet,mem_filter]
    tauto
  rw [he]
  unfold degreeInto
  rw [sum_filter]
  apply sum_congr rfl
  intro v hv
  have hd:=C.colourGraph_degree_le_one i v
  by_cases hz : (C.colourGraph i).degree v=0
  · simp [hz]
  · have hone : (C.colourGraph i).degree v=1:=by omega
    simp [hone]

/-- A weighted budget for the blocked subset forces a positive-mass
neighbour in the remaining set. No multiplicity cap is used. -/
theorem exists_neighbour_of_weight_budget (M : MultiGraph V) (T W : Finset V) (x : V)
    (hW : W⊆T) (hroom : M.degreeInto (T\W) x<M.degreeInto T x) :
    ∃ w∈W,0<M.mult s(x,w) := by
  classical
  by_contra hn
  have hz : ∀ w∈W,M.mult s(x,w)=0 := by
    intro w hw
    by_contra hm
    exact hn ⟨w,hw,by omega⟩
  have he : M.degreeInto (T\W) x=M.degreeInto T x := by
    unfold degreeInto
    apply sum_subset sdiff_subset
    intro w hw hnot
    have hwW : w∈W:=by simpa only [mem_sdiff,hw,true_and,not_not] using hnot
    exact hz w hwW
  omega

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- A small fixed internal matching can be completed using available
crossing copies. One exceptional vertex may have parallel edges. -/
theorem exists_free_colour_matching_weighted_available (P : M.PartialColouring k) (S : Finset V) (x : V)
    (m D a b : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x b)
    (hcover : P.CoversInternal S) (hroom : m+2*k+4*a+2*b+2≤2*D)
    (i : Fin k)
    (hcentre : k+P.available.degreeInto (Sᶜ\P.colouring.missingSet Sᶜ i) x<D) (hcx : (P.colouring.colourGraph i).degree x=0)
    (hcut : (P.colouring.colourGraph i).cutSize S=0)
    (hbal : (P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ)
    (hsmall : (P.colouring.colourGraph i).edgesWithin S≤a) :
    ∃ J : MultiGraph V,(∀ e,J.mult e≤P.available.mult e) ∧
      (∀ z,J.degree z=if (P.colouring.colourGraph i).degree z=0 then 1 else 0) ∧
      ∀ u v,(u∈S ↔ v∈S) → J.mult s(u,v)=0 := by
  classical
  let U:=P.colouring.missingSet S i
  let W:=P.colouring.missingSet Sᶜ i
  let N : V → V → Prop:=fun u v => 0<P.available.mult s(u,v)
  have hU : U⊆S:=filter_subset _ _
  have hW : W⊆Sᶜ:=filter_subset _ _
  have heq : U.card=W.card := by
    have hA:=P.colouring.missing_internal_cut_identity S i
    have hB:=P.colouring.missing_internal_cut_identity Sᶜ i
    rw [cutSize_compl,hcut,←hbal,hSc] at hB
    rw [hcut,hS] at hA
    dsimp [U,W]
    omega
  have hUA : (S\U).card≤2*a := by
    have hid:=P.colouring.missing_internal_cut_identity S i
    rw [hcut,hS] at hid
    have hc:=card_sdiff_add_card_eq_card hU
    dsimp only [U] at hc ⊢
    omega
  have hWB : (Sᶜ\W).card≤2*a := by
    have hc:=card_sdiff_add_card_eq_card hW
    have hc':=card_sdiff_add_card_eq_card hU
    omega
  have hxU : x∈U:=mem_filter.mpr ⟨hx,hcx⟩
  have havail : ∀ e,P.available.mult e≤M.mult e:=fun e => Nat.sub_le _ _
  have hbudget:=P.crossing_degree_budget S D 0 hreg (fun z => by rw [P.covered_remainder_zero S hcover z])
  have hleft : ∀ z∈U,z≠x → D-k-2*a-b≤(W.filter (N z)).card := by
    intro z hz hzx
    have hzS:=hU hz
    have hb:=hbudget z
    rw [if_pos hzS] at hb
    have hc:=P.available.degreeInto_le_neighbours_add_budget Sᶜ z x b
      (M.parallelBudget_mono P.available x b havail hstar) hzx
    have hl:=OverfullWork.ShortAugmentSearch.neighbours_lost Sᶜ W hW (N z)
    change (P.available.neighboursInto Sᶜ z).card≤(W.filter (N z)).card+(Sᶜ\W).card at hl
    omega
  have hright : ∀ z∈W,D-k-2*a-b≤(U.filter (fun w => N w z)).card := by
    intro z hz
    have hzS : z∉S:=mem_compl.mp (hW hz)
    have hzx : z≠x:=fun hh => hzS (hh ▸ hx)
    have hb:=hbudget z
    rw [if_neg hzS] at hb
    have hc:=P.available.degreeInto_le_neighbours_add_budget S z x b
      (M.parallelBudget_mono P.available x b havail hstar) hzx
    have hl:=OverfullWork.ShortAugmentSearch.neighbours_lost S U hU (N z)
    change (P.available.neighboursInto S z).card≤(U.filter (N z)).card+(S\U).card at hl
    have he : (U.filter (N z)).card=(U.filter (fun w => N w z)).card := by
      congr 1
      ext w
      simp only [mem_filter,N,Sym2.eq_swap]
    rw [he] at hl
    omega
  have hxfree : ∃ w : W,N x w := by
    have hb:=hbudget x
    rw [if_pos hx] at hb
    have hroomW : P.available.degreeInto (Sᶜ\W) x<P.available.degreeInto Sᶜ x := by
      change k+P.available.degreeInto (Sᶜ\W) x<D at hcentre
      omega
    obtain ⟨w,hw,hpos⟩:=P.available.exists_neighbour_of_weight_budget Sᶜ W x hW hroomW
    exact ⟨⟨w,hw⟩,hpos⟩
  have hsize : Fintype.card W≤2*(D-k-2*a-b) := by
    have hh:=card_le_card hW
    rw [hSc] at hh
    simpa only [Fintype.card_coe] using (show W.card≤2*(D-k-2*a-b) by omega)
  obtain ⟨f,hf⟩:=OverfullWork.DenseHall.exists_matching_exceptional
    (fun u : U => fun v : W => N u v) ⟨x,hxU⟩ (D-k-2*a-b)
    (by simpa only [Fintype.card_coe] using heq) hsize hxfree
    (fun z hzx => by
      have he : z.val≠x:=fun hh => hzx (Subtype.ext hh)
      have hc:=OverfullWork.DenseHall.subtype_filter_card W (N z)
      rw [hc]
      convert hleft z z.2 he using 1 <;> congr 1 <;> (ext w; simp only [mem_filter]))
    (fun z => by
      have hc:=OverfullWork.DenseHall.subtype_filter_card U (fun w => N w z)
      rw [hc]
      convert hright z z.2 using 1 <;> congr 1 <;> (ext w; simp only [mem_filter]))
  have hdis : Disjoint U W:=Finset.disjoint_left.mpr (fun _ hu hw => (mem_compl.mp (hW hw)) (hU hu))
  refine ⟨pairingMatching U W hdis f,pairingMatching_le U W hdis f P.available hf,?_,?_⟩
  · intro z
    rw [pairingMatching_degree]
    have hh : z∈U ∨ z∈W ↔ (P.colouring.colourGraph i).degree z=0 := by
      dsimp only [U,W,EdgeColoring.missingSet]
      simp only [mem_filter,mem_compl]
      tauto
    simp only [hh]
  · intro u v huv
    have hz : (pairingMatching U W hdis f).mult s(u,v)=0 := by
      change (if s(u,v)∈(pairingGraph U W hdis f).edgeSet then 1 else 0)=0
      apply if_neg
      rw [SimpleGraph.mem_edgeSet]
      intro hadj
      rcases hadj with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
      · exact (mem_compl.mp (hW (f a).2)) (huv.mp (hU a.2))
      · exact (mem_compl.mp (hW (f a).2)) (huv.mpr (hU a.2))
    exact hz

/-- A bound on the original blocked weights is deletion-stable and
suffices to construct the exceptional Hall matching. -/
theorem exists_free_colour_matching_weighted_original (P : M.PartialColouring k)
    (S : Finset V) (x : V) (m D a b L : ℕ)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x b)
    (hcover : P.CoversInternal S) (hroom : m+2*k+4*a+2*b+2≤2*D)
    (i : Fin k) (hcentre : k+L<D)
    (hblocked : M.degreeInto (Sᶜ\P.colouring.missingSet Sᶜ i) x≤L)
    (hcx : (P.colouring.colourGraph i).degree x=0)
    (hcut : (P.colouring.colourGraph i).cutSize S=0)
    (hbal : (P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ)
    (hsmall : (P.colouring.colourGraph i).edgesWithin S≤a) :
    ∃ J : MultiGraph V,(∀ e,J.mult e≤P.available.mult e) ∧
      (∀ z,J.degree z=if (P.colouring.colourGraph i).degree z=0 then 1 else 0) ∧
      ∀ u v,(u∈S ↔ v∈S) → J.mult s(u,v)=0 := by
  have hw : P.available.degreeInto (Sᶜ\P.colouring.missingSet Sᶜ i) x≤
      M.degreeInto (Sᶜ\P.colouring.missingSet Sᶜ i) x := by
    unfold degreeInto
    exact sum_le_sum (fun _ _ => Nat.sub_le _ _)
  exact P.exists_free_colour_matching_weighted_available S x m D a b hS hSc hx hreg hstar
    hcover hroom i (by omega) hcx hcut hbal hsmall

end PartialColouring
/-- Complete small internal classes simultaneously. The available graph
is recomputed after every colour; the bounds include the entire palette. -/
theorem exists_sparse_internal_cover_weighted_centre (M : MultiGraph V) (S : Finset V) (x : V)
    (m D a k b L : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x b)
    (hroom : m+2*k+4*a+2*b+2≤2*D) (hcentre : k+L<D)
    (C : (M.internalPart S).EdgeColoring k)
    (hcx : ∀ i,(C.colourGraph i).degree x=0)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hsmall : ∀ i,(C.colourGraph i).edgesWithin S≤a)
    (hblocked : ∀ i,M.degreeInto (Sᶜ\C.missingSet Sᶜ i) x≤L) :
    ∃ H : MultiGraph V,(∀ e,H.mult e≤M.mult e) ∧ H.IsRegularOfDegree k ∧
      Nonempty (H.EdgeColoring k) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  classical
  have hprocess : ∀ T : Finset (Fin k),∃ P : M.PartialColouring k,
      P.CoversInternal S ∧
      (∀ j∈T,(P.colouring.colourGraph j).IsRegularOfDegree 1) ∧
      (∀ j,j∉T → P.colouring.colourGraph j=C.colourGraph j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨PartialColouring.internalSeed S C,?_,by simp,fun _ _ => rfl⟩
      intro u v huv
      exact M.internalPart_covers S u v huv
    | @insert i T hi ih =>
      obtain ⟨P,hcover,hfilled,hunfilled⟩:=ih
      have hCi:=hunfilled i hi
      have hmiss : P.colouring.missingSet Sᶜ i=C.missingSet Sᶜ i := by
        ext v
        simp only [EdgeColoring.missingSet,mem_filter]
        rw [hCi]
      have hblockedP : M.degreeInto (Sᶜ\P.colouring.missingSet Sᶜ i) x≤L := by
        rw [hmiss]
        exact hblocked i
      obtain ⟨J,hJ,hdegree,hcross⟩:=P.exists_free_colour_matching_weighted_original S x m D a b L hS hSc hx hreg hstar
        hcover hroom i hcentre hblockedP (by rw [hCi];exact hcx i)
        (by rw [hCi];exact C.internal_colour_cut_zero S i)
        (by rw [hCi];exact hbal i) (by rw [hCi];exact hsmall i)
      have hp : ∀ z,(P.colouring.colourGraph i).degree z+J.degree z≤1 := by
        intro z
        rw [hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      let Q:=P.addMatching i J hJ hp
      have ho : ∀ j,j≠i → Q.colouring.colourGraph j=P.colouring.colourGraph j:=
        P.addMatching_other i J hJ hp
      have hselected : ∀ z,(Q.colouring.colourGraph i).degree z=1 := by
        intro z
        rw [P.addMatching_selected,degree_addCopies,hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      refine ⟨Q,?_,?_,?_⟩
      · intro u v huv
        change P.graph.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
        rw [hcover u v huv,hcross u v huv,Nat.add_zero]
      · intro j hj
        rcases mem_insert.mp hj with hj|hj
        · subst j
          exact hselected
        · have hji : j≠i:=fun he => hi (he ▸ hj)
          rw [ho j hji]
          exact hfilled j hj
      · intro j hj
        simp only [mem_insert,not_or] at hj
        rw [ho j hj.1]
        exact hunfilled j hj.2
  obtain ⟨P,hcover,hall,_⟩:=hprocess univ
  have hf : P.colouring.IsFactorization:=fun v i => hall i (mem_univ i) v
  exact ⟨P.graph,P.le,P.regular_of_factorization hf,⟨P.colouring⟩,hcover⟩


/-- External weights may dominate the ambient centre row. They can be
fixed before a previous phase of copy deletions, so the same weighted
colouring estimate remains valid for the current residual. -/
theorem exists_sparse_internal_cover_weighted_majorant (M : MultiGraph V) (S : Finset V) (x : V)
    (m D a k b L : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x b)
    (hroom : m+2*k+4*a+2*b+2≤2*D) (hcentre : k+L<D)
    (C : (M.internalPart S).EdgeColoring k)
    (hcx : ∀ i,(C.colourGraph i).degree x=0)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hsmall : ∀ i,(C.colourGraph i).edgesWithin S≤a)
    (w : V → ℕ) (hdom : ∀ v,M.mult s(x,v)≤w v)
    (hload : ∀ i,(∑ v∈Sᶜ,w v*(C.colourGraph i).degree v)≤L) :
    ∃ H : MultiGraph V,(∀ e,H.mult e≤M.mult e) ∧ H.IsRegularOfDegree k ∧
      Nonempty (H.EdgeColoring k) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  apply M.exists_sparse_internal_cover_weighted_centre S x m D a k b L
    hS hSc hx hreg hstar hroom hcentre C hcx hbal hsmall
  intro i
  rw [C.blocked_mass_eq_weighted_degree M x Sᶜ i]
  have hh:=sum_le_sum (s:=Sᶜ) (fun v _ => Nat.mul_le_mul_right ((C.colourGraph i).degree v) (hdom v))
  exact hh.trans (hload i)

end SimpleGraph.MultiGraph
