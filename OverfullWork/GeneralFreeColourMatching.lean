module

public import OverfullWork.CentreControl
public import OverfullWork.FreeColourMatching

@[expose] public section


/-! # Exceptional Hall completion with arbitrary multiplicity and excess -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- A small fixed internal matching can be completed using available
crossing copies. One exceptional vertex may have parallel edges. -/
theorem exists_free_colour_matching_bounded (P : M.PartialColouring k) (S : Finset V) (x : V)
    (m D a μ b : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤μ) (hstar : M.HasParallelBudget x b)
    (hcover : P.CoversInternal S) (hroom : m+2*k+4*a+2*b+2≤2*D) (hcentre : k+2*μ*a<D)
    (i : Fin k) (hcx : (P.colouring.colourGraph i).degree x=0)
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
    have hc:=P.available.degreeInto_le_mul_neighbours Sᶜ x μ
      (fun w _ => (havail s(x,w)).trans (hmu s(x,w)))
    have hl:=OverfullWork.ShortAugmentSearch.neighbours_lost Sᶜ W hW (N x)
    change (P.available.neighboursInto Sᶜ x).card≤(W.filter (N x)).card+(Sᶜ\W).card at hl
    have hp : 0<(W.filter (N x)).card:=by
      by_contra hn
      have hz : (W.filter (N x)).card=0:=by omega
      have hnbr : (P.available.neighboursInto Sᶜ x).card≤2*a:=by omega
      have hm:=Nat.mul_le_mul_left μ hnbr
      nlinarith only [hb,hc,hm,hcentre]
    obtain ⟨w,hw⟩:=card_pos.mp hp
    exact ⟨⟨w,(mem_filter.mp hw).1⟩,(mem_filter.mp hw).2⟩
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

end PartialColouring
end SimpleGraph.MultiGraph
