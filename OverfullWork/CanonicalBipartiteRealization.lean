module

public import OverfullWork.LooplessRealization

@[expose] public section


/-! # Actual bipartite realization of balanced prescribed degrees

Pair the two finite sets of half-edges by a constructed equivalence.
Multiplicities count its actual edge fibres. This is the realization
step in the ordered degree-sequence construction of CMS Lemma 3.1.
-/
namespace OverfullWork.CanonicalBipartiteRealization
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

private theorem stub_fiber_card {A : Type*} [Fintype A] [DecidableEq A]
    (a : A→ℕ) (v : A) :
    (univ.filter fun z : Sigma (fun u=>Fin (a u))=>z.1=v).card=a v := by
  symm
  rw [←Fintype.card_fin (a v),←card_univ]
  apply card_bij (fun i _=>⟨v,i⟩)
  · intro i _;simp
  · intro i _ j _ he
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  · intro z hz
    rcases z with ⟨u,i⟩
    have hu:u=v:=(mem_filter.mp hz).2
    subst u
    exact ⟨i,mem_univ _,rfl⟩

/-- Constructed realization on the original vertex type, with every edge
crossing the prescribed partition. No multigraph or matching is an input. -/
theorem exists_realization (a : V→ℕ) (P : Finset V)
    (hbalance : (∑v∈P,a v)=∑v∈Pᶜ,a v) :
    ∃M : MultiGraph V,(∀v,M.degree v=a v) ∧
      (∀u v,0<M.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P)) ∧
      ∀u v,M.mult s(u,v)≤min (a u) (a v) := by
  classical
  let A:=Σv:P,Fin (a v.val)
  let B:=Σv:↥(Pᶜ : Finset V),Fin (a v.val)
  have hcard : Fintype.card A=Fintype.card B := by
    simp only [A,B,Fintype.card_sigma,Fintype.card_fin]
    simpa only [Finset.sum_coe_sort] using hbalance
  let e : A≃B:=Fintype.equivOfCardEq hcard
  let left : A→V:=fun z=>z.1.val
  let right : A→V:=fun z=>(e z).1.val
  have hl : ∀z,left z∈P:=fun z=>z.1.property
  have hr : ∀z,right z∉P:=fun z=>mem_compl.mp (e z).1.property
  have hne : ∀z,left z≠right z:=fun z h=>hr z (h ▸ hl z)
  let edgeOf : A→Sym2 V:=fun z=>s(left z,right z)
  let M : MultiGraph V:={
    mult:=fun t=>(univ.filter fun z=>edgeOf z=t).card
    loopless:=by
      intro t ht
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro z hz
      have hd : (s(left z,right z)).IsDiag := by
        change (edgeOf z).IsDiag
        rw [(mem_filter.mp hz).2]
        exact ht
      exact hne z (Sym2.mk_isDiag_iff.mp hd) }
  have hdeg : ∀v,M.degree v=(univ.filter fun z=>v∈edgeOf z).card := by
    intro v
    change (∑t∈univ.filter (fun t:Sym2 V=>v∈t),(univ.filter fun z=>edgeOf z=t).card)=_
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext z
    simp
  have hdegrees : ∀v,M.degree v=a v := by
    intro v
    rw [hdeg]
    by_cases hv:v∈P
    · have heq : (univ.filter fun z=>v∈edgeOf z)=univ.filter (fun z:A=>z.1=⟨v,hv⟩) := by
        ext z
        simp only [mem_filter,mem_univ,true_and,edgeOf,Sym2.mem_iff]
        constructor
        · rintro (h|h)
          · exact Subtype.ext h.symm
          · exact False.elim (hr z (h ▸ hv))
        · intro h
          exact Or.inl (congrArg Subtype.val h).symm
      rw [heq]
      exact stub_fiber_card (fun z:P=>a z.val) ⟨v,hv⟩
    · have heq : (univ.filter fun z=>v∈edgeOf z)=univ.filter (fun z:A=>(e z).1=⟨v,mem_compl.mpr hv⟩) := by
        ext z
        simp only [mem_filter,mem_univ,true_and,edgeOf,Sym2.mem_iff]
        constructor
        · rintro (h|h)
          · exact False.elim (hv (h.symm ▸ hl z))
          · exact Subtype.ext h.symm
        · intro h
          exact Or.inr (congrArg Subtype.val h).symm
      rw [heq]
      have hc : (univ.filter fun z:A=>(e z).1=⟨v,mem_compl.mpr hv⟩).card=
          (univ.filter fun z:B=>z.1=⟨v,mem_compl.mpr hv⟩).card := by
        apply card_bij (fun z _=>e z)
        · intro z hz;exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩
        · intro z _ w _ h;exact e.injective h
        · intro z hz
          refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
          exact mem_filter.mpr ⟨mem_univ _,by rw [e.apply_symm_apply];exact (mem_filter.mp hz).2⟩
      rw [hc]
      exact stub_fiber_card (fun z:↥(Pᶜ : Finset V)=>a z.val) ⟨v,mem_compl.mpr hv⟩
  refine ⟨M,hdegrees,?_,?_⟩
  · intro u v huv
    obtain ⟨z,hz⟩:=card_pos.mp huv
    have hh : s(left z,right z)=s(u,v):=(mem_filter.mp hz).2
    rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact Or.inl ⟨h1 ▸ hl z,h2 ▸ hr z⟩
    · exact Or.inr ⟨h1 ▸ hl z,h2 ▸ hr z⟩
  · intro u v
    have hu:=M.mult_pair_le_degree u v
    have hv : M.mult s(u,v)≤M.degree v := by
      rw [Sym2.eq_swap]
      exact M.mult_pair_le_degree v u
    rw [hdegrees] at hu hv
    exact le_min hu hv

end OverfullWork.CanonicalBipartiteRealization
