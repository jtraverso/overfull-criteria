module

public import OverfullWork.CellBalancedPartition

@[expose] public section


/-! # Construct equal even cells and a bounded exceptional set

Given an actual cell map outside a supplied exceptional set, select
exactly `2*l` vertices in each cell and move the remaining vertices to
the exceptional set. The loss bound and parity of every resulting cell
are proved from cardinalities. This supplies, rather than assumes, the
even-cell input to the common partition construction of CMS Lemma 5.4.
-/
namespace OverfullWork.EqualEvenCellRefinement
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem exists_refinement (f : V→I) (E : Finset V) (m l c : ℕ)
    (hcard : Fintype.card V=2*m)
    (hSizes : ∀i,2*l≤(Eᶜ.filter fun v=>f v=i).card ∧
      (Eᶜ.filter fun v=>f v=i).card≤2*l+c) :
    ∃E' : Finset V,∃g : V→Option I,
      E⊆E' ∧ E'.card≤E.card+c*Fintype.card I ∧
      (∀v,g v=none ↔ v∈E') ∧
      (∀i,(univ.filter fun v=>g v=some i).card=2*l) ∧
      (∀v i,g v=some i → f v=i) ∧
      ∀i,Even (Fintype.card {v : V // g v=i}) := by
  let C:=fun i=>Eᶜ.filter fun v=>f v=i
  have hChoose:∀i,∃S : Finset V,S⊆C i ∧ S.card=2*l:=by
    intro i
    exact exists_subset_card_eq (hSizes i).1
  choose S hSC hScard using hChoose
  have hCdis:(↑(univ:Finset I):Set I).PairwiseDisjoint C:=by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hfi: f v=i:=(mem_filter.mp hvi).2
    have hfj: f v=j:=(mem_filter.mp hvj).2
    exact hij (hfi.symm.trans hfj)
  have hSdis:(↑(univ:Finset I):Set I).PairwiseDisjoint S:=by
    intro i hi j hj hij
    exact Finset.disjoint_left.mpr (fun v hvi hvj=>
      Finset.disjoint_left.mp (hCdis hi hj hij) (hSC i hvi) (hSC j hvj))
  let U:=(univ:Finset I).biUnion S
  let E':=Uᶜ
  let g:V→Option I:=fun v=>if v∈U then some (f v) else none
  have hMem:∀i v,v∈S i → f v=i:=by intro i v hv;exact (mem_filter.mp (hSC i hv)).2
  have hSub:U⊆Eᶜ:=by
    intro v hv
    obtain ⟨i,_,hvi⟩:=mem_biUnion.mp hv
    exact (mem_filter.mp (hSC i hvi)).1
  have hEsub:E⊆E':=by
    intro v hv
    exact mem_compl.mpr (fun hvU=>(mem_compl.mp (hSub hvU)) hv)
  have hUcard:U.card=2*l*Fintype.card I:=by
    rw [card_biUnion hSdis]
    simp only [hScard,sum_const,card_univ,smul_eq_mul,Nat.mul_comm]
  have hCunion:(univ:Finset I).biUnion C=Eᶜ:=by
    ext v
    simp only [mem_biUnion,mem_univ,true_and,C,mem_filter]
    exact ⟨fun ⟨i,hv,_⟩=>hv,fun hv=>⟨f v,hv,rfl⟩⟩
  have hCsum:(∑i : I,(C i).card)=Eᶜ.card:=by rw [←hCunion,card_biUnion hCdis]
  have hTotal:Eᶜ.card≤(2*l+c)*Fintype.card I:=by
    rw [←hCsum]
    calc
      _ ≤ ∑_i : I,(2*l+c) :=sum_le_sum (fun i _=>(hSizes i).2)
      _ = _ :=by simp [Nat.mul_comm]
  have hPartition:E'.card+2*l*Fintype.card I=Fintype.card V:=by
    change Uᶜ.card+2*l*Fintype.card I=Fintype.card V
    have hh:=card_add_card_compl U
    omega
  have hBound:E'.card≤E.card+c*Fintype.card I:=by
    have hh:=card_add_card_compl E
    rw [Nat.add_mul] at hTotal
    omega
  have hNone:∀v,g v=none ↔ v∈E':=by intro v;simp [g,E']
  have hFiber:∀i,(univ.filter fun v=>g v=some i)=S i:=by
    intro i
    ext v
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · intro hv
      have hvU:v∈U:=by by_contra hn;simp [g,hn] at hv
      have hfi:f v=i:=by simpa only [g,if_pos hvU,Option.some.injEq] using hv
      obtain ⟨j,_,hvj⟩:=mem_biUnion.mp hvU
      have hj:j=i:=(hMem j v hvj).symm.trans hfi
      simpa only [hj] using hvj
    · intro hv
      have hvU:v∈U:=mem_biUnion.mpr ⟨i,mem_univ _,hv⟩
      simp [g,hvU,hMem i v hv]
  have hEvenSome:∀i,Even (Fintype.card {v : V // g v=some i}):=by
    intro i
    have hh:(univ.filter fun v=>g v=some i).card=2*l:=by rw [hFiber,hScard]
    have hc:Fintype.card {v : V // g v=some i}=2*l:=by
      rw [Fintype.card_subtype]
      exact hh
    exact ⟨l,by omega⟩
  have hEvenNone:Even (Fintype.card {v : V // g v=none}):=by
    have hc:Fintype.card {v : V // g v=none}=E'.card:=by
      have hs:(univ.filter fun v=>g v=none)=E':=by ext v;simp [hNone]
      rw [Fintype.card_subtype]
      exact congrArg Finset.card hs
    rw [hc]
    refine ⟨m-l*Fintype.card I,?_⟩
    have hmul:2*l*Fintype.card I=2*(l*Fintype.card I):=by ring
    omega
  refine ⟨E',g,hEsub,hBound,hNone,?_,?_,?_⟩
  · intro i
    rw [hFiber,hScard]
  · intro v i hv
    have hm:v∈(univ.filter fun v=>g v=some i):=mem_filter.mpr ⟨mem_univ _,hv⟩
    rw [hFiber] at hm
    exact hMem i v hm
  · intro i
    cases i with
    | none => exact hEvenNone
    | some i => exact hEvenSome i

end OverfullWork.EqualEvenCellRefinement
