module

public import OverfullWork.EquitableMissingCounts
public import OverfullWork.LooplessRealization
public import OverfullWork.MultigraphActiveSupport
public import OverfullWork.PerturbationAccounting

@[expose] public section


/-! # Construct missing-common-color pairs with crossing priority

The pairing graph is on the missing vertices, not asserted to be a
subgraph of the ambient graph. Crossing pairs are chosen until one side
is exhausted; the remaining even set is paired internally. Every
missing vertex occurs exactly once and no nonmissing vertex occurs.
-/
namespace OverfullWork.PriorityMCCPairing
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 12000000

theorem exists_pairing (S : Finset V) (hS : Even S.card) :
    ∃ J : MultiGraph V, ∀ v, J.degree v=if v ∈ S then 1 else 0 := by
  have hsum : (∑ v : V, if v ∈ S then 1 else 0)=S.card := by simp
  apply LooplessRealization.exists_realization (fun v => if v ∈ S then 1 else 0)
  · rwa [hsum]
  · intro v
    rw [hsum]
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have hp : 0 < S.card := card_pos.mpr ⟨v,hv⟩
      obtain ⟨q,hq⟩ := hS
      omega
    · rw [if_neg hv];omega

theorem zero_cut_of_one_side (J : MultiGraph V) (S A : Finset V)
    (hdeg : ∀ v, J.degree v=if v ∈ S then 1 else 0) (hS : S ⊆ A ∨ S ⊆ Aᶜ) :
    J.cutSize A=0 := by
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  rcases hS with hS|hS
  · have hvS : v ∉ S := fun hh => (mem_compl.mp hv) (hS hh)
    rw [show s(u,v)=s(v,u) from Sym2.eq_swap]
    exact J.mult_eq_zero_of_degree_zero v u (by rw [hdeg,if_neg hvS])
  · have huS : u ∉ S := fun hh => (mem_compl.mp (hS hh)) hu
    exact J.mult_eq_zero_of_degree_zero u v (by rw [hdeg,if_neg huS])

theorem exists_priority_pairing (S A : Finset V) (hS : Even S.card) :
    ∃ J : MultiGraph V, (∀ v, J.degree v=if v ∈ S then 1 else 0) ∧
      J.cutSize A=min (S∩A).card (S\A).card := by
  suffices ∀ n : ℕ, ∀ S : Finset V, S.card=n → Even n →
      ∃ J : MultiGraph V, (∀ v, J.degree v=if v ∈ S then 1 else 0) ∧
        J.cutSize A=min (S∩A).card (S\A).card from this _ S rfl hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard heven
    by_cases hleft : (S∩A).Nonempty
    · by_cases hright : (S\A).Nonempty
      · obtain ⟨u,hu⟩ := hleft
        obtain ⟨v,hv⟩ := hright
        have huS := (mem_inter.mp hu).1
        have huA := (mem_inter.mp hu).2
        have hvS := (mem_sdiff.mp hv).1
        have hvA := (mem_sdiff.mp hv).2
        have huv : u ≠ v := fun hh => hvA (hh ▸ huA)
        let R := (S.erase u).erase v
        have hvErase : v ∈ S.erase u := mem_erase.mpr ⟨huv.symm,hvS⟩
        have hRsize : R.card+2=S.card := by
          have h1 := card_erase_add_one huS
          have h2 := card_erase_add_one hvErase
          dsimp only [R]
          omega
        have hRsmall : R.card < n := by omega
        have hReven : Even R.card := by
          obtain ⟨q,hq⟩ := heven
          exact ⟨q-1,by omega⟩
        obtain ⟨F,hFdeg,hFcut⟩ := ih R.card hRsmall R rfl hReven
        have hRA : R∩A=(S∩A).erase u := by
          ext z
          by_cases hz : z=v
          · subst z;simp [R,hvA]
          · simp [R,hz] <;> tauto
        have hRB : R\A=(S\A).erase v := by
          ext z
          by_cases hz : z=u
          · subst z;simp [R,huA]
          · simp [R,hz] <;> tauto
        have hleftCount : (R∩A).card+1=(S∩A).card := by rw [hRA];exact card_erase_add_one hu
        have hrightCount : (R\A).card+1=(S\A).card := by rw [hRB];exact card_erase_add_one hv
        refine ⟨(MultiGraph.unitEdge u v huv).addCopies F,?_,?_⟩
        · intro z
          rw [MultiGraph.degree_addCopies,MultiGraph.degree_unitEdge,hFdeg]
          by_cases hzu : z=u
          · subst z;simp [R,huS]
          by_cases hzv : z=v
          · subst z;simp [R,hvS]
          · simp [R,hzu,hzv]
        · rw [MultiGraph.cutSize_addCopies,MultiGraph.cutSize_unitEdge,hFcut,if_neg (by simp [huA,hvA])]
          omega
      · obtain ⟨J,hJ⟩ := exists_pairing S (hcard ▸ heven)
        have hsub : S ⊆ A := by
          intro v hv
          by_contra hvA
          exact hright ⟨v,mem_sdiff.mpr ⟨hv,hvA⟩⟩
        refine ⟨J,hJ,?_⟩
        have hc := zero_cut_of_one_side J S A hJ (Or.inl hsub)
        have hz : (S\A).card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hright)
        rw [hc,hz,Nat.min_zero]
    · obtain ⟨J,hJ⟩ := exists_pairing S (hcard ▸ heven)
      have hsub : S ⊆ Aᶜ := by
        intro v hv
        apply mem_compl.mpr
        intro hvA
        exact hleft ⟨v,mem_inter.mpr ⟨hv,hvA⟩⟩
      refine ⟨J,hJ,?_⟩
      have hc := zero_cut_of_one_side J S A hJ (Or.inr hsub)
      have hz : (S∩A).card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hleft)
      rw [hc,hz,Nat.zero_min]

theorem pairing_edgeCount (J : MultiGraph V) (S : Finset V)
    (hdeg : ∀ v, J.degree v=if v ∈ S then 1 else 0) : J.edgeCount=S.card/2 := by
  have hh := J.sum_degrees_eq_twice_edgeCount
  simp_rw [hdeg] at hh
  have hsum : (∑ v : V, if v ∈ S then 1 else 0)=S.card := by simp
  rw [hsum] at hh
  omega

theorem pairing_ends_mem (J : MultiGraph V) (S : Finset V)
    (hdeg : ∀ v, J.degree v=if v ∈ S then 1 else 0) (u v : V) (huv : 0 < J.mult s(u,v)) :
    u ∈ S ∧ v ∈ S := by
  have hu := J.mult_pair_le_degree u v
  have hv := J.mult_pair_le_degree v u
  rw [show s(v,u)=s(u,v) from Sym2.eq_swap,hdeg] at hv
  rw [hdeg] at hu
  constructor
  · by_contra h;rw [if_neg h] at hu;omega
  · by_contra h;rw [if_neg h] at hv;omega

end OverfullWork.PriorityMCCPairing

namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 8000000

theorem exists_priority_mcc_pairing (C : M.EdgeColoring k) (A : Finset V)
    (hV : Even (Fintype.card V)) (i : Fin k) :
    ∃ J : MultiGraph V,
      (∀ v, J.degree v=if (C.colourGraph i).degree v=0 then 1 else 0) ∧
      J.cutSize A=min (C.missingSet A i).card (C.missingSet Aᶜ i).card ∧
      J.edgeCount=(C.missingSet univ i).card/2 ∧
      ∀ u v, 0 < J.mult s(u,v) → (C.colourGraph i).degree u=0 ∧ (C.colourGraph i).degree v=0 := by
  let S := C.missingSet univ i
  obtain ⟨J,hJ,hCut⟩ := OverfullWork.PriorityMCCPairing.exists_priority_pairing S A (C.missing_card_even hV i)
  have hSA : S∩A=C.missingSet A i := by ext v;simp [S,missingSet,and_comm]
  have hSB : S\A=C.missingSet Aᶜ i := by ext v;simp [S,missingSet,and_comm]
  rw [hSA,hSB] at hCut
  refine ⟨J,?_,hCut,OverfullWork.PriorityMCCPairing.pairing_edgeCount J S hJ,?_⟩
  · intro v
    simpa only [S,missingSet,mem_filter,mem_univ,true_and] using hJ v
  · intro u v huv
    have hh := OverfullWork.PriorityMCCPairing.pairing_ends_mem J S hJ u v huv
    exact ⟨(mem_filter.mp hh.1).2,(mem_filter.mp hh.2).2⟩

end SimpleGraph.MultiGraph.EdgeColoring

namespace OverfullWork.PriorityMCCPairing
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

structure Family (C : M.EdgeColoring k) (A : Finset V) where
  graph : Fin k → MultiGraph V
  degree : ∀ i v, (graph i).degree v=if (C.colourGraph i).degree v=0 then 1 else 0
  crossing : ∀ i, (graph i).cutSize A=min (C.missingSet A i).card (C.missingSet Aᶜ i).card
  size : ∀ i, (graph i).edgeCount=(C.missingSet univ i).card/2
  missing : ∀ i u v, 0 < (graph i).mult s(u,v) →
    (C.colourGraph i).degree u=0 ∧ (C.colourGraph i).degree v=0

theorem exists_family (C : M.EdgeColoring k) (A : Finset V) (hV : Even (Fintype.card V)) :
    Nonempty (Family C A) := by
  let J := fun i => Classical.choose (C.exists_priority_mcc_pairing A hV i)
  have hJ := fun i => Classical.choose_spec (C.exists_priority_mcc_pairing A hV i)
  exact ⟨{
    graph := J
    degree := fun i => (hJ i).1
    crossing := fun i => (hJ i).2.1
    size := fun i => (hJ i).2.2.1
    missing := fun i => (hJ i).2.2.2
  }⟩

end OverfullWork.PriorityMCCPairing
