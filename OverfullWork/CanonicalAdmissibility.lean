module

public import OverfullWork.MultigraphCuts
public import OverfullWork.DeficitCompletion

@[expose] public section


/-! # Admissible deficit sequences from even-order multigraph odd cuts

Only the vertex-complement odd sets are needed for deficit balance.
This supplies actual parity and balance inputs to canonical completion,
including multigraphs, without assuming a regular supergraph exists.
-/
namespace OverfullWork.CanonicalAdmissibility
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_singleton (M : MultiGraph V) (v : V) : M.cutSize {v}=M.degree v := by
  rw [MultiGraph.cutSize,sum_singleton,MultiGraph.degree_eq_sum_mult]
  have hh:=sum_add_sum_compl ({v}:Finset V) (fun w=>M.mult s(v,w))
  have hz:M.mult s(v,v)=0:=M.loopless _ (by simp)
  simpa only [sum_singleton,hz,Nat.zero_add] using hh

theorem deficit_even (M : MultiGraph V) (D m : ℕ) (hcard : Fintype.card V=2*m)
    (hD : ∀v,M.degree v≤D) : Even (∑v,(D-M.degree v)) := by
  have ht:=MultiGraph.total_deficit_of_bounded M D hD
  rw [M.sum_degrees_eq_twice_edgeCount,hcard] at ht
  have hp : 2*m*D=2*(m*D) := by ring
  rw [hp] at ht
  exact ⟨m*D-M.edgeCount,by omega⟩

theorem deficit_balanced (M : MultiGraph V) (D m : ℕ) (hm : 1≤m)
    (hcard : Fintype.card V=2*m) (hD : ∀v,M.degree v≤D)
    (hno : ¬M.HasOverfullSubset D) (v : V) :
    2*(D-M.degree v)≤∑w,(D-M.degree w) := by
  let S:=({v}:Finset V)ᶜ
  have hS : S.card=2*m-1 := by
    dsimp [S]
    rw [card_compl,card_singleton,hcard]
  have he : M.edgesWithin S≤D*(S.card/2) := by
    by_contra hn
    exact hno ⟨S,Nat.lt_of_not_ge hn⟩
  have hhalf : S.card/2=m-1 := by omega
  rw [hhalf] at he
  have hsum:=M.sum_degree_eq_internal_add_cut S
  rw [MultiGraph.twiceInternal_eq,MultiGraph.cutSize_compl,cut_singleton] at hsum
  have hsplit:=sum_add_sum_compl ({v}:Finset V) M.degree
  simp only [sum_singleton] at hsplit
  have htotal:=M.sum_degrees_eq_twice_edgeCount
  have hdef:=MultiGraph.total_deficit_of_bounded M D hD
  rw [htotal,hcard] at hdef
  have hsplit' : M.degree v+(∑w∈S,M.degree w)=2*M.edgeCount := by
    simpa only [S,htotal] using hsplit
  have hid : 2*M.edgesWithin S+2*M.degree v=2*M.edgeCount := by omega
  have hprod : 2*m*D=2*(D*(m-1))+2*D := by
    have hm':m=(m-1)+1:=by omega
    conv_lhs => rw [hm']
    ring
  rw [hprod] at hdef
  have hd:=hD v
  omega

/-- The even total and its half are obtained, and every deficit is
bounded by that half. They are data for Lemma 3.1, not extra inputs. -/
theorem exists_half_deficit (M : MultiGraph V) (D m : ℕ) (hm : 1≤m)
    (hcard : Fintype.card V=2*m) (hD : ∀v,M.degree v≤D)
    (hno : ¬M.HasOverfullSubset D) :
    ∃T : ℕ,(∑v,(D-M.degree v))=2*T ∧ ∀v,D-M.degree v≤T := by
  obtain ⟨T,hT⟩:=deficit_even M D m hcard hD
  have ht:(∑v,(D-M.degree v))=2*T:=by omega
  refine ⟨T,ht,?_⟩
  intro v
  have hb:=deficit_balanced M D m hm hcard hD hno v
  omega

end OverfullWork.CanonicalAdmissibility
