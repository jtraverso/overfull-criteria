module

public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Actual directed cluster quotients and exact finite fibre counts.
The exceptional vertices are those mapped to none. Equal cluster sizes
are explicit partition data, not an assumed robust reduced graph.
This supplies the counting geometry in Kühn--Osthus--Treglown Lemma 14. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def cluster (f : V → Option I) (i : I) : Finset V :=
  univ.filter fun v => f v=some i

noncomputable def exceptional (f : V → Option I) : Finset V :=
  univ.filter fun v => f v=none

noncomputable def lift (f : V → Option I) (S : Finset I) : Finset V :=
  S.biUnion (cluster f)

def quotient (D : Digraph V) (f : V → Option I) : Digraph I where
  Adj i j := ∃ u v : V,f u=some i ∧ f v=some j ∧ D.Adj u v

theorem quotient_loopless (D : Digraph V) (f : V → Option I)
    (hIndependent : ∀ u v i,f u=some i → f v=some i → ¬D.Adj u v) :
    ∀ i,¬(quotient D f).Adj i i := by
  rintro i ⟨u,v,hu,hv,hAdj⟩
  exact hIndependent u v i hu hv hAdj

theorem mem_cluster (f : V → Option I) (i : I) (v : V) :
    v ∈ cluster f i ↔ f v=some i := by simp only [cluster,mem_filter,mem_univ,true_and]

theorem mem_exceptional (f : V → Option I) (v : V) :
    v ∈ exceptional f ↔ f v=none := by simp only [exceptional,mem_filter,mem_univ,true_and]

theorem mem_lift (f : V → Option I) (S : Finset I) (v : V) :
    v ∈ lift f S ↔ ∃ i ∈ S,f v=some i := by simp only [lift,mem_biUnion,mem_cluster]

theorem clusters_disjoint (f : V → Option I) {i j : I} (hij : i ≠ j) :
    Disjoint (cluster f i) (cluster f j) := by
  apply disjoint_left.mpr
  intro v hi hj
  have hh := (mem_cluster f i v).mp hi
  have hh' := (mem_cluster f j v).mp hj
  exact hij (Option.some.inj (hh.symm.trans hh'))

theorem lift_card (f : V → Option I) (m : ℕ) (hSize : ∀ i,(cluster f i).card=m)
    (S : Finset I) : (lift f S).card=m*S.card := by
  unfold lift
  rw [card_biUnion (fun i _ j _ hij => clusters_disjoint f hij)]
  simp only [hSize,sum_const,nsmul_eq_mul]
  exact Nat.mul_comm _ _

theorem exceptional_disjoint_lift (f : V → Option I) (S : Finset I) :
    Disjoint (exceptional f) (lift f S) := by
  apply disjoint_left.mpr
  intro v hv hLift
  obtain ⟨i,_,hi⟩ := (mem_lift f S v).mp hLift
  have hn := (mem_exceptional f v).mp hv
  rw [hn] at hi
  cases hi

theorem exceptional_union_lift (f : V → Option I) :
    exceptional f ∪ lift f univ=univ := by
  ext v
  simp only [mem_union,mem_exceptional,mem_lift,mem_univ,iff_true]
  cases h : f v <;> simp

theorem order_eq (f : V → Option I) (m : ℕ) (hSize : ∀ i,(cluster f i).card=m) :
    Fintype.card V=(exceptional f).card+m*Fintype.card I := by
  have hh := card_union_of_disjoint (exceptional_disjoint_lift f univ)
  rw [exceptional_union_lift,lift_card f m hSize,card_univ,card_univ] at hh
  exact hh

theorem card_le_exceptional_add_lift (f : V → Option I) (m : ℕ)
    (hSize : ∀ i,(cluster f i).card=m) (A : Finset V) (B : Finset I)
    (hMap : ∀ v ∈ A,∀ i,f v=some i → i ∈ B) :
    A.card ≤ (exceptional f).card+m*B.card := by
  have hSub : A ⊆ exceptional f ∪ lift f B := by
    intro v hv
    cases hh : f v with
    | none => exact mem_union_left _ ((mem_exceptional f v).mpr hh)
    | some i => exact mem_union_right _ ((mem_lift f B v).mpr ⟨i,hMap v hv i hh,hh⟩)
  have hCount := card_le_card hSub
  rw [card_union_of_disjoint (exceptional_disjoint_lift f B),lift_card f m hSize] at hCount
  exact hCount

theorem inNeighbours_lift_le (D : Digraph V) (f : V → Option I) (m : ℕ)
    (hSize : ∀ i,(cluster f i).card=m) (S : Finset I) (v : V) (j : I)
    (hv : f v=some j) :
    inNeighbours D (lift f S) v ≤ m*inNeighbours (quotient D f) S j := by
  let A := (lift f S).filter fun u => D.Adj u v
  let B := S.filter fun i => (quotient D f).Adj i j
  have hSub : A ⊆ lift f B := by
    intro u hu
    obtain ⟨i,hi,hui⟩ := (mem_lift f S u).mp (mem_filter.mp hu).1
    exact (mem_lift f B u).mpr ⟨i,mem_filter.mpr ⟨hi,⟨u,v,hui,hv,(mem_filter.mp hu).2⟩⟩,hui⟩
  have hCount := card_le_card hSub
  rw [lift_card f m hSize] at hCount
  exact hCount

end OverfullWork.DirectedClusterQuotient
