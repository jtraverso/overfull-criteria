module

public import OverfullWork.DirectedRegularPairs
public import OverfullWork.DirectedClusterQuotient
public import OverfullWork.NormalizedRobustQuotient

@[expose] public section


/-! Construct the actual pure graph by retaining arcs in selected pairs.
Positive pair density identifies its actual quotient with the selected
reduced graph. Existence of a partition with controlled degree losses is
not assumed to follow from this identification. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem arc_of_positive_density (D : Digraph V) (A B : Finset V)
    (hPos : 0 < density D A B) : ∃ u ∈ A,∃ v ∈ B,D.Adj u v := by
  by_contra hn
  push_neg at hn
  have hZero : incidences D A B=0 := by
    unfold incidences
    apply sum_eq_zero
    intro v hv
    have hEmpty : A.filter (fun u => D.Adj u v)=∅ :=
      filter_eq_empty_iff.mpr (fun u hu => hn u hu v hv)
    simp only [inNeighbours,hEmpty,card_empty]
  simp only [density,hZero,Nat.cast_zero,zero_div] at hPos
  exact (lt_irrefl 0) hPos

def restrictPairs (D : Digraph V) (f : V → Option I) (R : Digraph I) : Digraph V where
  Adj u v := D.Adj u v ∧ ∃ i j,f u=some i ∧ f v=some j ∧ R.Adj i j

theorem restrictPairs_le (D : Digraph V) (f : V → Option I) (R : Digraph I) :
    restrictPairs D f R ≤ D := fun _ _ h => h.1

theorem quotient_restrictPairs (D : Digraph V) (f : V → Option I) (R : Digraph I)
    (hPositive : ∀ i j,R.Adj i j → 0 < density D (cluster f i) (cluster f j)) :
    quotient (restrictPairs D f R) f=R := by
  ext i j
  constructor
  · rintro ⟨u,v,hu,hv,_,i',j',hi',hj',hR⟩
    have hi : i'=i := Option.some.inj (hi'.symm.trans hu)
    have hj : j'=j := Option.some.inj (hj'.symm.trans hv)
    subst i';subst j';exact hR
  · intro hR
    obtain ⟨u,hu,v,hv,hArc⟩ := arc_of_positive_density D _ _ (hPositive i j hR)
    have hu' := (mem_cluster f i u).mp hu
    have hv' := (mem_cluster f j v).mp hv
    exact ⟨u,v,hu',hv',hArc,i,j,hu',hv',hR⟩

def regularReduced (D : Digraph V) (f : V → Option I) (ε d : ℝ) : Digraph I where
  Adj i j := i ≠ j ∧ IsUniform D ε (cluster f i) (cluster f j) ∧
    d ≤ density D (cluster f i) (cluster f j)

theorem quotient_regular_pure (D : Digraph V) (f : V → Option I) (ε d : ℝ) (hd : 0 < d) :
    quotient (restrictPairs D f (regularReduced D f ε d)) f=regularReduced D f ε d :=
  quotient_restrictPairs D f _ (fun _ _ h => hd.trans_le h.2.2)

theorem regular_pure_independent_clusters (D : Digraph V) (f : V → Option I) (ε d : ℝ)
    (u v : V) (i : I) (hu : f u=some i) (hv : f v=some i) :
    ¬(restrictPairs D f (regularReduced D f ε d)).Adj u v := by
  rintro ⟨_,j,k,hj,hk,hR⟩
  have hj' : j=i := Option.some.inj (hj.symm.trans hu)
  have hk' : k=i := Option.some.inj (hk.symm.trans hv)
  exact hR.1 (hj'.trans hk'.symm)

theorem regularReduced_real_transfer (D : Digraph V) (f : V → Option I)
    (ε d : ℝ) (hd : 0 < d) (m L : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hLossIn : ∀ v,inDegree (D\restrictPairs D f (regularReduced D f ε d)) v ≤ L)
    (hLossOut : ∀ v,outDegree (D\restrictPairs D f (regularReduced D f ε d)) v ≤ L)
    (hClusters : 4 ≤ ν*(Fintype.card I:ℝ))
    (hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ))
    (hException : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLossSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4)
    (hDegreeSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    IsRealRobust (regularReduced D f ε d) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (inDegree (regularReduced D f ε d) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (outDegree (regularReduced D f ε d) j:ℝ)) := by
  have hh := RobustClusterQuotient.real_quotient_transfer D _ (restrictPairs_le D f _) f m L hm
    hSize ν τ α hν hτ hα hRobust hIn hOut hLossIn hLossOut hClusters hOrderLarge
    hException hLossSmall hDegreeSmall
  rw [quotient_regular_pure D f ε d hd] at hh
  exact hh

end OverfullWork.DirectedClusterQuotient
