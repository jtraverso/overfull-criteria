module

public import OverfullWork.TwoSidedClusterQuotient
public import OverfullWork.ClusterOccupancy
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! Deterministic reverse transfer from a robust reduced digraph through
dense directed regular pairs. Unequal cluster sizes and an exceptional
set are permitted. Every loss is explicit; no regularity partition is
assumed to exist, and no Hamiltonian conclusion is asserted. This is the
regular-pair lifting step invoked in GGKLO Lemma 14.3. -/
namespace OverfullWork.TwoSidedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem target_cluster_good_count (D : Digraph V) (R : Digraph I)
    (f g : V → Option I) (S : Finset V) (J : Finset I) (j : I)
    (m M h a r s : ℕ) (ε d : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hε : 0 < ε) (hεd : ε ≤ d)
    (hLower : ∀ i,m ≤ (cluster g i).card)
    (hSourceLower : ∀ i,0 < (cluster f i).card)
    (hUpper : ∀ i,(cluster f i).card ≤ M)
    (hTargetUpper : ∀ i,(cluster g i).card ≤ M)
    (hUniform : ∀ i j,R.Adj i j → IsUniform D ε (cluster f i) (cluster g j))
    (hDensity : ∀ i j,R.Adj i j → d ≤ density D (cluster f i) (cluster g j))
    (hOccupied : J ⊆ occupied f S h)
    (hj : j ∈ neighbourhood R r J)
    (hSource : (M:ℝ)*ε ≤ (h:ℝ)) (hBad : (M:ℝ)*ε ≤ (a:ℝ))
    (hThreshold : (s:ℝ) ≤ (d-ε)*(h:ℝ)*(r:ℝ)) :
    m ≤ ((cluster g j).filter fun v => s ≤ inNeighbours D S v).card+a := by
  let F := J.filter fun i => R.Adj i j
  let A := fun i => S ∩ cluster f i
  have hFr : r ≤ F.card := (mem_filter.mp hj).2
  have hF : F.Nonempty := card_pos.mp (lt_of_lt_of_le hr hFr)
  have hA : ∀ i ∈ F,h ≤ (A i).card := by
    intro i hi
    exact (mem_filter.mp (hOccupied (mem_filter.mp hi).1)).2
  have hSum : (h:ℝ)*(r:ℝ) ≤ ∑ i ∈ F,((A i).card:ℝ) := by
    have hh : h*r ≤ ∑ i ∈ F,(A i).card := calc
      _ ≤ h*F.card := Nat.mul_le_mul_left _ hFr
      _ = ∑ _i ∈ F,h := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hA
    exact_mod_cast hh
  have hThreshold' : (s:ℝ) ≤ (d-ε)*(∑ i ∈ F,((A i).card:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hSum (sub_nonneg.mpr hεd)
    nlinarith only [hThreshold,hh]
  have hSmall := few_low_neighbours_family D F hF (cluster f) A (cluster g j) S ε d hε
    (card_pos.mp (lt_of_lt_of_le hm (hLower j)))
    (fun i _ => card_pos.mp (hSourceLower i))
    (fun i hi => hUniform i j (mem_filter.mp hi).2)
    (fun i hi => hDensity i j (mem_filter.mp hi).2)
    (fun _ _ => inter_subset_right) (fun _ _ => inter_subset_left)
    (fun i hi => (mul_le_mul_of_nonneg_right (by exact_mod_cast hUpper i) hε.le).trans
      (hSource.trans (by exact_mod_cast hA i hi)))
    (fun i _ j _ hij => cluster_intersections_disjoint f S hij) s hThreshold'
  have hLoss : ((cluster g j).filter fun v => inNeighbours D S v < s).card ≤ a := by
    have hh : (((cluster g j).filter fun v => inNeighbours D S v < s).card:ℝ) ≤ (a:ℝ) :=
      hSmall.le.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast hTargetUpper j) hε.le).trans hBad)
    exact_mod_cast hh
  have hPartition := card_filter_add_card_filter_not (s:=cluster g j)
    (fun v => s ≤ inNeighbours D S v)
  simp only [not_le] at hPartition
  have hCard := hLower j
  omega

theorem robust_of_regular_clusters (D : Digraph V) (R : Digraph I)
    (f g : V → Option I) (m M h a r t s T : ℕ) (ε d : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hr : 0 < r)
    (hε : 0 < ε) (hεd : ε ≤ d)
    (hLower : ∀ i,m ≤ (cluster g i).card)
    (hSourceLower : ∀ i,0 < (cluster f i).card)
    (hUpper : ∀ i,(cluster f i).card ≤ M)
    (hTargetUpper : ∀ i,(cluster g i).card ≤ M)
    (hUniform : ∀ i j,R.Adj i j → IsUniform D ε (cluster f i) (cluster g j))
    (hDensity : ∀ i j,R.Adj i j → d ≤ density D (cluster f i) (cluster g j))
    (hRobust : IsRobustAt R r t) (hNonvacuous : 2*t ≤ Fintype.card I)
    (hSource : (M:ℝ)*ε ≤ (h:ℝ)) (hBad : (M:ℝ)*ε ≤ (a:ℝ))
    (hThreshold : (s:ℝ) ≤ (d-ε)*(h:ℝ)*(r:ℝ))
    (hInterval : (exceptional f).card+h*Fintype.card I+M*t ≤ T)
    (hGrowth : (exceptional f).card+((M-m)+a+h)*Fintype.card I+s ≤ m*r) :
    IsRobustAt D s T := by
  intro S hLo hHi
  obtain ⟨J,hOccupied,hJLo,hJHi,hMass⟩ := exists_capped_occupied f S M h t T
    (lt_of_lt_of_le hm hmM) hUpper hInterval hNonvacuous hLo hHi
  let K := neighbourhood R r J
  let B := fun j => (cluster g j).filter fun v => s ≤ inNeighbours D S v
  have hK : J.card+r ≤ K.card := hRobust J hJLo hJHi
  have hGood : ∀ j ∈ K,m ≤ (B j).card+a := by
    intro j hj
    exact target_cluster_good_count D R f g S J j m M h a r s ε d hm hr hε hεd
      hLower hSourceLower hUpper hTargetUpper hUniform hDensity hOccupied hj hSource hBad hThreshold
  have hDis : (↑K:Set I).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact (clusters_disjoint g hij).mono (filter_subset _ _) (filter_subset _ _)
  have hSub : K.biUnion B ⊆ neighbourhood D s S := by
    intro v hv
    obtain ⟨j,_,hvj⟩ := mem_biUnion.mp hv
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hvj).2⟩
  have hSum := sum_le_sum (s:=K) hGood
  rw [sum_add_distrib] at hSum
  simp only [sum_const,nsmul_eq_mul] at hSum
  have hCount := card_le_card hSub
  rw [card_biUnion hDis] at hCount
  have hKBound : K.card ≤ Fintype.card I := card_le_univ _
  have hLoss := Nat.mul_le_mul_left a hKBound
  have hReduced := Nat.mul_le_mul_left m hK
  have hMId : M = m+(M-m) := by omega
  have hJBound : J.card ≤ Fintype.card I := card_le_univ _
  have hUnequal := Nat.mul_le_mul_left (M-m) hJBound
  nlinarith only [hMass,hSum,hCount,hLoss,hReduced,hGrowth,hMId,hUnequal]

end OverfullWork.TwoSidedClusterQuotient
