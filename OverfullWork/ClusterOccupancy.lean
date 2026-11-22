module

public import OverfullWork.DirectedClusterQuotient

@[expose] public section


/-! Quantitative source-set geometry for lifting a reduced robust graph.
Cluster sizes may vary between later supplied lower/upper bounds. An
actual subset of occupied clusters is capped to the reduced admissible
interval; its cardinality still controls the source set. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem lift_card_le (f : V → Option I) (M : ℕ)
    (hSize : ∀ i,(cluster f i).card ≤ M) (S : Finset I) : (lift f S).card ≤ M*S.card := by
  unfold lift
  rw [card_biUnion (fun i _ j _ hij => clusters_disjoint f hij)]
  calc
    _ ≤ ∑ _i ∈ S,M := sum_le_sum fun i _ => hSize i
    _ = _ := by simp [Nat.mul_comm]

theorem order_le (f : V → Option I) (M : ℕ)
    (hSize : ∀ i,(cluster f i).card ≤ M) :
    Fintype.card V ≤ (exceptional f).card+M*Fintype.card I := by
  have hh := card_union_le (exceptional f) (lift f univ)
  rw [exceptional_union_lift,card_univ] at hh
  have hLift := lift_card_le f M hSize univ
  simp only [card_univ] at hLift
  omega

theorem cluster_intersections_disjoint (f : V → Option I) (S : Finset V)
    {i j : I} (hij : i ≠ j) : Disjoint (S ∩ cluster f i) (S ∩ cluster f j) :=
  (clusters_disjoint f hij).mono inter_subset_right inter_subset_right

theorem card_le_exceptional_add_cluster_intersections (f : V → Option I) (S : Finset V) :
    S.card ≤ (exceptional f).card+∑ i : I,(S ∩ cluster f i).card := by
  have hSub : S ⊆ exceptional f ∪ univ.biUnion (fun i : I => S ∩ cluster f i) := by
    intro v hv
    cases hh : f v with
    | none => exact mem_union_left _ ((mem_exceptional f v).mpr hh)
    | some i =>
      exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_inter.mpr ⟨hv,(mem_cluster f i v).mpr hh⟩⟩)
  have hCount := (card_le_card hSub).trans (card_union_le _ _)
  rw [card_biUnion (fun i _ j _ hij => cluster_intersections_disjoint f S hij)] at hCount
  exact hCount

noncomputable def occupied (f : V → Option I) (S : Finset V) (h : ℕ) : Finset I :=
  univ.filter fun i => h ≤ (S ∩ cluster f i).card

theorem occupied_mass_bound (f : V → Option I) (S : Finset V) (M h : ℕ)
    (hSize : ∀ i,(cluster f i).card ≤ M) :
    S.card ≤ (exceptional f).card+M*(occupied f S h).card+h*Fintype.card I := by
  let J := occupied f S h
  have hPoint : ∀ i : I,(S ∩ cluster f i).card ≤ (if i ∈ J then M else 0)+h := by
    intro i
    have hiM := (card_le_card (s:=S ∩ cluster f i) (t:=cluster f i) inter_subset_right).trans (hSize i)
    by_cases hi : i ∈ J
    · simp only [if_pos hi];omega
    · have hLow : (S ∩ cluster f i).card < h := by
        have hNot : ¬h ≤ (S ∩ cluster f i).card := fun hh => hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
        omega
      simp only [if_neg hi,Nat.zero_add]
      exact hLow.le
  have hSum := sum_le_sum (s:=univ) fun i _ => hPoint i
  have hJSum : (∑ i : I,if i ∈ J then M else 0)=J.card*M := by
    rw [←sum_filter]
    simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
    simp
  rw [sum_add_distrib,hJSum] at hSum
  simp only [sum_const,card_univ,nsmul_eq_mul] at hSum
  have hMass := card_le_exceptional_add_cluster_intersections f S
  dsimp only [J] at hSum
  nlinarith only [hMass,hSum]

theorem exists_capped_occupied (f : V → Option I) (S : Finset V) (M h t T : ℕ)
    (hM : 0 < M) (hSize : ∀ i,(cluster f i).card ≤ M)
    (hInterval : (exceptional f).card+h*Fintype.card I+M*t ≤ T)
    (hNonvacuous : 2*t ≤ Fintype.card I) (hLo : T ≤ S.card)
    (hHi : S.card+T ≤ Fintype.card V) :
    ∃ J : Finset I,J ⊆ occupied f S h ∧ t ≤ J.card ∧ J.card+t ≤ Fintype.card I ∧
      S.card ≤ M*J.card+(exceptional f).card+h*Fintype.card I := by
  let O := occupied f S h
  have hMass := occupied_mass_bound f S M h hSize
  change S.card ≤ (exceptional f).card+M*O.card+h*Fintype.card I at hMass
  have hOLo : t ≤ O.card := by
    have hh : M*t ≤ M*O.card := by omega
    exact (mul_le_mul_iff_right₀ hM).mp hh
  obtain ⟨J,hJO,hJCard⟩ := exists_subset_card_eq (min_le_left O.card (Fintype.card I-t))
  refine ⟨J,hJO,by omega,by omega,?_⟩
  rcases le_total O.card (Fintype.card I-t) with hSmall|hLarge
  · rw [min_eq_left hSmall] at hJCard
    change _ ≤ (exceptional f).card+M*O.card+h*Fintype.card I at hMass
    nlinarith only [hMass,hJCard]
  · rw [min_eq_right hLarge] at hJCard
    have hOrder := order_le f M hSize
    have ht : t ≤ Fintype.card I := by omega
    have hId : M*(Fintype.card I-t)+M*t=M*Fintype.card I := by
      rw [←Nat.mul_add,Nat.sub_add_cancel ht]
    nlinarith only [hHi,hInterval,hOrder,hId,hJCard]

end OverfullWork.DirectedClusterQuotient
