module

public import OverfullWork.ClusterExceptionalTrimming
public import OverfullWork.ClusterOccupancy

@[expose] public section


/-! Discard the few clusters hit too heavily by a vertex exceptional set.
Reindex the surviving clusters so that no empty discarded fibre remains
in the index type. This controls distribution, but does not construct the
initial directed regular partition or equalize the surviving fibres. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def overloaded (f : V → Option I) (X : Finset V) (q : ℕ) : Finset I :=
  univ.filter fun i => q < (X ∩ cluster f i).card

noncomputable def retained (f : V → Option I) (X : Finset V) (q : ℕ) : Finset I :=
  univ.filter fun i => (X ∩ cluster f i).card ≤ q

theorem overloaded_budget (f : V → Option I) (X : Finset V) (q : ℕ) :
    (overloaded f X q).card*(q+1) ≤ X.card := by
  let J := overloaded f X q
  let A := fun i => X ∩ cluster f i
  have hDis : (↑J:Set I).PairwiseDisjoint A :=
    fun i _ j _ hij => cluster_intersections_disjoint f X hij
  have hSub : J.biUnion A ⊆ X := by
    intro v hv
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
    exact (mem_inter.mp hi).1
  have hSum : J.card*(q+1) ≤ ∑ i ∈ J,(A i).card := by
    calc
      _ = ∑ _i ∈ J,(q+1) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have hh := (mem_filter.mp hi).2
        change q < (A i).card at hh
        omega
  have hCount := card_le_card hSub
  rw [card_biUnion hDis] at hCount
  exact hSum.trans hCount

theorem retained_card_loss (f : V → Option I) (X : Finset V) (q : ℕ) :
    (retained f X q).card+(overloaded f X q).card=Fintype.card I := by
  have hh := card_filter_add_card_filter_not (s:=(univ : Finset I))
    (fun i => (X ∩ cluster f i).card ≤ q)
  simpa [retained,overloaded] using hh

noncomputable def redistribute (f : V → Option I) (X : Finset V) (q : ℕ) :
    V → Option (retained f X q) := fun v =>
  if v ∈ X then none else match f v with
    | none => none
    | some i => if hi : i ∈ retained f X q then some ⟨i,hi⟩ else none

theorem cluster_redistribute (f : V → Option I) (X : Finset V) (q : ℕ)
    (i : retained f X q) :
    cluster (redistribute f X q) i=cluster f i.val\X := by
  ext v
  simp only [mem_cluster,mem_sdiff]
  by_cases hv : v ∈ X
  · simp [redistribute,hv]
  · cases hh : f v with
    | none => simp [redistribute,hv,hh]
    | some j =>
      by_cases hj : j ∈ retained f X q
      · simp [redistribute,hv,hh,hj,Subtype.ext_iff]
      · have hji : j ≠ i.val := by intro he;subst j;exact hj i.property
        simp [redistribute,hv,hh,hj,hji]

theorem redistributed_cluster_sizes (f : V → Option I) (X : Finset V) (q : ℕ)
    (i : retained f X q) :
    (cluster (redistribute f X q) i).card ≤ (cluster f i.val).card ∧
      (cluster f i.val).card ≤ (cluster (redistribute f X q) i).card+q := by
  rw [cluster_redistribute]
  have hLoss : (X ∩ cluster f i.val).card ≤ q := (mem_filter.mp i.property).2
  have hId := card_sdiff_add_card_inter (cluster f i.val) X
  rw [inter_comm] at hId
  exact ⟨card_le_card sdiff_subset,by omega⟩

theorem redistributed_exceptional_subset (f : V → Option I) (X : Finset V) (q : ℕ) :
    exceptional (redistribute f X q) ⊆ exceptional f ∪ X ∪ lift f (overloaded f X q) := by
  intro v hv
  by_cases hX : v ∈ X
  · exact mem_union_left _ (mem_union_right _ hX)
  · cases hh : f v with
    | none => exact mem_union_left _ (mem_union_left _ ((mem_exceptional f v).mpr hh))
    | some i =>
      have hi : i ∉ retained f X q := by
        intro hi
        have hn := (mem_exceptional (redistribute f X q) v).mp hv
        simp [redistribute,hX,hh,hi] at hn
      have hOver : i ∈ overloaded f X q := by
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        have hn : ¬(X ∩ cluster f i).card ≤ q := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
        omega
      exact mem_union_right _ ((mem_lift f _ v).mpr ⟨i,hOver,hh⟩)

theorem redistributed_exceptional_budget (f : V → Option I) (X : Finset V) (q M : ℕ)
    (hSize : ∀ i,(cluster f i).card ≤ M) :
    (exceptional (redistribute f X q)).card ≤
      (exceptional f).card+X.card+M*(overloaded f X q).card := by
  have hSub := card_le_card (redistributed_exceptional_subset f X q)
  have hUnion := card_union_le (exceptional f ∪ X) (lift f (overloaded f X q))
  have hFirst := card_union_le (exceptional f) X
  have hLift := lift_card_le f M hSize (overloaded f X q)
  omega

theorem redistributed_half_regular_pair (D : Digraph V) (f : V → Option I)
    (X : Finset V) (q : ℕ) (i j : retained f X q) (ε d : ℝ)
    (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2)
    (hi : 2*q ≤ (cluster f i.val).card) (hj : 2*q ≤ (cluster f j.val).card)
    (hUniform : DirectedRegularPairs.IsUniform D ε (cluster f i.val) (cluster f j.val))
    (hDensity : d ≤ DirectedRegularPairs.density D (cluster f i.val) (cluster f j.val)) :
    DirectedRegularPairs.IsUniform D (2*ε)
      (cluster (redistribute f X q) i) (cluster (redistribute f X q) j) ∧
    d-ε ≤ DirectedRegularPairs.density D
      (cluster (redistribute f X q) i) (cluster (redistribute f X q) j) := by
  have hScale : ∀ z : retained f X q,2*q ≤ (cluster f z.val).card →
      ((cluster f z.val).card:ℝ)*ε ≤ ((cluster (redistribute f X q) z).card:ℝ) ∧
      ((cluster f z.val).card:ℝ)*ε ≤ ((cluster (redistribute f X q) z).card:ℝ)*(2*ε) := by
    intro z hz
    have hSize := (redistributed_cluster_sizes f X q z).2
    have hHalf : (cluster f z.val).card ≤ 2*(cluster (redistribute f X q) z).card := by omega
    have hHalfR : ((cluster f z.val).card:ℝ) ≤ 2*((cluster (redistribute f X q) z).card:ℝ) := by exact_mod_cast hHalf
    have hh := mul_le_mul_of_nonneg_right hHalfR hε
    have hCap := mul_le_mul_of_nonneg_left hεHalf (Nat.cast_nonneg (cluster f z.val).card : (0:ℝ) ≤ _)
    constructor <;> nlinarith only [hh,hCap,hHalfR]
  obtain ⟨hiLarge,hiScale⟩ := hScale i hi
  obtain ⟨hjLarge,hjScale⟩ := hScale j hj
  have hiSub : cluster (redistribute f X q) i ⊆ cluster f i.val := by
    rw [cluster_redistribute];exact sdiff_subset
  have hjSub : cluster (redistribute f X q) j ⊆ cluster f j.val := by
    rw [cluster_redistribute];exact sdiff_subset
  exact ⟨DirectedRegularPairs.uniform_on_subcells D hUniform hiSub hjSub hiLarge hjLarge hiScale hjScale le_rfl,
    (DirectedRegularPairs.density_on_subcells D hUniform hDensity hiSub hjSub hiLarge hjLarge).le⟩

theorem redistributed_loss_bounds (D H : Digraph V) (f : V → Option I) (L q : ℕ) :
    ∀ v,redistribute f (DirectedDegreeTrimming.bad (D\H) L) q v ≠ none →
      DirectedRobustExpansion.inDegree (D\H) v ≤ L ∧ DirectedRobustExpansion.outDegree (D\H) v ≤ L := by
  intro v hv
  have hNot : v ∉ DirectedDegreeTrimming.bad (D\H) L := by
    intro hh
    exact hv (by simp only [redistribute,if_pos hh])
  exact DirectedDegreeTrimming.loss_outside_bad (D\H) L v hNot

theorem retained_nonempty (f : V → Option I) (X : Finset V) (q : ℕ)
    (hSmall : X.card < Fintype.card I*(q+1)) : (retained f X q).Nonempty := by
  apply card_pos.mp
  have hBudget := overloaded_budget f X q
  have hCount := retained_card_loss f X q
  by_contra hn
  have hZero : (retained f X q).card=0 := by omega
  have hAll : (overloaded f X q).card=Fintype.card I := by omega
  rw [hAll] at hBudget
  omega

theorem redistributed_cluster_positive (f : V → Option I) (X : Finset V) (q : ℕ)
    (i : retained f X q) (hSize : q < (cluster f i.val).card) :
    (cluster (redistribute f X q) i).Nonempty := by
  apply card_pos.mp
  have hh := (redistributed_cluster_sizes f X q i).2
  omega

end OverfullWork.DirectedClusterQuotient
