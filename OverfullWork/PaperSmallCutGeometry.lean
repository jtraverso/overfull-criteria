module

public import OverfullWork.PaperOneCoreRoundPreservation
public import OverfullWork.TrimmingResidualOddGeometry

@[expose] public section


/-! # Finite boundary estimates used in CMS Claim 4.5

These count actual cut edges. The selected vertices outside S spend
disjoint rows of the cut, with at most |S complement|-1 neighbours each
outside S. No expansion or no-overfull oracle is an input.
-/
namespace OverfullWork.PaperSmallCutGeometry
open SimpleGraph Finset OddCutDeficit PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem selected_degrees_le_cut_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S A : Finset V) (hA : A⊆Sᶜ) :
    (∑v∈A,H.degree v)≤cutEdges H S+A.card*(Sᶜ.card-1) := by
  have hRow:∀v∈A,H.degree v≤neighboursIn H S v+(Sᶜ.card-1):=by
    intro v hv
    have hh:=TrimmingResidualOddGeometry.degree_add_one_le_boundary_add_complement H S v (hA hv)
    have hp:0<Sᶜ.card:=card_pos.mpr ⟨v,hA hv⟩
    omega
  have hCut:cutEdges H S=∑v∈Sᶜ,neighboursIn H S v:=
    MaximumOddCutPacking.cut_eq_sum_neighboursIn H S Sᶜ disjoint_compl_right
      (fun _ _ v _=>by by_cases hv:v∈S <;>simp_all)
  have hSum:(∑v∈A,neighboursIn H S v)≤cutEdges H S:=by
    rw [hCut]
    exact sum_le_sum_of_subset_of_nonneg hA (fun _ _ _=>Nat.zero_le _)
  calc
    _ ≤ ∑v∈A,(neighboursIn H S v+(Sᶜ.card-1)) := sum_le_sum hRow
    _ = (∑v∈A,neighboursIn H S v)+A.card*(Sᶜ.card-1) := by rw [sum_add_distrib];simp
    _ ≤ _ := Nat.add_le_add_right hSum _

theorem pair_degrees_le_cut_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈Sᶜ) (hv : v∈Sᶜ) (hne : u≠v) :
    H.degree u+H.degree v≤cutEdges H S+2*(Sᶜ.card-1) := by
  simpa only [card_pair hne,sum_pair hne] using
    selected_degrees_le_cut_add H S {u,v} (by intro w hw;simp only [mem_insert,mem_singleton] at hw;rcases hw with rfl|rfl <;>assumption)

theorem triple_degrees_le_cut_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v w : V) (hu : u∈Sᶜ) (hv : v∈Sᶜ) (hw : w∈Sᶜ)
    (huv : u≠v) (huw : u≠w) (hvw : v≠w) :
    H.degree u+H.degree v+H.degree w≤cutEdges H S+3*(Sᶜ.card-1) := by
  have hh:=selected_degrees_le_cut_add H S {u,v,w} (by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl <;>assumption)
  simpa [huv,huw,hvw,Nat.add_assoc] using hh

theorem cut_insert_identity (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (x : V) (hx : x∉U) :
    cutEdges H (insert x U)+2*(Plantholt.nbIn H U x).card=cutEdges H U+H.degree x := by
  have hU:=internal_cut_identity H U
  have hT:=internal_cut_identity H (insert x U)
  rw [InducedEdgeExchange.internal_edges_insert H U x hx,sum_insert hx] at hT
  omega

theorem complement_card_le_missing_add (X S : Finset V) :
    Sᶜ.card≤(X\S).card+Xᶜ.card := by
  have hPart:Sᶜ=(X\S)∪(Sᶜ∩Xᶜ):=by
    ext v
    simp only [mem_compl,mem_union,mem_sdiff,mem_inter]
    tauto
  have hUnion:=card_union_le (X\S) (Sᶜ∩Xᶜ)
  have hInter:=card_le_card (inter_subset_right (s₁:=Sᶜ) (s₂:=Xᶜ))
  rw [←hPart] at hUnion
  omega

theorem inside_insert_of_no_neighbours (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (x v : V) (hNo : ∀w∈Z,¬H.Adj x w) :
    (Plantholt.nbIn H (insert v Z) x).card=(if H.Adj x v then 1 else 0) := by
  by_cases hAdj:H.Adj x v
  · have hEq:Plantholt.nbIn H (insert v Z) x={v}:=by
      ext w
      simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset,mem_insert,mem_singleton]
      constructor
      · rintro ⟨hA,he|hw⟩
        · exact he
        · exact (hNo w hw hA).elim
      · intro he
        subst w
        exact ⟨hAdj,Or.inl rfl⟩
    rw [hEq,card_singleton,if_pos hAdj]
  · have hEq:Plantholt.nbIn H (insert v Z) x=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hh:=mem_filter.mp hw
      have hA:H.Adj x w:=by simpa only [mem_neighborFinset] using hh.1
      rcases mem_insert.mp hh.2 with he|hw
      · exact hAdj (he ▸ hA)
      · exact hNo w hw hA
    rw [hEq,card_empty,if_neg hAdj]

/-- The local concave quadratic behind the small-complement argument.
Its endpoints are controlled by a high-degree margin and an above-half
gap. All products are ordinary natural-number arithmetic. -/
theorem quadratic_boundary_lower (D b k n q : ℕ)
    (hq : 2≤q) (hSize : q+D+1≤n)
    (hDense : n+b+k+3≤2*D) (hSmall : 4*(b+k+2)≤D) :
    D≤q*(D-b-k-q) := by
  have hGap:4≤D-b-k-q:=by omega
  have hAdd:(D-b-k-q)+b+k+q=D:=by omega
  by_cases hqSmall:4*q≤D
  · have hLarge: D≤2*(D-b-k-q):=by omega
    have hMul:=Nat.mul_le_mul_right (D-b-k-q) hq
    omega
  · have hMul:=Nat.mul_le_mul_left q hGap
    omega

/-- Localization in an almost-regular core, without criticality of H.
The quantitative margins imply the small-cut consequence of expansion
needed here; general robust Hamilton layouts are not asserted. -/
theorem overfull_omits_at_most_two (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (x : V) (b k : ℕ) (hY : Xᶜ.card≤k)
    (hHigh : ∀v∈X,v≠x → H.maxDegree≤H.degree v+b)
    (hDense : Fintype.card V+b+k+3≤2*H.maxDegree)
    (hSmall : 4*(b+k+2)≤H.maxDegree)
    (S : Finset V) (hOdd : Odd S.card)
    (hOver : H.maxDegree*(S.card/2) < internalEdges H S) :
    (X\S).card≤2 := by
  by_contra hMany
  let A:=(X\S).erase x
  let q:=A.card
  have hq:2≤q:=by
    by_cases hx:x∈X\S
    · have hh:=card_erase_of_mem hx
      change q=(X\S).card-1 at hh
      omega
    · have hh:=erase_eq_of_notMem hx
      change A=X\S at hh
      dsimp only [q]
      rw [hh]
      omega
  have hA:A⊆Sᶜ:=by intro v hv;exact mem_compl.mpr (mem_sdiff.mp (mem_erase.mp hv).2).2
  have hBig:H.maxDegree<S.card:=by
    have hSimple:=NearTightOddSetGeometry.internalEdges_le_card_mul_half H S hOdd
    by_contra hNot
    have hh:=Nat.mul_le_mul_right (S.card/2) (show S.card≤H.maxDegree by omega)
    omega
  have hSize:q+H.maxDegree+1≤Fintype.card V:=by
    have hc:=card_le_card hA
    have ht:=card_add_card_compl S
    omega
  have hPart:Sᶜ=(X\S)∪(Sᶜ∩Xᶜ):=by ext v;simp only [mem_compl,mem_union,mem_sdiff,mem_inter];tauto
  have hMissing:(X\S).card≤q+1:=by
    by_cases hx:x∈X\S
    · have hh:=card_erase_of_mem hx
      change q=(X\S).card-1 at hh
      omega
    · have hh:=erase_eq_of_notMem hx
      change A=X\S at hh
      dsimp only [q]
      rw [hh]
      omega
  have hComp:Sᶜ.card≤q+k+1:=by
    have hc:=card_union_le (X\S) (Sᶜ∩Xᶜ)
    have hy:=card_le_card (inter_subset_right (s₁:=Sᶜ) (s₂:=Xᶜ))
    rw [←hPart] at hc
    omega
  have hSum:q*H.maxDegree≤(∑v∈A,H.degree v)+q*b:=by
    calc
      _ = ∑_v∈A,H.maxDegree := by simp [q]
      _ ≤ ∑v∈A,(H.degree v+b) := by
        apply sum_le_sum
        intro v hv
        exact hHigh v (mem_sdiff.mp (mem_erase.mp hv).2).1 (mem_erase.mp hv).1
      _ = _ := by rw [sum_add_distrib];simp [q]
  have hCut:=selected_degrees_le_cut_add H S A hA
  have hCost:q*(Sᶜ.card-1)≤q*(q+k):=Nat.mul_le_mul_left q (by omega)
  have hLower:=quadratic_boundary_lower H.maxDegree b k (Fintype.card V) q hq hSize hDense hSmall
  have hGap:(H.maxDegree-b-k-q)+b+k+q=H.maxDegree:=by omega
  have hProduct:=congrArg (fun t=>q*t) hGap
  have hCutLower:H.maxDegree≤cutEdges H S:=by
    change (∑v∈A,H.degree v)≤cutEdges H S+q*(Sᶜ.card-1) at hCut
    nlinarith only [hSum,hCut,hCost,hLower,hProduct]
  have hId:=internal_cut_deficit_identity H H.maxDegree H.degree_le_maxDegree S
  obtain ⟨t,ht⟩:=hOdd
  have hHalf:S.card/2=t:=by omega
  have hExpand:H.maxDegree*S.card=2*(H.maxDegree*t)+H.maxDegree:=by rw [ht];ring
  rw [hExpand] at hId
  rw [hHalf] at hOver
  omega

end OverfullWork.PaperSmallCutGeometry
