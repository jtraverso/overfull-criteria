module

public import OverfullWork.LowVertexMatchingAbsorption

@[expose] public section


/-! # Actual neighbour representatives for the low skeleton endpoints

This is the finite greedy input in CMS Claim 4.1(6). A numerical degree
budget constructs a matching from the exceptional endpoints to fresh core
vertices. Combining these partners with the endpoints already in the core
gives an injective representative map. No projection is assumed.
-/
namespace OverfullWork.LowSkeletonProjection
open SimpleGraph Finset LowVertexMatchingAbsorption
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000

/-- If every source has at least as many neighbours outside a forbidden
set as there are sources, Hall constructs an actual distinct selection. -/
theorem exists_fresh_neighbour_selection (G : SimpleGraph V) [DecidableRel G.Adj]
    (L B : Finset V) (hdegree : ∀u∈L,B.card+L.card≤G.degree u) :
    ∃f : L → ↥(Bᶜ : Finset V),Function.Injective f ∧ ∀u,G.Adj u.val (f u).val := by
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  let R:=Bᶜ
  let rel:=fun (u:L) (v:R) => G.Adj u.val v.val
  have hrow : ∀u:L,L.card≤(univ.filter (rel u)).card := by
    intro u
    have heq : R.filter (G.Adj u.val)=G.neighborFinset u.val\B := by
      ext v
      simp only [R,mem_filter,mem_compl,mem_neighborFinset,mem_sdiff]
      tauto
    change L.card≤(univ.filter (fun v:R => G.Adj u.val v.val)).card
    rw [DenseHall.subtype_filter_card R (G.Adj u.val),heq]
    have hh:=card_le_card_sdiff_add_card (s:=G.neighborFinset u.val) (t:=B)
    rw [card_neighborFinset_eq_degree] at hh
    have hd:=hdegree u.val u.property
    omega
  have hall : ∀S:Finset L,S.card≤(univ.filter fun v:R => ∃u∈S,rel u v).card := by
    intro S
    rcases S.eq_empty_or_nonempty with he|⟨u,hu⟩
    · simp only [he,card_empty,Nat.zero_le]
    · have hsub : univ.filter (rel u)⊆univ.filter (fun v:R => ∃u∈S,rel u v) := by
        intro v hv
        exact mem_filter.mpr ⟨mem_univ _,u,hu,(mem_filter.mp hv).2⟩
      have hc : S.card≤L.card := by simpa only [Fintype.card_coe] using card_le_univ S
      exact hc.trans ((hrow u).trans (card_le_card hsub))
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hall

/-- Representatives fix the original core endpoints; projected endpoints
use an actual matching and avoid both all original endpoints and Z. -/
structure Projection (G : SimpleGraph V) (A U Z : Finset V) where
  representative : A → ↥(Uᶜ : Finset V)
  injective : Function.Injective representative
  fixed : ∀a:A,a.val∉U → (representative a).val=a.val
  neighbour : ∀a:A,a.val∈U → G.Adj a.val (representative a).val
  fresh : ∀a:A,a.val∈U → (representative a).val∉A∪Z
  matching : SimpleGraph V
  matching_le : matching≤G
  isMatching : OneFactor.IsMatchingGraph matching
  covers : ∀u∈A∩U,∃!v,matching.Adj u v
  selected : ∀a:A,a.val∈U → matching.Adj a.val (representative a).val
  endpoints : ∀u v,matching.Adj u v →
    (u∈A∩U ∧ v∉U ∧ v∉A∪Z) ∨ (v∈A∩U ∧ u∉U ∧ u∉A∪Z)

/-- The whole projection, including its matching, is constructed from a
numerical minimum-degree budget on the endpoints that need projecting.
Z may be any additional forbidden set. -/
theorem exists_projection (G : SimpleGraph V) [DecidableRel G.Adj]
    (A U Z : Finset V)
    (hdegree : ∀u∈A∩U,U.card+A.card+Z.card≤G.degree u) :
    Nonempty (Projection G A U Z) := by
  let L:=A∩U
  let B:=(U∪(A\U))∪Z
  have hB : B.card+L.card≤U.card+A.card+Z.card := by
    have h₁:=card_union_le (U∪(A\U)) Z
    have h₂:=card_union_le U (A\U)
    have h₃:=card_sdiff_add_card_inter A U
    change B.card+L.card≤_
    dsimp only [B,L]
    omega
  obtain ⟨f,hf,hadj⟩:=exists_fresh_neighbour_selection G L B
    (fun u hu => hB.trans (hdegree u hu))
  have hnot : ∀u:L,(f u).val∉U ∧ (f u).val∉A∪Z := by
    intro u
    have hh : (f u).val∉B:=mem_compl.mp (f u).property
    have hu : (f u).val∉U := fun he => hh (mem_union_left _ (mem_union_left _ he))
    refine ⟨hu,?_⟩
    intro he
    rcases mem_union.mp he with ha|hz
    · exact hh (mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨ha,hu⟩)))
    · exact hh (mem_union_right _ hz)
  let ρ : A → ↥(Uᶜ : Finset V):=fun a =>
    if ha:a.val∈U then ⟨(f ⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩).val,
      mem_compl.mpr (hnot ⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩).1⟩
    else ⟨a.val,mem_compl.mpr ha⟩
  have hρlow : ∀a:A,∀ha:a.val∈U,
      (ρ a).val=(f ⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩).val := by
    intro a ha
    simp only [ρ,dif_pos ha]
  have hρfixed : ∀a:A,a.val∉U → (ρ a).val=a.val := by
    intro a ha
    simp only [ρ,dif_neg ha]
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have he:=congrArg Subtype.val hab
    by_cases ha:a.val∈U
    · rw [hρlow a ha] at he
      by_cases hb:b.val∈U
      · rw [hρlow b hb] at he
        exact Subtype.ext (congrArg (fun z:L => z.val) (hf (Subtype.ext he)))
      · rw [hρfixed b hb] at he
        exact False.elim ((hnot ⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩).2
          (mem_union_left _ (he ▸ b.property)))
    · rw [hρfixed a ha] at he
      by_cases hb:b.val∈U
      · rw [hρlow b hb] at he
        exact False.elim ((hnot ⟨b.val,mem_inter.mpr ⟨b.property,hb⟩⟩).2
          (mem_union_left _ (he ▸ a.property)))
      · rw [hρfixed b hb] at he
        exact Subtype.ext he
  let fL : L → ↥(Lᶜ : Finset V):=fun u =>
    ⟨(f u).val,mem_compl.mpr (fun he => (hnot u).1 (mem_inter.mp he).2)⟩
  have hfL : Function.Injective fL := by
    intro a b he
    exact hf (Subtype.ext (congrArg (fun z:↥(Lᶜ : Finset V) => z.val) he))
  have hgraph:=selectionGraph_isMatching L fL hfL
  have hle : selectionGraph L fL≤G:=selectionGraph_le L fL hadj
  refine ⟨⟨ρ,hρinj,hρfixed,?_,?_,selectionGraph L fL,hle,
    hgraph.1,hgraph.2,?_,?_⟩⟩
  · intro a ha
    rw [hρlow a ha]
    exact hadj ⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩
  · intro a ha
    rw [hρlow a ha]
    exact (hnot _).2
  · intro a ha
    rw [hρlow a ha]
    exact Or.inl ⟨⟨a.val,mem_inter.mpr ⟨a.property,ha⟩⟩,rfl,rfl⟩
  · intro u v huv
    rcases huv with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
    · exact Or.inl ⟨a.property,(hnot a).1,(hnot a).2⟩
    · exact Or.inr ⟨a.property,(hnot a).1,(hnot a).2⟩

/-- CMS Step 2 needs no extra forbidden vertices: degree at least
|U|+|A| on each exceptional endpoint suffices. -/
theorem exists_projection_without_extra_forbidden (G : SimpleGraph V) [DecidableRel G.Adj]
    (A U : Finset V) (hdegree : ∀u∈A∩U,U.card+A.card≤G.degree u) :
    Nonempty (Projection G A U ∅) := by
  apply exists_projection G A U ∅
  simpa only [card_empty,Nat.add_zero] using hdegree

end OverfullWork.LowSkeletonProjection
