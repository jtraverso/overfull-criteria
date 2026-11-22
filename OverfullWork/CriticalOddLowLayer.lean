module

public import OverfullWork.CriticalOddCorePathPreparation
public import OverfullWork.CriticalEvenLowLayer
public import OverfullWork.OddLowLayerSeparation

@[expose] public section


/-! # Actual two-colour trimming with an odd low set

The fresh extra edge has its two projected arms in different prescribed
paths. This proves acyclicity of the actual union. Core degree demands,
two colours, the exact maximum-degree drop and residual uncolourability
are then consequences, without an assumed layout or colouring.
-/
namespace OverfullWork.CriticalOddLowLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open PaperLowSkeleton LowSkeletonProjection PathGraphRealization
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

structure Certificate (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) where
  layer : SimpleGraph V
  le_original : layer≤G
  acyclic : layer.IsAcyclic
  degree_le_two : ∀v,layer.degree v≤2
  colourable : layer.EdgeColorable 2
  core_two_cover : ∀v∉U,layer.degree v=2
  low_positive : ∀w∈lowVertices G,1≤layer.degree w
  low_endpoints : 2≤((lowVertices G).filter fun w=>layer.degree w=1).card
  residual_maxDegree : (G\layer).maxDegree=G.maxDegree-2
  residual_uncolourable : ¬(G\layer).EdgeColorable (G\layer).maxDegree

theorem certificate_of_prepared (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (s : CriticalOddCorePathPreparation.OddPrepared G U k) : Nonempty (Certificate G U) := by
  classical
  let W:=lowVertices G
  let H:=s.M⊔edge s.w s.b
  let A:=outerLeaves H W
  let Q:=H⊔s.projection.matching
  let K:=pathUnion s.paths
  let L:=Q⊔K
  let a:=fun i => (s.projection.representative (s.e (i,false))).val
  let b:=fun i => (s.projection.representative (s.e (i,true))).val
  have hab : ∀i,a i≠b i := by
    intro i he
    have he':=s.projection.injective (Subtype.ext he)
    have h:=congrArg Prod.snd (s.e.injective he')
    cases h
  have hend:=CriticalEvenLowLayer.representative_endpoints s.projection s.e
  have hAW : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro x hx hxW
    exact mem_compl.mp (mem_filter.mp hx).1 hxW
  have hf:=OddLowLayerSeparation.odd_union_isAcyclic s.M A W U
    (LowSkeletonPreparation.nonisolatedVertices H) s.projection s.low_subset hAW
    s.base_matching s.base_cross s.paths s.paths_simple s.paths_disjoint s.paths_off
    s.w s.a s.b s.w_low s.matched_arm s.left_arm_mem s.right_arm_mem s.fresh_outside
    (s.e.symm ⟨s.a,s.left_arm_mem⟩).1 (s.e.symm ⟨s.b,s.right_arm_mem⟩).1
    s.separated s.left_arm_on_path s.right_arm_on_path
  have hforest : L.IsAcyclic := by
    have heq : L=((s.M⊔s.projection.matching)⊔pathUnion s.paths)⊔edge s.w s.b := by
      dsimp [L,Q,H,K]
      ac_rfl
    rw [heq]
    exact hf
  have hKG : K≤G\Q := by
    intro x y h
    obtain ⟨i,hi⟩:=pathUnion_adj_iff s.paths |>.mp h
    exact ⟨le_original (s.paths i) hi,s.paths_avoid i x y hi⟩
  have hQG : Q≤G:=LowSkeletonAttachmentDegrees.attachment_le s.skeleton.le_graph s.projection
  have hQdeg : ∀v,Q.degree v≤2:=LowSkeletonAttachmentDegrees.degree_le_two s.low_subset
    s.skeleton.crosses s.skeleton.degree_le_two s.outside_degree_one s.projection
  have hKoff : ∀v∈U,K.degree v=0 := by
    intro v hv
    exact pathUnion_degree_outside s.paths (fun i hi => s.paths_off i v hi hv)
  have hKcore : ∀v∉U,K.degree v=
      if ∃x:A,(s.projection.representative x).val=v then 1 else 2 := by
    intro v hv
    by_cases he : ∃i,v=a i ∨ v=b i
    · rw [if_pos ((hend v).mpr he)]
      obtain ⟨i,hi⟩:=he
      rcases hi with rfl|rfl
      · exact pathUnion_degree_start s.paths s.paths_simple s.paths_disjoint i (hab i)
      · exact pathUnion_degree_end s.paths s.paths_simple s.paths_disjoint i (hab i)
    · rw [if_neg (fun h => he ((hend v).mp h))]
      obtain ⟨i,hi⟩:=s.paths_cover v hv
      rw [degree_eq_of_mem_support s.paths s.paths_disjoint i hi]
      exact degree_internal (s.paths i) (s.paths_simple i) hi
        (fun h=>he ⟨i,Or.inl h⟩) (fun h=>he ⟨i,Or.inr h⟩)
  obtain ⟨hLG,hdeg,hcore⟩:=SpanningLayerDegrees.realised_layer_degrees G Q K U
    (fun v=>∃x:A,(s.projection.representative x).val=v) hQG hKG hQdeg
    (by
      intro v hv
      have hh:=s.attachment_core_degree v hv
      split_ifs with he
      · dsimp only [A,H,W,Q] at *
        simpa only [if_pos he] using hh
      · dsimp only [A,H,W,Q] at *
        simpa only [if_neg he] using hh)
    (by
      intro v hv
      have hh:=hKcore v hv
      split_ifs with he
      · simpa only [if_pos he] using hh
      · simpa only [if_neg he] using hh) hKoff
  have hlow : ∀w∈W,L.degree w=H.degree w := by
    intro w hw
    rw [SpanningLayerDegrees.degree_union_of_le_residue G Q K hKG,hKoff w (s.low_subset hw),Nat.add_zero]
    exact LowSkeletonAttachmentDegrees.degree_on_low s.low_subset s.skeleton.crosses s.projection hw
  have hlpos : ∀w∈W,1≤L.degree w := by
    intro w hw
    rw [hlow w hw]
    exact s.skeleton.low_positive w hw
  have hlends : 2≤(W.filter fun w=>L.degree w=1).card := by
    have he : W.filter (fun w=>L.degree w=1)=W.filter (fun w=>H.degree w=1) := by
      apply filter_congr
      intro w hw
      rw [hlow w hw]
    rw [he]
    exact s.skeleton.low_endpoints
  have hcol : L.EdgeColorable 2:=
    TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  refine ⟨⟨L,hLG,hforest,?_,hcol,?_,?_,?_,?_,?_⟩⟩
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hdeg
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hcore
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hlpos
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hlends
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      SpanningLayerDegrees.maxDegree_residue_of_core_two_cover G L U hD hLG hexception hcore
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      SpanningLayerDegrees.critical_residue_of_core_two_cover G L U hc hD hLG hcol hexception hcore

theorem above_half_odd_low_layer (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Odd (lowVertices G).card → 3≤(lowVertices G).card →
        Nonempty (Certificate G (exceptions G G.maxDegree (Fintype.card V/(8*q)))) := by
  obtain ⟨q,hq,N,hprep⟩:=CriticalOddCorePathPreparation.above_half_odd_core_path_preparation.{u} ε hε
  refine ⟨q,hq,max N (16*q),?_⟩
  intro V _ _ G _ hn hc hdense hodd hthree
  obtain ⟨_,⟨s⟩⟩:=hprep G ((le_max_left _ _).trans hn) hc hdense hodd hthree
  have hn16 : 16*q≤Fintype.card V := (le_max_right _ _).trans hn
  have ha : 2≤Fintype.card V/(8*q) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    omega
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  apply certificate_of_prepared G _ _ hc (by omega) _ s
  intro v hv
  have hh:=(mem_filter.mp hv).2
  omega

end OverfullWork.CriticalOddLowLayer
