module

public import OverfullWork.ChenShanReserveCommonFamilies
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}
variable (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
variable (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)

noncomputable def sampledCrossingArcs
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool) :
    Finset (TripartiteVertex A B W × TripartiteVertex A B W) :=
  (univ.filter fun e => sample e = true ∧ crossingArc S i F P Q e.1 (crossingNext e.1) e.2.1 e.2.2).map
    (crossingArcSlotEmbedding S i)

theorem sampledCrossingArcs_mem_slot
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext) :
    crossingArcSlotEmbedding S i e ∈ sampledCrossingArcs S i F P Q sample ↔
      sample e = true ∧ crossingArc S i F P Q e.1 (crossingNext e.1) e.2.1 e.2.2 := by
  simp [sampledCrossingArcs]

theorem sampledCrossingArcs_supported
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    {a b : TripartiteVertex A B W} (h : (a,b) ∈ sampledCrossingArcs S i F P Q sample) :
    tripartiteArc F P Q a b := by
  unfold sampledCrossingArcs at h
  obtain ⟨e,he,hr⟩ := mem_map.mp h
  have ht := (mem_filter.mp he).2.2
  change tripartiteArc F P Q (crossingArcSlotEmbedding S i e).1
    (crossingArcSlotEmbedding S i e).2 at ht
  rwa [hr] at ht

omit [Fintype A] [Fintype B] [Fintype W] in
private theorem tripartite_arc_asymm {a b : TripartiteVertex A B W}
    (h : tripartiteArc F P Q a b) : ¬tripartiteArc F P Q b a := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> simp [tripartiteArc] at h ⊢

def sampledCrossingAdjacent
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (a b : TripartiteVertex A B W) : Prop :=
  (a,b) ∈ sampledCrossingArcs S i F P Q sample ∨ (b,a) ∈ sampledCrossingArcs S i F P Q sample

theorem sampledCrossingAdjacent_iff
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext)
    {a b : TripartiteVertex A B W}
    (hArc : let h := crossingArcSlotEmbedding S i e; tripartiteArc F P Q h.1 h.2)
    (hEnds : crossingArcSlotEmbedding S i e = (a,b) ∨ crossingArcSlotEmbedding S i e = (b,a)) :
    sampledCrossingAdjacent S i F P Q sample a b ↔ sample e = true := by
  have hMem := sampledCrossingArcs_mem_slot S i F P Q sample e
  have hProper : crossingArc S i F P Q e.1 (crossingNext e.1) e.2.1 e.2.2 := hArc
  rw [and_iff_left hProper] at hMem
  unfold sampledCrossingAdjacent
  rcases hEnds with h | h
  · rw [h] at hMem
    have h₁ : tripartiteArc F P Q a b := by simpa only [h] using hArc
    have h₂ : (b,a) ∉ sampledCrossingArcs S i F P Q sample :=
      fun hh => tripartite_arc_asymm F P Q h₁ (sampledCrossingArcs_supported S i F P Q sample hh)
    simpa only [h₂,or_false] using hMem
  · rw [h] at hMem
    have h₁ : tripartiteArc F P Q b a := by simpa only [h] using hArc
    have h₂ : (a,b) ∉ sampledCrossingArcs S i F P Q sample :=
      fun hh => tripartite_arc_asymm F P Q h₁ (sampledCrossingArcs_supported S i F P Q sample hh)
    simpa only [h₂,false_or] using hMem

noncomputable def sampledCrossingCommonNeighbors
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (x y : TripartiteVertex A B W) : Finset (TripartiteVertex A B W) :=
  (S.vertices (i+1)).filter
    (fun z => sampledCrossingAdjacent S i F P Q sample x z ∧ sampledCrossingAdjacent S i F P Q sample y z)

/-- A common-neighbor count in the sampled graph equals the paired
Bernoulli count in the shared sample space. -/
theorem crossing_common_count_eq_graph
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (x y : TripartiteVertex A B W)
    (f : (↥(crossingCommonCandidates S i F P Q x y) × Bool) ↪
      CyclicEdgeSlot (V := CrossingPart S i) crossingNext)
    (hf : ∀ z b, let out := if b then y else x
      let arc := crossingArcSlotEmbedding S i (f (z,b))
      (arc = (out,z.1) ∨ arc = (z.1,out)) ∧ tripartiteArc F P Q arc.1 arc.2) :
    count univ (fun z => sample (f (z,false)) && sample (f (z,true))) =
      ((sampledCrossingCommonNeighbors S i F P Q sample x y).card : ℝ) := by
  let Z := crossingCommonCandidates S i F P Q x y
  let Good (z : TripartiteVertex A B W) :=
    sampledCrossingAdjacent S i F P Q sample x z ∧ sampledCrossingAdjacent S i F P Q sample y z
  have hHit (z : ↥Z) : (sample (f (z,false)) && sample (f (z,true))) = true ↔ Good z := by
    have h₁ := hf z false
    have h₂ := hf z true
    rw [Bool.and_eq_true]
    exact and_congr
      (sampledCrossingAdjacent_iff S i F P Q sample _ h₁.2 h₁.1).symm
      (sampledCrossingAdjacent_iff S i F P Q sample _ h₂.2 h₂.1).symm
  have hEq : (univ.filter (fun z : Z => (sample (f (z,false)) && sample (f (z,true))) = true)) =
      univ.filter (fun z : Z => Good z.1) := by
    ext z
    simp only [mem_filter,mem_univ,true_and,hHit]
  have hGraph : Z.filter Good = sampledCrossingCommonNeighbors S i F P Q sample x y := by
    ext z
    simp only [Z,crossingCommonCandidates,sampledCrossingCommonNeighbors,mem_filter]
    constructor
    · exact fun ⟨⟨hz,_⟩,hg⟩ => ⟨hz,hg⟩
    · intro ⟨hz,hg⟩
      have hAdj {a b} (hab : sampledCrossingAdjacent S i F P Q sample a b) :
          tripartiteAdjacent F P Q a b :=
        hab.imp (sampledCrossingArcs_supported S i F P Q sample)
          (sampledCrossingArcs_supported S i F P Q sample)
      exact ⟨⟨hz,hAdj hg.1,hAdj hg.2⟩,hg⟩
  unfold count
  rw [hEq,← hGraph]
  apply congrArg (fun z : ℕ => (z:ℝ))
  apply card_bij (fun z _ => z.1)
  · intro z hz
    exact mem_filter.mpr ⟨z.2,(mem_filter.mp hz).2⟩
  · intro z _ w _ h
    exact Subtype.ext h
  · intro z hz
    obtain ⟨hZ,hP⟩ := mem_filter.mp hz
    exact ⟨⟨z,hZ⟩,mem_filter.mpr ⟨mem_univ _,hP⟩,rfl⟩


theorem crossingCommonCandidates_comm (x y : TripartiteVertex A B W) :
    crossingCommonCandidates S i F P Q x y = crossingCommonCandidates S i F P Q y x := by
  ext z
  simp only [crossingCommonCandidates,mem_filter,and_comm]

theorem crossingCommonCandidates_left_right (a : A) (b : B) :
    crossingCommonCandidates S i F P Q (.inl a) (.inr (.inl b)) =
      ((S.colors (i+1)).filter (fun w => P a w ∧ Q b w)).map
        (Function.Embedding.inr.trans Function.Embedding.inr) := by
  ext z
  simp only [crossingCommonCandidates,mem_filter]
  rcases z with z | (z | z) <;>
    simp [tripartiteAdjacent,tripartiteArc,mem_map,mem_filter,
      mem_vertices_left,mem_vertices_right,mem_vertices_color]

theorem crossingCommonCandidates_left_color (a : A) (w : W) :
    crossingCommonCandidates S i F P Q (.inl a) (.inr (.inr w)) =
      ((S.right (i+1)).filter (fun b => F a b ∧ Q b w)).map
        (Function.Embedding.inl.trans Function.Embedding.inr) := by
  ext z
  simp only [crossingCommonCandidates,mem_filter]
  rcases z with z | (z | z) <;>
    simp [tripartiteAdjacent,tripartiteArc,mem_map,mem_filter,
      mem_vertices_left,mem_vertices_right,mem_vertices_color]

theorem crossingCommonCandidates_right_color (b : B) (w : W) :
    crossingCommonCandidates S i F P Q (.inr (.inl b)) (.inr (.inr w)) =
      ((S.left (i+1)).filter (fun a => F a b ∧ P a w)).map Function.Embedding.inl := by
  ext z
  simp only [crossingCommonCandidates,mem_filter]
  rcases z with z | (z | z) <;>
    simp [tripartiteAdjacent,tripartiteArc,mem_map,mem_filter,
      mem_vertices_left,mem_vertices_right,mem_vertices_color]

/-- The lower threshold in (R3) applies to the untyped candidate
finset for each adjacent pair. -/
theorem adjacent_crossing_common_candidate_card
    {δ : ℝ} (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hInner : ρ*(nestedCoreSize ρ m i : ℝ) ≤ nestedCoreSize ρ m (i+1))
    (hδ : 0 ≤ δ) (hSmall : 18*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    {x y : TripartiteVertex A B W} (hx : x ∈ S.vertices i) (hy : y ∈ S.vertices i)
    (hxy : tripartiteAdjacent F P Q x y) :
    ρ*(nestedCoreSize ρ m i : ℝ)/3 ≤ (crossingCommonCandidates S i F P Q x y).card := by
  obtain ⟨hAB,hAW,hBW⟩ := crossing_common_neighbor_candidates hBounds hi hHalf hInner hδ hSmall hRound
  rcases x with a | (b | w) <;> rcases y with a' | (b' | w') <;>
    simp only [tripartiteAdjacent,tripartiteArc,or_false,false_or,or_self] at hxy
  · rw [crossingCommonCandidates_left_right,card_map]
    exact hAB a ((mem_vertices_left S i a).mp hx) b' ((mem_vertices_right S i b').mp hy)
  · rw [crossingCommonCandidates_left_color,card_map]
    exact hAW a ((mem_vertices_left S i a).mp hx) w' ((mem_vertices_color S i w').mp hy)
  · rw [crossingCommonCandidates_comm S i F P Q (.inr (.inl b)),crossingCommonCandidates_left_right,card_map]
    exact hAB a' ((mem_vertices_left S i a').mp hy) b ((mem_vertices_right S i b).mp hx)
  · rw [crossingCommonCandidates_right_color,card_map]
    exact hBW b ((mem_vertices_right S i b).mp hx) w' ((mem_vertices_color S i w').mp hy)
  · rw [crossingCommonCandidates_comm S i F P Q (.inr (.inr w)),crossingCommonCandidates_left_color,card_map]
    exact hAW a' ((mem_vertices_left S i a').mp hy) w ((mem_vertices_color S i w).mp hx)
  · rw [crossingCommonCandidates_comm S i F P Q (.inr (.inr w)),crossingCommonCandidates_right_color,card_map]
    exact hBW b' ((mem_vertices_right S i b').mp hy) w ((mem_vertices_color S i w).mp hx)


/-- A single-neighborhood Bernoulli count is the corresponding
sampled degree, possibly restricted to a further predicate on neighbors. -/
theorem crossing_neighborhood_count_eq_graph
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (x : TripartiteVertex A B W) (Z : Finset (TripartiteVertex A B W))
    (Good : TripartiteVertex A B W → Prop)
    (f : ↥(Z.filter (tripartiteAdjacent F P Q x)) ↪ CyclicEdgeSlot (V := CrossingPart S i) crossingNext)
    (hf : ∀ z, let arc := crossingArcSlotEmbedding S i (f z)
      (arc = (x,z.1) ∨ arc = (z.1,x)) ∧ tripartiteArc F P Q arc.1 arc.2) :
    count ((univ.filter (fun z : ↥(Z.filter (tripartiteAdjacent F P Q x)) => Good z.1)).map f) sample =
      ((Z.filter (fun z => sampledCrossingAdjacent S i F P Q sample x z ∧ Good z)).card : ℝ) := by
  let N := Z.filter (tripartiteAdjacent F P Q x)
  have hEq : ((univ.filter (fun z : N => Good z.1)).map f).filter (fun e => sample e) =
      (univ.filter (fun z : N => Good z.1 ∧ sample (f z) = true)).map f := by
    ext e
    constructor
    · intro he
      obtain ⟨hm,hs⟩ := mem_filter.mp he
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hm
      exact mem_map.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2,hs⟩,rfl⟩
    · intro he
      obtain ⟨z,hz,rfl⟩ := mem_map.mp he
      obtain ⟨_,hg,hs⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_map.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,hg⟩,rfl⟩,hs⟩
  unfold count
  rw [hEq,card_map]
  apply congrArg (fun d : ℕ => (d:ℝ))
  apply card_bij (fun z _ => z.1)
  · intro z hz
    obtain ⟨_,hg,hs⟩ := mem_filter.mp hz
    have hAdj := (sampledCrossingAdjacent_iff S i F P Q sample _ (hf z).2 (hf z).1).mpr hs
    exact mem_filter.mpr ⟨(mem_filter.mp z.2).1,hAdj,hg⟩
  · intro z _ w _ h
    exact Subtype.ext h
  · intro z hz
    obtain ⟨hzZ,hAdj,hGood⟩ := mem_filter.mp hz
    have hzN : z ∈ N := mem_filter.mpr ⟨hzZ,
      hAdj.imp (sampledCrossingArcs_supported S i F P Q sample)
        (sampledCrossingArcs_supported S i F P Q sample)⟩
    let t : N := ⟨z,hzN⟩
    have ht := (sampledCrossingAdjacent_iff S i F P Q sample (f t) (hf t).2 (hf t).1).mp hAdj
    exact ⟨t,mem_filter.mpr ⟨mem_univ _,hGood,ht⟩,rfl⟩


theorem sampledCrossingArcs_crosses
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    {a b : TripartiteVertex A B W} (h : (a,b) ∈ sampledCrossingArcs S i F P Q sample) :
    CrossesNestedPrefix S i a b := by
  unfold sampledCrossingArcs at h
  obtain ⟨e,_,he⟩ := mem_map.mp h
  have hc := crossing_slot_crosses S i e
  dsimp only at hc
  rwa [he] at hc

theorem sampledCrossingOut_degree
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (j : Fin 6) (a : CrossingPart S i j)
    [DecidablePred (fun e : TripartiteVertex A B W × TripartiteVertex A B W =>
      e.1 = crossingVertex S i j a)] :
    (((sampledCrossingArcs S i F P Q sample).filter
      (fun e => e.1 = crossingVertex S i j a)).card : ℝ) =
      count (cyclicOutNeighbors crossingNext (fun t => crossingArc S i F P Q t (crossingNext t)) j a)
        sample := by
  let G := sampledCrossingArcs S i F P Q sample
  let N := cyclicOutNeighbors crossingNext (fun t => crossingArc S i F P Q t (crossingNext t)) j a
  let f := crossingArcSlotEmbedding S i
  have he : G.filter (fun e => e.1 = crossingVertex S i j a) = (N.filter (fun e => sample e)).map f := by
    ext e
    constructor
    · intro h
      obtain ⟨hg,hv⟩ := mem_filter.mp h
      obtain ⟨q,hq,hqeq⟩ := mem_map.mp hg
      have hAnchor : (⟨q.1,q.2.1⟩ : Σ t, CrossingPart S i t) = ⟨j,a⟩ :=
        (crossingVertexEmbedding S i).injective ((congrArg Prod.fst hqeq).trans hv)
      rcases q with ⟨t,b,c⟩
      have hh := congrArg Sigma.fst hAnchor
      dsimp only at hh
      subst t
      have hb := eq_of_heq (Sigma.mk.inj_iff.mp hAnchor).2
      change b = a at hb
      subst b
      have hSample := (mem_filter.mp hq).2
      refine mem_map.mpr ⟨⟨j,a,c⟩,mem_filter.mpr ⟨?_,hSample.1⟩,hqeq⟩
      exact mem_map.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,hSample.2⟩,rfl⟩
    · intro h
      obtain ⟨q,hq,rfl⟩ := mem_map.mp h
      obtain ⟨hqN,hqSample⟩ := mem_filter.mp hq
      obtain ⟨c,hc,rfl⟩ := mem_map.mp hqN
      have hArc := (mem_filter.mp hc).2
      exact mem_filter.mpr ⟨(sampledCrossingArcs_mem_slot S i F P Q sample _).mpr
        ⟨hqSample,hArc⟩,rfl⟩
  change ((G.filter (fun e => e.1 = crossingVertex S i j a)).card : ℝ) = count N sample
  rw [he,card_map]
  rfl

theorem sampledCrossingIn_degree
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (j : Fin 6) (b : CrossingPart S i (crossingNext j))
    [DecidablePred (fun e : TripartiteVertex A B W × TripartiteVertex A B W =>
      e.2 = crossingVertex S i (crossingNext j) b)] :
    (((sampledCrossingArcs S i F P Q sample).filter
      (fun e => e.2 = crossingVertex S i (crossingNext j) b)).card : ℝ) =
      count (cyclicInNeighbors crossingNext (fun t => crossingArc S i F P Q t (crossingNext t)) j b)
        sample := by
  let G := sampledCrossingArcs S i F P Q sample
  let N := cyclicInNeighbors crossingNext (fun t => crossingArc S i F P Q t (crossingNext t)) j b
  let f := crossingArcSlotEmbedding S i
  have he : G.filter (fun e => e.2 = crossingVertex S i (crossingNext j) b) =
      (N.filter (fun e => sample e)).map f := by
    ext e
    constructor
    · intro h
      obtain ⟨hg,hv⟩ := mem_filter.mp h
      obtain ⟨q,hq,hqeq⟩ := mem_map.mp hg
      have hAnchor : (⟨crossingNext q.1,q.2.2⟩ : Σ t, CrossingPart S i t) = ⟨crossingNext j,b⟩ :=
        (crossingVertexEmbedding S i).injective ((congrArg Prod.snd hqeq).trans hv)
      rcases q with ⟨t,a,c⟩
      have hh := congrArg Sigma.fst hAnchor
      have ht : t=j := crossingNext.injective hh
      subst t
      have hc := eq_of_heq (Sigma.mk.inj_iff.mp hAnchor).2
      change c = b at hc
      subst c
      have hSample := (mem_filter.mp hq).2
      refine mem_map.mpr ⟨⟨j,a,b⟩,mem_filter.mpr ⟨?_,hSample.1⟩,hqeq⟩
      exact mem_map.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,hSample.2⟩,rfl⟩
    · intro h
      obtain ⟨q,hq,rfl⟩ := mem_map.mp h
      obtain ⟨hqN,hqSample⟩ := mem_filter.mp hq
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hqN
      have hArc := (mem_filter.mp ha).2
      exact mem_filter.mpr ⟨(sampledCrossingArcs_mem_slot S i F P Q sample _).mpr
        ⟨hqSample,hArc⟩,rfl⟩
  change ((G.filter (fun e => e.2 = crossingVertex S i (crossingNext j) b)).card : ℝ) = count N sample
  rw [he,card_map]
  rfl


private theorem crossing_vertex_has_incoming_index
    (v : TripartiteVertex A B W) (hv : v ∈ S.vertices i) :
    ∃ (j : Fin 6) (a : CrossingPart S i (crossingNext j)), crossingVertex S i (crossingNext j) a = v := by
  rcases v with a | (b | w)
  · have h := (mem_vertices_left S i a).mp hv
    by_cases h' : a ∈ S.left (i+1)
    · exact ⟨5,⟨a,h'⟩,rfl⟩
    · exact ⟨2,⟨a,mem_sdiff.mpr ⟨h,h'⟩⟩,rfl⟩
  · have h := (mem_vertices_right S i b).mp hv
    by_cases h' : b ∈ S.right (i+1)
    · exact ⟨3,⟨b,h'⟩,rfl⟩
    · exact ⟨0,⟨b,mem_sdiff.mpr ⟨h,h'⟩⟩,rfl⟩
  · have h := (mem_vertices_color S i w).mp hv
    by_cases h' : w ∈ S.colors (i+1)
    · exact ⟨1,⟨w,h'⟩,rfl⟩
    · exact ⟨4,⟨w,mem_sdiff.mpr ⟨h,h'⟩⟩,rfl⟩

private theorem incidentDegree_of_no_loop {V : Type*} (G : Finset (V × V)) (v : V)
    (hv : (v,v) ∉ G) :
    incidentDegree G v = (G.filter fun e => e.1=v).card+(G.filter fun e => e.2=v).card := by
  unfold incidentDegree
  rw [filter_or,card_union_of_disjoint]
  refine disjoint_left.mpr fun e h₁ h₂ => hv ?_
  have h : e=(v,v) := Prod.ext (mem_filter.mp h₁).2 (mem_filter.mp h₂).2
  exact h ▸ (mem_filter.mp h₁).1

private theorem no_incidence_degree_zero {V : Type*} (G : Finset (V × V)) (v : V)
    (h : ∀ e ∈ G, e.1 ≠ v ∧ e.2 ≠ v) : arcDivergence G v = 0 ∧ incidentDegree G v = 0 := by
  have hOut : G.filter (fun e => e.1=v) = ∅ := filter_eq_empty_iff.mpr fun e he => (h e he).1
  have hIn : G.filter (fun e => e.2=v) = ∅ := filter_eq_empty_iff.mpr fun e he => (h e he).2
  have hAll : G.filter (fun e => e.1=v ∨ e.2=v) = ∅ :=
    filter_eq_empty_iff.mpr fun e he hr => hr.elim (h e he).1 (h e he).2
  simp [arcDivergence,incidentDegree,hOut,hIn,hAll]

/-- The indexed degree tests are precisely the incident degree and
imbalance bounds for the sampled graph. -/
theorem sampledCrossingArc_degree_control
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (h : let E := fun t => crossingArc S i F P Q t (crossingNext t)
      ∀ j (a : CrossingPart S i (crossingNext j)),
        |count (cyclicOutNeighbors crossingNext E (crossingNext j) a) sample-
          count (cyclicInNeighbors crossingNext E j a) sample| ≤ D ∧
        count (cyclicOutNeighbors crossingNext E (crossingNext j) a) sample+
          count (cyclicInNeighbors crossingNext E j a) sample ≤ M) :
    ∀ v, let G := sampledCrossingArcs S i F P Q sample
      |(arcDivergence G v : ℝ)| ≤ D ∧ (incidentDegree G v : ℝ) ≤ M := by
  intro v
  dsimp only
  let G := sampledCrossingArcs S i F P Q sample
  have hNoLoops : (v,v) ∉ G := by
    intro hv
    have hArc := sampledCrossingArcs_supported S i F P Q sample hv
    exact tripartite_arc_asymm F P Q hArc hArc
  by_cases hv : v ∈ S.vertices i
  · obtain ⟨j,a,rfl⟩ := crossing_vertex_has_incoming_index S i v hv
    rw [incidentDegree_of_no_loop G _ hNoLoops,Nat.cast_add]
    simp only [arcDivergence,Int.cast_sub,Int.cast_natCast]
    rw [@sampledCrossingOut_degree,@sampledCrossingIn_degree]
    exact h j a
  · have hEnds {a b} (hab : (a,b) ∈ G) : a ∈ S.vertices i ∧ b ∈ S.vertices i := by
      have ht := sampledCrossingArcs_crosses S i F P Q sample hab
      have hSub := S.vertices_antitone (Nat.le_succ i)
      rcases ht with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact ⟨hSub ha,(mem_sdiff.mp hb).1⟩
      · exact ⟨(mem_sdiff.mp ha).1,hSub hb⟩
    have he := no_incidence_degree_zero G v (by
      rintro ⟨a,b⟩ hab
      exact ⟨fun ha => hv (ha ▸ (hEnds hab).1),fun hb => hv (hb ▸ (hEnds hab).2)⟩)
    change |(arcDivergence G v : ℝ)| ≤ D ∧ (incidentDegree G v : ℝ) ≤ M
    rw [he.1,he.2,Int.cast_zero,Nat.cast_zero,abs_zero]
    exact ⟨hD,hM⟩


theorem sampledCrossingArcs_subset_outside_inner
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool) :
    sampledCrossingArcs S i F P Q sample ⊆
      tripartiteArcs F P Q \ (S.vertices (i+1) ×ˢ S.vertices (i+1)) := by
  rintro ⟨x,y⟩ he
  have hArc := sampledCrossingArcs_supported S i F P Q sample he
  have hCut := sampledCrossingArcs_crosses S i F P Q sample he
  apply mem_sdiff.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ _,hArc⟩,fun hh => ?_⟩
  obtain ⟨hx,hy⟩ := mem_product.mp hh
  rcases hCut with ⟨_,hy'⟩ | ⟨hx',_⟩
  · exact (mem_sdiff.mp hy').2 hy
  · exact (mem_sdiff.mp hx').2 hx

end OverfullWork.ChenShan
