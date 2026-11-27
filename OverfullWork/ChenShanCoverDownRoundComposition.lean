module

public import OverfullWork.ChenShanCoverDownRound
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- The three phases of Step 2 partition precisely the edges removed in
one round. Here U is the induced interior arc set, not its vertex set. -/
theorem cover_down_round_arc_partition
    (G U R L D C M : Finset (V × V))
    (hU : U ⊆ G) (hR : R ⊆ G \ U) (hL : L ⊆ (G \ U) \ R)
    (hD : D ⊆ L) (hC : C ⊆ R) (hM : M ⊆ U) :
    let A := (((G \ U) \ R) \ L)
    let B := D ∪ C
    let E := ((R \ C) ∪ (L \ D)) ∪ M
    (A ∪ B) ∪ E = G \ (U \ M) ∧
      Disjoint A B ∧ Disjoint A E ∧ Disjoint B E := by
  intro A B E
  have hPart (e : V × V) :
      (e ∈ U → e ∈ G) ∧ (e ∈ R → e ∈ G ∧ e ∉ U) ∧
      (e ∈ L → (e ∈ G ∧ e ∉ U) ∧ e ∉ R) ∧
      (e ∈ D → e ∈ L) ∧ (e ∈ C → e ∈ R) ∧ (e ∈ M → e ∈ U) :=
    ⟨fun h => hU h,fun h => mem_sdiff.mp (hR h),
      fun h => let t := mem_sdiff.mp (hL h); ⟨mem_sdiff.mp t.1,t.2⟩,
      fun h => hD h,fun h => hC h,fun h => hM h⟩
  refine ⟨?_,?_,?_,?_⟩
  · ext e
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hPart e
    simp only [A,B,E,mem_union,mem_sdiff]
    constructor
    · rintro ((ha | hb) | he)
      · exact ⟨ha.1.1.1,fun h => ha.1.1.2 h.1⟩
      · rcases hb with hd | hc
        · exact ⟨(h₃ (h₄ hd)).1.1,fun h => (h₃ (h₄ hd)).1.2 h.1⟩
        · exact ⟨(h₂ (h₅ hc)).1,fun h => (h₂ (h₅ hc)).2 h.1⟩
      · rcases he with ((hr | hl) | hm)
        · exact ⟨(h₂ hr.1).1,fun h => (h₂ hr.1).2 h.1⟩
        · exact ⟨(h₃ hl.1).1.1,fun h => (h₃ hl.1).1.2 h.1⟩
        · exact ⟨h₁ (h₆ hm),fun h => h.2 hm⟩
    · rintro ⟨hg,hno⟩
      by_cases hu : e ∈ U
      · exact Or.inr (Or.inr (not_not.mp (fun hm => hno ⟨hu,hm⟩)))
      by_cases hr : e ∈ R
      · by_cases hc : e ∈ C
        · exact Or.inl (Or.inr (Or.inr hc))
        · exact Or.inr (Or.inl (Or.inl ⟨hr,hc⟩))
      by_cases hl : e ∈ L
      · by_cases hd : e ∈ D
        · exact Or.inl (Or.inr (Or.inl hd))
        · exact Or.inr (Or.inl (Or.inr ⟨hl,hd⟩))
      exact Or.inl (Or.inl ⟨⟨⟨hg,hu⟩,hr⟩,hl⟩)
  · apply disjoint_left.mpr
    intro e he he'
    obtain ⟨_,_,_,h₄,h₅,_⟩ := hPart e
    simp only [A,B,mem_union,mem_sdiff] at he he'
    exact he'.elim (fun hd => he.2 (h₄ hd)) (fun hc => he.1.2 (h₅ hc))
  · apply disjoint_left.mpr
    intro e he he'
    obtain ⟨_,_,_,_,_,h₆⟩ := hPart e
    simp only [A,E,mem_union,mem_sdiff] at he he'
    rcases he' with ((hr | hl) | hm)
    · exact he.1.2 hr.1
    · exact he.2 hl.1
    · exact he.1.1.2 (h₆ hm)
  · apply disjoint_left.mpr
    intro e he he'
    obtain ⟨_,h₂,h₃,h₄,h₅,h₆⟩ := hPart e
    simp only [B,E,mem_union,mem_sdiff] at he he'
    rcases he with hd | hc <;> rcases he' with ((hr | hl) | hm)
    · exact (h₃ (h₄ hd)).2 hr.1
    · exact hl.2 hd
    · exact (h₃ (h₄ hd)).1.2 (h₆ hm)
    · exact hr.2 hc
    · exact (h₃ hl.1).2 (h₅ hc)
    · exact (h₂ (h₅ hc)).2 (h₆ hm)

theorem coveredEdges_union (T S : Finset (Finset (V × V))) :
    coveredEdges (T ∪ S) = coveredEdges T ∪ coveredEdges S := by
  ext e
  simp only [mem_coveredEdges,mem_union]
  constructor
  · rintro ⟨A,ha | ha,he⟩
    · exact Or.inl ⟨A,ha,he⟩
    · exact Or.inr ⟨A,ha,he⟩
  · rintro (⟨A,ha,he⟩ | ⟨A,ha,he⟩)
    · exact ⟨A,Or.inl ha,he⟩
    · exact ⟨A,Or.inr ha,he⟩

theorem packing_union_of_disjoint_covered
    {T S : Finset (Finset (V × V))}
    (hT : (↑T : Set (Finset (V × V))).PairwiseDisjoint id)
    (hS : (↑S : Set (Finset (V × V))).PairwiseDisjoint id)
    (hDisj : Disjoint (coveredEdges T) (coveredEdges S)) :
    (↑(T ∪ S) : Set (Finset (V × V))).PairwiseDisjoint id := by
  intro A hA B hB hne
  rcases mem_union.mp hA with ha | ha <;> rcases mem_union.mp hB with hb | hb
  · exact hT ha hb hne
  · exact hDisj.mono (fun e he => mem_coveredEdges.mpr ⟨A,ha,he⟩)
      (fun e he => mem_coveredEdges.mpr ⟨B,hb,he⟩)
  · exact hDisj.symm.mono (fun e he => mem_coveredEdges.mpr ⟨A,ha,he⟩)
      (fun e he => mem_coveredEdges.mpr ⟨B,hb,he⟩)
  · exact hS ha hb hne

/-- Concatenate the repair packing, exterior triangles, and matching
triangles in one round. Any common certificate of the individual pieces
is preserved. -/
theorem compose_cover_down_round_packings
    (G U R L D C M : Finset (V × V))
    (hU : U ⊆ G) (hR : R ⊆ G \ U) (hL : L ⊆ (G \ U) \ R)
    (hD : D ⊆ L) (hC : C ⊆ R) (hM : M ⊆ U)
    (P : Finset (V × V) → Prop) (T₀ T₁ T₂ : Finset (Finset (V × V)))
    (hT₀ : (↑T₀ : Set (Finset (V × V))).PairwiseDisjoint id)
    (hT₁ : (↑T₁ : Set (Finset (V × V))).PairwiseDisjoint id)
    (hT₂ : (↑T₂ : Set (Finset (V × V))).PairwiseDisjoint id)
    (hCert₀ : ∀ t ∈ T₀, P t) (hCert₁ : ∀ t ∈ T₁, P t) (hCert₂ : ∀ t ∈ T₂, P t)
    (hCov₀ : coveredEdges T₀ = ((G \ U) \ R) \ L)
    (hCov₁ : coveredEdges T₁ = D ∪ C)
    (hCov₂ : coveredEdges T₂ = ((R \ C) ∪ (L \ D)) ∪ M) :
    let T := (T₀ ∪ T₁) ∪ T₂
    (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
      coveredEdges T = G \ (U \ M) ∧ ∀ t ∈ T, P t := by
  obtain ⟨hEq,h₀₁,h₀₂,h₁₂⟩ := cover_down_round_arc_partition G U R L D C M hU hR hL hD hC hM
  have hD01 : Disjoint (coveredEdges T₀) (coveredEdges T₁) := by rw [hCov₀,hCov₁]; exact h₀₁
  have hD2 : Disjoint (coveredEdges (T₀ ∪ T₁)) (coveredEdges T₂) := by
    rw [coveredEdges_union,hCov₀,hCov₁,hCov₂]
    exact disjoint_union_left.mpr ⟨h₀₂,h₁₂⟩
  intro T
  refine ⟨packing_union_of_disjoint_covered (packing_union_of_disjoint_covered hT₀ hT₁ hD01)
    hT₂ hD2,?_,?_⟩
  · change coveredEdges ((T₀ ∪ T₁) ∪ T₂) = _
    rw [coveredEdges_union,coveredEdges_union,hCov₀,hCov₁,hCov₂]
    exact hEq
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (mem_union.mp ht).elim (hCert₀ t) (hCert₁ t)
    · exact hCert₂ t ht

/-- Transport a packing through an injective vertex map. -/
theorem map_cover_down_packing {V' : Type*} (f : V' ↪ V)
    (T : Finset (Finset (V' × V')))
    (hT : (↑T : Set (Finset (V' × V'))).PairwiseDisjoint id)
    (hCert : ∀ t ∈ T, IsCoverDownTriangle t) :
    let F := f.prodMap f
    let T' := T.map (mapEmbedding F).toEmbedding
    (↑T' : Set (Finset (V × V))).PairwiseDisjoint id ∧
    (∀ t ∈ T', IsCoverDownTriangle t) ∧ coveredEdges T' = (coveredEdges T).map F := by
  intro F T'
  refine ⟨?_,?_,?_⟩
  · intro a ha b hb hne
    obtain ⟨a',ha',rfl⟩ := mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := mem_map.mp hb
    exact (disjoint_map F).mpr (hT ha' hb'
      (fun h => hne (congrArg (mapEmbedding F).toEmbedding h)))
  · intro t ht
    obtain ⟨t',ht',rfl⟩ := mem_map.mp ht
    obtain ⟨a,b,c,hab,hbc,hca,rfl⟩ := hCert t' ht'
    refine ⟨f a,f b,f c,fun h => hab (f.injective h),fun h => hbc (f.injective h),
      fun h => hca (f.injective h),?_⟩
    change (exteriorTriangle (a,b) c).map F = exteriorTriangle (f a,f b) (f c)
    simp only [exteriorTriangle,exteriorReserveArcs,map_insert,map_singleton,F,
      Function.Embedding.coe_prodMap,Prod.map_apply]
  · ext e
    constructor
    · intro he
      obtain ⟨t,ht,he⟩ := mem_coveredEdges.mp he
      obtain ⟨t',ht',rfl⟩ := mem_map.mp ht
      obtain ⟨e',he',rfl⟩ := mem_map.mp he
      exact mem_map.mpr ⟨e',mem_coveredEdges.mpr ⟨t',ht',he'⟩,rfl⟩
    · intro he
      obtain ⟨e',he',rfl⟩ := mem_map.mp he
      obtain ⟨t,ht,ht'⟩ := mem_coveredEdges.mp he'
      exact mem_coveredEdges.mpr ⟨t.map F,mem_map.mpr ⟨t,ht,rfl⟩,mem_map.mpr ⟨e',ht',rfl⟩⟩

theorem triangleHypergraph_cover_down_certificate {A B W : Type*} (T : Finset (A × B × W)) :
    ∀ t ∈ triangleHypergraph T, IsCoverDownTriangle t := by
  intro t ht
  obtain ⟨⟨a,b,w⟩,_,rfl⟩ := mem_map.mp ht
  refine ⟨.inl a,.inr (.inl b),.inr (.inr w),by simp,by simp,by simp,?_⟩
  change triangleEdges (a,b,w) = _
  ext e
  simp only [triangleEdges,exteriorTriangle,exteriorReserveArcs,mem_insert,mem_singleton]

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- Combine (4.24) with the sampled reserve to obtain the exact
transition, including (4.25), (4.26), and the matching phase. -/
theorem exists_cover_down_transition_after_cut
    {μ η : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hμ : 0 < μ) (hμsmall : 10*μ ≤ 1) (hη : 0 ≤ η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
      (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
      (R L : TripartiteArcSet A B W) (T₀ : Finset (Finset (OrientedTripartiteEdge A B W)))
      (ξ ζ : ℝ),
    let n : ℝ := nestedCoreSize ρ m i
    let U := S.vertices (i+1)
    let X := S.vertices i \ U
    let K := coverDownProtected S i
    let G := tripartiteArcs E P Q
    let GU := G ∩ (U ×ˢ U)
    let H := (G \ GU) \ R
    ρ*n ≤ N → (N:ℝ) ≤ 4*ρ*n → U.card ≤ 3*N → (X.card : ℝ) ≤ 4*n →
    120000*μ^(3/2:ℝ)*n ≤ η*μ*(ρ*n)/8 → ζ*n ≤ μ*(ρ*n)/8 →
    0 ≤ ζ*n → 2*ζ*n < μ^2*ρ*n/20 → ζ*n ≤ 10*μ*n →
    (∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+ξ*n+(3/2+η)*(ζ*n) ≤
      7*η*(μ*(ρ*n)/4)) →
    G ⊆ S.vertices i ×ˢ S.vertices i → R ⊆ G \ GU →
    (∀ e ∈ R, CrossesNestedPrefix S i e.1 e.2) →
    (∀ v, (incidentDegree R v : ℝ) ≤ 10*μ*n) →
    (∀ u ∈ X, ∀ c, c ≠ crossingPartTag u →
      μ*(ρ*n)/4 ≤ ((arcNeighborsIn (prefixPartVertices S (i+1) c) R u).card : ℝ)) →
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v →
      let c : ℝ := ((arcNeighborsIn U R u) ∩ (arcNeighborsIn U R v)).card
      c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent E P Q u v → μ^2*ρ*n/20 ≤ c)) →
    (∀ u ∈ X, ∀ x ∈ U, crossingPartTag u ≠ crossingPartTag x →
      let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
      let Y := arcNeighborsIn (prefixPartVertices S (i+1) c) R u
      (1/2+8*η)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent E P Q x)).card) →
    (∀ u ∈ X, ∀ c, let Kc := protectedCrossingPart S i c
      ((arcNeighborsIn Kc R u).card : ℝ) ≤ 3*μ*(Kc.card : ℝ)+ξ*n) →
    L ⊆ H → (∀ v, (incidentDegree L v : ℝ) ≤ ζ*n) →
    (↑T₀ : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id →
    (∀ t ∈ T₀, IsCoverDownTriangle t) →
    coveredEdges T₀ = H \ L → ArcBalanced (GU ∪ R ∪ L) →
    ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)), ∃ M : TripartiteArcSet A B W,
      (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      (∀ t ∈ T, IsCoverDownTriangle t) ∧
      coveredEdges T = G \ (GU \ M) ∧ M ⊆ GU \ (K ×ˢ K) ∧
      (∀ v, (incidentDegree M v : ℝ) ≤ 20*μ*n) ∧
      ArcBalanced (GU \ M) ∧ (GU \ M) ∩ (K ×ˢ K) = GU ∩ (K ×ˢ K) := by
  obtain ⟨N₀,hEnd⟩ := exists_concrete_round_matching_end (m := m) (k := k) (l := l)
    (A := A) (B := B) (W := W) hρ hρone hμ hμsmall hη
  refine ⟨N₀,?_⟩
  intro N hN₀ S i E P Q R L T₀ ξ ζ n U X K G GU H
    hN hNup hU hX hCost hsmall hζ hCrossCost hLoadCost hSlack hSupport hR hCross hRdeg
    hR2 hR3 hR4 hR5 hL hLDeg hPack hCert hCov hBal
  let D := L ∩ (X ×ˢ X)
  have hUG : GU ⊆ G := inter_subset_left
  have hRsub : R ⊆ G := hR.trans sdiff_subset
  have hLsub : L ⊆ G := by
    intro e he
    have h : e ∈ H := hL he
    simp only [H,mem_sdiff] at h
    exact h.1.1
  have hXU : Disjoint X U := disjoint_sdiff_self_left
  have hUR : Disjoint GU R :=
    disjoint_left.mpr fun e hu hr => (mem_sdiff.mp (hR hr)).2 hu
  have hUL : Disjoint GU L := by
    apply disjoint_left.mpr
    intro e hu hl
    have h : e ∈ H := hL hl
    simp only [H,mem_sdiff] at h
    exact h.1.2 hu
  have hRL : Disjoint R L := disjoint_left.mpr fun e hr hl => (mem_sdiff.mp (hL hl)).2 hr
  have hLNo : Disjoint L (U ×ˢ U) :=
    disjoint_left.mpr fun e hl hu => disjoint_left.mp hUL (mem_inter.mpr ⟨hLsub hl,hu⟩) hl
  obtain ⟨label,hLabel,hUsed,hDisj,hUseDeg,hBal',_,_,hInter,hLoad⟩ :=
    exists_updated_exterior_reserve U X GU R L hXU inter_subset_right hLsub hRsub
      hUR hUL hRL hBal hζ hCrossCost hLoadCost hLDeg hRdeg hR3
  let C := usedExteriorReserve D label
  let J := L \ D
  let R' := (R \ C) ∪ J
  have hJsub : J ⊆ L := sdiff_subset
  have hJdeg (v) : (incidentDegree J v : ℝ) ≤ ζ*n :=
    (by exact_mod_cast incidentDegree_mono hJsub v : (incidentDegree J v : ℝ) ≤ incidentDegree L v).trans
      (hLDeg v)
  have hR' : R' ⊆ G := union_subset (sdiff_subset.trans hRsub) (hJsub.trans hLsub)
  have hCross' : ∀ e ∈ R', CrossesNestedPrefix S i e.1 e.2 :=
    cover_down_updated_reserve_crosses S i R C L hCross (hLsub.trans hSupport) hLNo
  obtain ⟨T₂,M,hT₂,hCov₂,hM,hMDeg,hNext,hKeep,hCert₂⟩ :=
    hEnd N hN₀ S i E P Q R C J ξ ζ hN hNup hU hX hCost hsmall hSlack
      hR' hCross' hBal' hUseDeg hJdeg hR2 hR4 hR5 hInter hLoad
  let T₁ := D.image (fun e => exteriorTriangle e (label e))
  have hCov₁ : coveredEdges T₁ = D ∪ C := by
    have h := exteriorTriangle_cover_eq D label
    convert h using 1 <;> first | rfl | (ext e; simp only [T₁,D,C,mem_union,mem_inter,mem_coveredEdges,mem_image])
  have hT₁ : (↑T₁ : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id := by
    intro t ht w hw hne
    obtain ⟨e,he,rfl⟩ := mem_image.mp ht
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hw
    exact hDisj e he f hf (fun h => hne (h ▸ rfl))
  have hD : D ⊆ L := inter_subset_left
  have hCert₁ (t) (ht : t ∈ T₁) : IsCoverDownTriangle t := by
    obtain ⟨e,he,rfl⟩ := mem_image.mp ht
    have hxy := mem_product.mp (mem_inter.mp he).2
    refine ⟨e.1,e.2,label e,?_,?_,?_,rfl⟩
    · rcases e with ⟨a,b⟩
      intro heq
      change a = b at heq
      subst b
      have h := mem_tripartiteArcs.mp (hLsub (hD he))
      rcases a with a | (a | a) <;> exact h
    · intro heq
      exact disjoint_left.mp hXU hxy.2 (heq.symm ▸ hLabel e he)
    · intro heq
      exact disjoint_left.mp hXU hxy.1 (heq ▸ hLabel e he)
  have hMU : M ⊆ GU := hM.trans sdiff_subset
  have hh := compose_cover_down_round_packings G GU R L D C M hUG
    (by intro e he; have h := hR he; simpa only [mem_sdiff] using h)
    (by intro e he; have h := hL he; simpa only [H,mem_sdiff] using h)
    hD hUsed hMU IsCoverDownTriangle T₀ T₁ T₂ hPack hT₁ hT₂ hCert hCert₁ hCert₂
    (by convert hCov using 1; ext e; simp only [H,mem_sdiff])
    (by convert hCov₁ using 1; ext e; simp only [mem_union])
    (by convert hCov₂ using 1; ext e; simp only [R',J,mem_union,mem_sdiff])
  refine ⟨_,M,hh.1,hh.2.2,?_,hM,hMDeg,hNext,hKeep⟩
  convert hh.2.1 using 1 <;> first | rfl | (ext e; simp only [mem_sdiff])

end OverfullWork.ChenShan
