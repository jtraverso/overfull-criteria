module

public import OverfullWork.ChenShanCoverDownCutDegrees
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

section ArcTransport

variable {V V' : Type*}

noncomputable def pullbackArcs [Fintype V'] (f : V' ↪ V) (G : Finset (V × V)) :
    Finset (V' × V') :=
  univ.filter (fun e => f.prodMap f e ∈ G)

@[simp] theorem mem_pullbackArcs [Fintype V'] (f : V' ↪ V) (G : Finset (V × V)) (e : V' × V') :
    e ∈ pullbackArcs f G ↔ f.prodMap f e ∈ G := by
  simp only [pullbackArcs,mem_filter,mem_univ,true_and]

theorem map_pullbackArcs [Fintype V'] (f : V' ↪ V) (G : Finset (V × V))
    (hG : ∀ e ∈ G, e.1 ∈ Set.range f ∧ e.2 ∈ Set.range f) :
    (pullbackArcs f G).map (f.prodMap f) = G := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := mem_map.mp he
    exact (mem_pullbackArcs f G a).mp ha
  · intro he
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hG e he
    exact mem_map.mpr ⟨(a,b),(mem_pullbackArcs f G (a,b)).mpr (by
      change (f a,f b) ∈ G
      rwa [ha,hb,Prod.eta]),Prod.ext ha hb⟩

private theorem arc_filter_card_map (f : V' ↪ V) (G : Finset (V' × V'))
    (p : V × V → Prop) (q : V' × V' → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ e, p (f.prodMap f e) ↔ q e) :
    ((G.map (f.prodMap f)).filter p).card = (G.filter q).card := by
  rw [filter_map,card_map]
  congr 1
  ext e
  simp only [mem_filter,Function.comp_apply,h]

private theorem arc_out_card_map (f : V' ↪ V) (G : Finset (V' × V')) (v : V') :
    ((G.map (f.prodMap f)).filter (fun e => e.1 = f v)).card =
      (G.filter (fun e => e.1 = v)).card :=
  arc_filter_card_map f G _ _ fun _ => f.injective.eq_iff

private theorem arc_in_card_map (f : V' ↪ V) (G : Finset (V' × V')) (v : V') :
    ((G.map (f.prodMap f)).filter (fun e => e.2 = f v)).card =
      (G.filter (fun e => e.2 = v)).card :=
  arc_filter_card_map f G _ _ fun _ => f.injective.eq_iff

theorem arcDivergence_map (f : V' ↪ V) (G : Finset (V' × V')) (v : V') :
    arcDivergence (G.map (f.prodMap f)) (f v) = arcDivergence G v := by
  unfold arcDivergence
  rw [arc_out_card_map,arc_in_card_map]

theorem incidentDegree_map (f : V' ↪ V) (G : Finset (V' × V')) (v : V') :
    incidentDegree (G.map (f.prodMap f)) (f v) = incidentDegree G v := by
  unfold incidentDegree
  exact arc_filter_card_map f G _ _ fun _ => or_congr f.injective.eq_iff f.injective.eq_iff

theorem incidentDegree_map_outside_range (f : V' ↪ V) (G : Finset (V' × V')) (v : V)
    (hv : v ∉ Set.range f) : incidentDegree (G.map (f.prodMap f)) v = 0 := by
  unfold incidentDegree
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hh⟩ := mem_filter.mp he
  obtain ⟨a,_,rfl⟩ := mem_map.mp he
  rcases hh with h | h
  · exact hv ⟨a.1,h⟩
  · exact hv ⟨a.2,h⟩

theorem arcBalanced_map (f : V' ↪ V) (G : Finset (V' × V')) :
    ArcBalanced (G.map (f.prodMap f)) ↔ ArcBalanced G := by
  constructor
  · intro h v
    have hv := h (f v)
    rw [arc_out_card_map,arc_in_card_map] at hv
    exact hv
  · intro h v
    by_cases hv : v ∈ Set.range f
    · obtain ⟨w,rfl⟩ := hv
      rw [arc_out_card_map,arc_in_card_map]
      exact h w
    have he₁ : ((G.map (f.prodMap f)).filter (fun e => e.1 = v)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hh⟩ := mem_filter.mp he
      obtain ⟨a,_,rfl⟩ := mem_map.mp he
      exact hv ⟨a.1,hh⟩
    have he₂ : ((G.map (f.prodMap f)).filter (fun e => e.2 = v)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hh⟩ := mem_filter.mp he
      obtain ⟨a,_,rfl⟩ := mem_map.mp he
      exact hv ⟨a.2,hh⟩
    change ((G.map (f.prodMap f)).filter (fun e => e.1 = v)).card =
      ((G.map (f.prodMap f)).filter (fun e => e.2 = v)).card
    rw [he₁,he₂]

theorem pullbackArcs_mono [Fintype V'] (f : V' ↪ V) {G H : Finset (V × V)} (h : G ⊆ H) :
    pullbackArcs f G ⊆ pullbackArcs f H := by
  intro e he
  exact (mem_pullbackArcs f H e).mpr (h ((mem_pullbackArcs f G e).mp he))

noncomputable def pullbackVertices [Fintype V'] (f : V' ↪ V) (U : Finset V) : Finset V' :=
  univ.filter (fun v => f v ∈ U)

@[simp] theorem mem_pullbackVertices [Fintype V'] (f : V' ↪ V) (U : Finset V) (v : V') :
    v ∈ pullbackVertices f U ↔ f v ∈ U := by
  simp only [pullbackVertices,mem_filter,mem_univ,true_and]

theorem pullbackArcs_inter_induced [Fintype V'] (f : V' ↪ V)
    (G : Finset (V × V)) (U : Finset V) :
    pullbackArcs f (G ∩ (U ×ˢ U)) =
      pullbackArcs f G ∩ (pullbackVertices f U ×ˢ pullbackVertices f U) := by
  ext ⟨x,y⟩
  simp only [mem_pullbackArcs,mem_inter,mem_product,mem_pullbackVertices]
  rfl

theorem pullbackArcs_sdiff [Fintype V'] (f : V' ↪ V) (G R : Finset (V × V)) :
    pullbackArcs f (G \ R) = pullbackArcs f G \ pullbackArcs f R := by
  ext e
  simp only [mem_pullbackArcs,mem_sdiff]

end ArcTransport
universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The inclusion of the three current classes into the ambient vertex type. -/
def prefixVertexEmbedding (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    TripartiteVertex ↥(S.left i) ↥(S.right i) ↥(S.colors i) ↪ TripartiteVertex A B W :=
  (Function.Embedding.subtype _).sumMap
    ((Function.Embedding.subtype _).sumMap (Function.Embedding.subtype _))

theorem mem_range_prefixVertexEmbedding (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (v : TripartiteVertex A B W) :
    v ∈ Set.range (prefixVertexEmbedding S i) ↔ v ∈ S.vertices i := by
  constructor
  · rintro ⟨x,rfl⟩
    rcases x with a | (b | w)
    · exact (mem_vertices_left S i a).mpr a.property
    · exact (mem_vertices_right S i b).mpr b.property
    · exact (mem_vertices_color S i w).mpr w.property
  · intro hv
    rcases v with a | (b | w)
    · exact ⟨.inl ⟨a,(mem_vertices_left S i a).mp hv⟩,rfl⟩
    · exact ⟨.inr (.inl ⟨b,(mem_vertices_right S i b).mp hv⟩),rfl⟩
    · exact ⟨.inr (.inr ⟨w,(mem_vertices_color S i w).mp hv⟩),rfl⟩

theorem prefix_pullbackArcs_map (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (G : TripartiteArcSet A B W) (hG : G ⊆ S.vertices i ×ˢ S.vertices i) :
    let f := prefixVertexEmbedding S i
    (pullbackArcs f G).map (f.prodMap f) = G := by
  apply map_pullbackArcs
  intro e he
  obtain ⟨h₁,h₂⟩ := mem_product.mp (hG he)
  exact ⟨(mem_range_prefixVertexEmbedding S i _).mpr h₁,
    (mem_range_prefixVertexEmbedding S i _).mpr h₂⟩

theorem prefix_pullback_tripartiteArcs
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop) :
    pullbackArcs (prefixVertexEmbedding S i) (tripartiteArcs E P Q) =
      tripartiteArcs (fun a : ↥(S.left i) => fun b : ↥(S.right i) => E a b)
        (fun a w => P a (w : ↥(S.colors i))) (fun b w => Q b w) := by
  ext ⟨x,y⟩
  rw [mem_pullbackArcs,mem_tripartiteArcs,mem_tripartiteArcs]
  rcases x with a | (b | w) <;> rcases y with a' | (b' | w') <;> exact Iff.rfl

/-- Apply (4.24) to the concrete round graph. The triangle packing is
computed in the current classes, and its covered arcs map to exactly
the complement of the leave in the ambient cut remainder. -/
theorem exists_concrete_cover_down_leave
    (η ζ : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ n₀ : ℕ, ε₀ = coverDownPackingCap (η/2/2) ∧ 0 < ε₀ ∧
    ∀ (A B W : Type u) [Fintype A] [Fintype B] [Fintype W] (m k l : ℕ),
    ∀ (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ), i+1 ≤ l →
    ∀ (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
      (R : TripartiteArcSet A B W) (δ μ ξ : ℝ),
    let n := nestedCoreSize ρ m i
    let s := nestedCoreSize ρ m (i+1)
    let U := S.vertices (i+1)
    let G := tripartiteArcs E P Q
    let GU := G ∩ (U ×ˢ U)
    let H := coverDownRemainder G R U
    let ε := δ+4*ρ+10*μ
    let f := prefixVertexEmbedding S i
    n₀ ≤ n → 0 < m → 0 < ρ → ρ ≤ 1/4 → 1 ≤ ρ*(n:ℝ) →
    1/2+η ≤ (k:ℝ)/m → (k:ℝ)/m ≤ 3/2 → 1/2 ≤ η*n →
    0 ≤ ξ → 1/2 ≤ ξ*n → 0 ≤ ε → ε ≤ η/2 → ε ≤ 1/16 →
    Real.sqrt (4*ξ) ≤ min ((η/2)/32) (1/128) →
    ε+5*Real.sqrt (4*ξ) ≤ ε₀ → 5*Real.sqrt (4*ξ) ≤ ζ/2 →
    TripartiteResidualPrefixBounds E P Q S i (δ*n) →
    G ⊆ S.vertices i ×ˢ S.vertices i → R ⊆ G \ GU → ArcBalanced G →
    (∀ v, |(arcDivergence GU v : ℝ)| ≤ 2*ξ*s+1/2) →
    (∀ v, |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) →
    ∃ L : TripartiteArcSet ↥(S.left i) ↥(S.right i) ↥(S.colors i),
    ∃ T : Finset (↥(S.left i) × ↥(S.right i) × ↥(S.colors i)),
      let Lmap := L.map (f.prodMap f)
      Lmap ⊆ H ∧ (∀ v, (incidentDegree Lmap v : ℝ) ≤ ζ*n) ∧
      (↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge ↥(S.left i) ↥(S.right i) ↥(S.colors i)))).PairwiseDisjoint id ∧
      H \ Lmap = (coveredEdges (triangleHypergraph T)).map (f.prodMap f) ∧
      ArcBalanced (GU ∪ R ∪ Lmap) := by
  have hη₂ : 0 < η/2 := by positivity
  have hη₂' : η/2 < 1 := by linarith only [hηhalf]
  obtain ⟨ε₀,n₀,hCap,hε₀,hPack⟩ :=
    exists_cover_down_leave_after_reserve.{u,u,u} (η/2) ζ hη₂ hη₂' hζ
  refine ⟨ε₀,n₀,hCap,hε₀,?_⟩
  intro A B W _ _ _ m k l S i hi E P Q R δ μ ξ n s U G GU H ε f hn₀ hm hρ hρsmall hInit
    hDensity hRatio hSlack hξ hRound hε hMargin hCap hSmall hThreshold hRepair
    hBounds hGSupport hRSub hGBal hGUdeg hRdeg
  let A' := ↥(S.left i)
  let B' := ↥(S.right i)
  let W' := ↥(S.colors i)
  let E' (a : A') (b : B') := E a.val b.val
  let P' (a : A') (w : W') := P a.val w.val
  let Q' (b : B') (w : W') := Q b.val w.val
  let U' := pullbackVertices f U
  let R' := pullbackArcs f R
  let G' := tripartiteArcs E' P' Q'
  let GU' := G' ∩ (U' ×ˢ U')
  let H' := (G' \ GU') \ R'
  have hG : pullbackArcs f G = G' := prefix_pullback_tripartiteArcs S i E P Q
  have hMemG (e) : e ∈ G' ↔ f.prodMap f e ∈ G := by
    rw [← hG]
    exact mem_pullbackArcs f G e
  have hGU : pullbackArcs f GU = GU' := by
    ext ⟨v,w⟩
    simp only [GU,GU',U',mem_pullbackArcs,mem_inter,mem_product,mem_pullbackVertices,hMemG]
    rfl
  have hMemGU (e) : e ∈ GU' ↔ f.prodMap f e ∈ GU := by
    rw [← hGU]
    exact mem_pullbackArcs f GU e
  have hH : pullbackArcs f H = H' := by
    ext e
    simp only [H,H',R',coverDownRemainder,mem_pullbackArcs,mem_sdiff,hMemG,hMemGU,GU,mem_inter]
  have hGUsub : GU ⊆ G := inter_subset_left
  have hRsubG : R ⊆ G := hRSub.trans sdiff_subset
  have hHsub : H ⊆ G := by
    intro e he
    have he' := he
    simp only [H,coverDownRemainder,mem_sdiff] at he'
    exact he'.1.1
  have hMapG : G'.map (f.prodMap f) = G := by
    rw [← hG]
    exact prefix_pullbackArcs_map S i G hGSupport
  have hMapGU : GU'.map (f.prodMap f) = GU := by
    rw [← hGU]
    exact prefix_pullbackArcs_map S i GU (hGUsub.trans hGSupport)
  have hMapR : R'.map (f.prodMap f) = R :=
    prefix_pullbackArcs_map S i R (hRsubG.trans hGSupport)
  have hMapH : H'.map (f.prodMap f) = H := by
    rw [← hH]
    exact prefix_pullbackArcs_map S i H (hHsub.trans hGSupport)
  have hR' : R' ⊆ G' \ GU' := by
    intro e he
    obtain ⟨hg,hn⟩ := mem_sdiff.mp (hRSub ((mem_pullbackArcs f R e).mp he))
    exact mem_sdiff.mpr ⟨(hMemG e).mpr hg,fun h => hn ((hMemGU e).mp h)⟩
  have hG' : ArcBalanced G' := (arcBalanced_map f G').mp (hMapG ▸ hGBal)
  have hInner' (v) : |(arcDivergence GU' v : ℝ)| ≤ 2*ξ*s+1/2 := by
    rw [← arcDivergence_map f GU',hMapGU]
    exact hGUdeg (f v)
  have hRes' (v) : |(arcDivergence R' v : ℝ)| ≤ ξ*n := by
    rw [← arcDivergence_map f R',hMapR]
    exact (hRdeg (f v)).1
  have hBase (a : A') (b : B') : baseRelation H' a b ↔ baseRelation H a.val b.val := by
    rw [← hH]
    exact mem_pullbackArcs f H _
  have hLeft (a : A') (w : W') : leftColorRelation H' a w ↔ leftColorRelation H a.val w.val := by
    rw [← hH]
    exact mem_pullbackArcs f H _
  have hRight (b : B') (w : W') : rightColorRelation H' b w ↔ rightColorRelation H b.val w.val := by
    rw [← hH]
    exact mem_pullbackArcs f H _
  have filterEq {X : Type u} [Fintype X] (p q : X → Prop) [DecidablePred p] [DecidablePred q]
      (h : ∀ x, p x ↔ q x) : univ.filter p = univ.filter q := by
    ext v
    simp only [mem_filter,h]
  have ⟨hAB,hBA,hAW,hBW,hWA,hWB⟩ :=
    cover_down_cut_degrees S i hi R hm hρ hρsmall hInit hRatio hDensity hMargin hBounds
      (fun v => (hRdeg v).2)
  have hN : (1:ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hρsmall (Nat.cast_nonneg (α := ℝ) n)
    linarith only [h,hInit]
  have ⟨hA,hB,hW⟩ := cover_down_class_sizes S i (by omega) hDensity hRatio hN hSlack
  have hsn : (s:ℝ) ≤ n := by
    exact_mod_cast nestedCoreSize_monotone_down ρ (by linarith only [hρsmall]) m i
  have hLocalAB (a : A') : (1/2+η/2)*n ≤ ((univ.filter (fun b : B' => baseRelation H' a b)).card : ℝ) := by
    rw [filterEq (fun b : B' => baseRelation H' a b) (fun b => baseRelation H a.val b.val) (fun b => hBase a b)]
    convert hAB a using 1
  have hLocalBA (b : B') : (1/2+η/2)*n ≤ ((univ.filter (fun a : A' => baseRelation H' a b)).card : ℝ) := by
    rw [filterEq (fun a : A' => baseRelation H' a b) (fun a => baseRelation H a.val b.val) (fun a => hBase a b)]
    convert hBA b using 1
  have hLocalAW (a : A') : ((univ.filter (fun w : W' => ¬ leftColorRelation H' a w)).card : ℝ) ≤ ε*n := by
    rw [filterEq (fun w : W' => ¬ leftColorRelation H' a w) (fun w => ¬ leftColorRelation H a.val w.val) (fun w => not_congr (hLeft a w))]
    convert hAW a using 1
  have hLocalBW (b : B') : ((univ.filter (fun w : W' => ¬ rightColorRelation H' b w)).card : ℝ) ≤ ε*n := by
    rw [filterEq (fun w : W' => ¬ rightColorRelation H' b w) (fun w => ¬ rightColorRelation H b.val w.val) (fun w => not_congr (hRight b w))]
    convert hBW b using 1
  have hLocalWA (w : W') : ((univ.filter (fun a : A' => ¬ leftColorRelation H' a w)).card : ℝ) ≤ ε*n := by
    rw [filterEq (fun a : A' => ¬ leftColorRelation H' a w) (fun a => ¬ leftColorRelation H a.val w.val) (fun a => not_congr (hLeft a w))]
    convert hWA w using 1
  have hLocalWB (w : W') : ((univ.filter (fun b : B' => ¬ rightColorRelation H' b w)).card : ℝ) ≤ ε*n := by
    rw [filterEq (fun b : B' => ¬ rightColorRelation H' b w) (fun b => ¬ rightColorRelation H b.val w.val) (fun b => not_congr (hRight b w))]
    convert hWB w using 1
  have hh := hPack n hn₀ A' B' W' E' P' Q' U' R' ξ s ε hξ hsn hRound hε
    (by convert hR' using 1 <;> congr 6 <;> apply Subsingleton.elim) hG'
    (by intro v; convert hInner' v using 1 <;> congr 7 <;> apply Subsingleton.elim)
    hRes' hSmall hA hB hW
    (by
      intro a
      convert hLocalAB a using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (ext e; simp only [H',GU',G',mem_sdiff,mem_inter]))
    (by
      intro b
      convert hLocalBA b using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (funext a; exact propext (by
        simp only [H',GU',G',baseRelation,mem_sdiff,mem_inter]))) hCap
    (by
      intro a
      convert hLocalAW a using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (funext w; exact propext (by
        simp only [H',GU',G',leftColorRelation,mem_sdiff,mem_inter])))
    (by
      intro b
      convert hLocalBW b using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (funext w; exact propext (by
        simp only [H',GU',G',rightColorRelation,mem_sdiff,mem_inter])))
    (by
      intro w
      convert hLocalWA w using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (funext a; exact propext (by
        simp only [H',GU',G',leftColorRelation,mem_sdiff,mem_inter])))
    (by
      intro w
      convert hLocalWB w using 1
      congr 4 <;> first | rfl | apply Subsingleton.elim | (funext b; exact propext (by
        simp only [H',GU',G',rightColorRelation,mem_sdiff,mem_inter])))
    hThreshold hRepair
  obtain ⟨L,T,hL,hDegree,hDisj,hCovered,hBal⟩ := hh
  refine ⟨L,T,?_,?_,hDisj,?_,?_⟩
  · rw [← hMapH]
    exact map_subset_map.mpr (by convert hL using 1 <;>
      first | apply Subsingleton.elim | (ext e; simp only [H',GU',G',mem_sdiff,mem_inter]))
  · intro v
    by_cases hv : v ∈ Set.range f
    · obtain ⟨w,rfl⟩ := hv
      rw [incidentDegree_map]
      exact hDegree w
    · rw [incidentDegree_map_outside_range f L v hv, Nat.cast_zero]
      positivity
  · have hCov : H' \ L = coveredEdges (triangleHypergraph T) := by
      convert hCovered using 1
      ext e
      simp only [H',GU',G',mem_sdiff,mem_inter]
    have h := congrArg (fun A => A.map (f.prodMap f)) hCov
    rw [Finset.map_sdiff,hMapH] at h
    convert h using 1
  · have hBal' : ArcBalanced (GU' ∪ R' ∪ L) := by
      convert hBal using 1
      ext e
      simp only [GU',G',mem_union,mem_inter]
    have h := (arcBalanced_map f _).mpr hBal'
    rw [Finset.map_union,Finset.map_union,hMapGU,hMapR] at h
    convert h using 1

end OverfullWork.ChenShan
