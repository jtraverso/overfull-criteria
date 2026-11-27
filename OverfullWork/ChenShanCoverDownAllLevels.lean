module

public import OverfullWork.ChenShanCoverDownTransition
public import OverfullWork.ChenShanCoverDownInduction
public import OverfullWork.ChenShanNestedImbalance
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

theorem cover_down_vertices_zero (S : NestedTripartitePrefixes A B W ρ m k l) :
    S.vertices 0 = univ := by
  ext x
  rcases x with a | (b | w) <;>
    simp [mem_vertices_left,mem_vertices_right,mem_vertices_color,
      S.leftFull,S.rightFull,S.colorsFull]

theorem induced_prefix_arcDivergence_bound
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ v : TripartiteVertex ↥(S.left i) ↥(S.right i) ↥(S.colors i),
      |(arcDivergence
        (tripartiteArcs (fun a b => E a.val b.val) (fun a w => P a.val w.val)
          (fun b w => Q b.val w.val)) v : ℝ)| ≤ d) :
    ∀ v, |(arcDivergence (tripartiteArcs E P Q ∩ (S.vertices i ×ˢ S.vertices i)) v : ℝ)| ≤ d := by
  let f := prefixVertexEmbedding S i
  let G := tripartiteArcs E P Q
  let H := G ∩ (S.vertices i ×ˢ S.vertices i)
  have hSub : H ⊆ S.vertices i ×ˢ S.vertices i := inter_subset_right
  have hf (v) : f v ∈ S.vertices i :=
    (mem_range_prefixVertexEmbedding S i _).mp ⟨v,rfl⟩
  have hPull : pullbackArcs f H = pullbackArcs f G := by
    ext e
    simp only [H,mem_pullbackArcs,mem_inter,mem_product]
    exact ⟨And.left,fun h => ⟨h,hf e.1,hf e.2⟩⟩
  have hMap := prefix_pullbackArcs_map S i H hSub
  change (pullbackArcs f H).map (f.prodMap f) = H at hMap
  rw [hPull,prefix_pullback_tripartiteArcs] at hMap
  intro v
  by_cases hv : v ∈ Set.range f
  · obtain ⟨w,rfl⟩ := hv
    change |(arcDivergence H (f w) : ℝ)| ≤ d
    rw [← hMap,arcDivergence_map]
    exact h w
  · letI : DecidableEq (TripartiteVertex A B W) := Classical.decEq _
    have hOut : H.filter (fun e => e.1 = v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hr⟩ := mem_filter.mp he
      exact hv ((mem_range_prefixVertexEmbedding S i _).mpr (hr ▸ (mem_product.mp (hSub he)).1))
    have hIn : H.filter (fun e => e.2 = v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hr⟩ := mem_filter.mp he
      exact hv ((mem_range_prefixVertexEmbedding S i _).mpr (hr ▸ (mem_product.mp (hSub he)).2))
    change |(arcDivergence H v : ℝ)| ≤ d
    unfold arcDivergence
    rw [hOut,hIn]
    simpa using hd

/-- The matching theorem can use the largest of the three inner classes
as its order parameter, with no padding in the ambient graph. -/
theorem cover_down_inner_order (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (hi : i+1 ≤ l) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hRatio : (k:ℝ)/m ≤ 3/2)
    (hSize : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ)) :
    let n := nestedCoreSize ρ m i
    let s := nestedCoreSize ρ m (i+1)
    let N := max s (S.colors (i+1)).card
    s ≤ N ∧ ρ*(n:ℝ) ≤ N ∧ (N:ℝ) ≤ 4*ρ*n ∧
      (S.vertices (i+1)).card ≤ 3*N := by
  intro n s N
  obtain ⟨h₀,h₁,_⟩ := nested_crossing_core_window hρ hρsmall hSize
  have h₂ : (0:ℝ) ≤ s := by positivity
  have h₃ := mul_le_mul_of_nonneg_right hRatio h₂
  have hW := (abs_le.mp (S.crossing_color_sizes hi).1).2
  have hBound : ((S.colors (i+1)).card : ℝ) ≤ 4*ρ*n := by
    dsimp only [n,s] at h₃ ⊢
    linarith only [hW,h₁,h₃,hSize]
  have hN₀ : s ≤ N := le_max_left _ _
  have hN₁ : (S.colors (i+1)).card ≤ N := le_max_right _ _
  have hn : ρ*(n:ℝ) ≤ N := h₀.trans (by exact_mod_cast hN₀)
  have hn' : (N:ℝ) ≤ 4*ρ*n := by
    dsimp only [N]
    rw [Nat.cast_max]
    exact max_le (by linarith only [h₀,h₁,hSize]) hBound
  refine ⟨hN₀,hn,hn',?_⟩
  unfold NestedTripartitePrefixes.vertices
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  rw [card_map,card_map,card_map,S.leftSize _ hi,S.rightSize _ hi]
  omega

/-- Numerical obligations of the transition, before the graph-dependent
inputs are constructed from (4.20) and the invariant (4.22). -/
structure CoverDownLevelBounds
    (S : NestedTripartitePrefixes A B W ρ m k l) (i n₀ N₀ : ℕ)
    (η η₀ μ ζ δ ξ cap : ℝ) : Prop where
  outerThreshold : n₀ ≤ nestedCoreSize ρ m i
  innerThreshold : N₀ ≤ nestedCoreSize ρ m (i+1)
  coreLarge : 6 ≤ ρ*(nestedCoreSize ρ m i : ℝ)
  roundDelta : 1 ≤ δ*nestedCoreSize ρ m i
  roundEta : 1/2 ≤ η*nestedCoreSize ρ m i
  densityCost : 18*δ ≤ η*ρ
  probWindow : (8/η)*(16*δ/ρ) ≤ η₀/100
  discrepancy : ξ ≤ η₀*(μ*ρ)/2
  samplingThreshold : 5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 <
    (nestedCoreSize ρ m i : ℝ)
  roundXi : 1/2 ≤ ξ*nestedCoreSize ρ m i
  baseDegree : δ+4*ρ+10*μ ≤ η/2
  colorDegree : δ+4*ρ+10*μ ≤ 1/16
  repairSmall : Real.sqrt (4*ξ) ≤ min ((η/2)/32) (1/128)
  repairDensity : δ+4*ρ+10*μ+5*Real.sqrt (4*ξ) ≤ cap
  repairBudget : 5*Real.sqrt (4*ξ) ≤ ζ/2
  matchingCost : 120000*μ^(3/2:ℝ)*(nestedCoreSize ρ m i : ℝ) ≤
    η₀*μ*(ρ*nestedCoreSize ρ m i)/8
  reservePart : ζ*(nestedCoreSize ρ m i : ℝ) ≤ μ*(ρ*nestedCoreSize ρ m i)/8
  exteriorCost : 2*ζ*(nestedCoreSize ρ m i : ℝ) < μ^2*ρ*nestedCoreSize ρ m i/20
  loadCost : ζ*(nestedCoreSize ρ m i : ℝ) ≤ 10*μ*nestedCoreSize ρ m i
  protection : ∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+
    ξ*nestedCoreSize ρ m i+(3/2+η₀)*(ζ*nestedCoreSize ρ m i) ≤
    7*η₀*(μ*(ρ*nestedCoreSize ρ m i)/4)

set_option maxHeartbeats 1000000 in
/-- Given the numerical inequalities of the article, run the concrete
transition at every level. The inputs at each round are recovered from
the original graph and (4.22), rather than supplied as graph hypotheses. -/
theorem exists_all_levels_cover_down_packing
    {η η₀ μ ζ ξ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hη₀ : 0 < η₀) (hη₀small : η₀ ≤ 1/80) (hEta : 40*η₀ ≤ η) (hηhalf : η ≤ 1/2)
    (hμ : 0 < μ) (hμsmall : 10*μ ≤ 1) (hζ : 0 < ζ) (hξ : 0 < ξ) :
    ∃ cap : ℝ, ∃ n₀ N₀ : ℕ, cap = coverDownPackingCap (η/2/2) ∧ 0 < cap ∧
    ∀ (A B W : Type u) [Fintype A] [Fintype B] [Fintype W] (m k l : ℕ),
    ∀ (S : NestedTripartitePrefixes A B W ρ m k l)
      (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop) (ε : ℝ)
      (Abs : TripartiteArcSet A B W),
    let G := tripartiteArcs E P Q
    let δ := 4*ε+10*ξ+20*μ/ρ
    0 < m → 0 < k → Fintype.card W = k → 0 ≤ ε →
    DenseTripartite E P Q m η ε → 1/2+η ≤ (k:ℝ)/m → (k:ℝ)/m ≤ 3/2 →
    TripartitePrefixDegreeControl E P Q S ξ →
    (∀ i < l, CoverDownLevelBounds S i n₀ N₀ η η₀ μ ζ δ ξ cap) →
    Abs ⊆ G → Disjoint Abs (S.vertices 1 ×ˢ S.vertices 1) → ArcBalanced Abs →
    (∀ v, (incidentDegree Abs v : ℝ) ≤ μ*m) →
    ∃ L : TripartiteArcSet A B W, ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)),
      L ⊆ G \ Abs ∧ L ⊆ G ∩ (S.vertices l ×ˢ S.vertices l) ∧ ArcBalanced L ∧
      (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = (G \ Abs) \ L := by
  obtain ⟨cap,n₀,N₀,hPackingCap,hCap,hRound⟩ := exists_cover_down_transition.{u}
    hρ hρsmall hη₀ hη₀small hEta hηhalf hμ hμsmall hζ
  refine ⟨cap,n₀,N₀,hPackingCap,hCap,?_⟩
  intro A B W _ _ _ m k l S E P Q ε Abs G δ hm hk hW hε hDense hLower hUpper hSample hLevels hAbs hAbsDisj hAbsBal hAbsDeg
  let β : ℝ := 20*μ/ρ
  let initial := G \ Abs
  let Inv (i : ℕ) (H : TripartiteArcSet A B W) : Prop :=
    H ⊆ G ∩ (S.vertices i ×ˢ S.vertices i) ∧ ArcBalanced H ∧
    (i < l → H ∩ (S.vertices (i+1) ×ˢ S.vertices (i+1)) =
      G ∩ (S.vertices (i+1) ×ˢ S.vertices (i+1))) ∧
    (∀ v, (incidentDegree (prefixLostArcs G H (S.vertices i)) v : ℝ) ≤ β*nestedCoreSize ρ m i)
  have hInit : Inv 0 initial := by
    have hGbal := arcBalanced_of_tripartiteLocallyBalanced hDense.balanced
    obtain ⟨hBal,hInside,_⟩ := absorber_sdiff_initial_state G Abs (S.vertices 1) (μ*m)
      hGbal hAbsBal hAbs (by convert hAbsDisj using 1) hAbsDeg
    have hG0 : G ∩ (S.vertices 0 ×ˢ S.vertices 0) = G := by
      rw [cover_down_vertices_zero]
      ext e
      simp only [mem_inter,mem_product,mem_univ,and_true]
    have hb : μ ≤ β := by
      apply (le_div_iff₀ hρ).mpr
      have h := mul_le_mul_of_nonneg_left hρsmall hμ.le
      linarith only [h,hμ]
    refine ⟨?_,?_,?_,?_⟩
    · rw [hG0]
      exact sdiff_subset
    · convert hBal using 1
      ext e
      simp only [initial,mem_sdiff]
    · intro _
      convert hInside using 1 <;> ext e <;> simp only [initial,mem_inter,mem_sdiff,mem_product]
    · intro v
      have hEq : prefixLostArcs G initial (S.vertices 0) = Abs := by
        ext e
        simp only [prefixLostArcs,initial,cover_down_vertices_zero,mem_sdiff,
          mem_inter,mem_product,mem_univ,and_true]
        constructor
        · rintro ⟨he,hn⟩
          exact not_not.mp (fun ha => hn ⟨he,ha⟩)
        · intro ha
          exact ⟨hAbs ha,fun hn => hn.2 ha⟩
      rw [hEq]
      exact (hAbsDeg v).trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))
  have hStep : ∀ i < l, ∀ H, Inv i H →
      ∃ H' : TripartiteArcSet A B W, ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)),
        H' ⊆ H ∧ Inv (i+1) H' ∧ (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
        (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = H \ H' := by
    intro i hi H hInv
    obtain ⟨hH,hBal,hFull,hLoss⟩ := hInv
    let U := S.vertices (i+1)
    let K := coverDownProtected S i
    let GU := H ∩ (U ×ˢ U)
    let N := max (nestedCoreSize ρ m (i+1)) (S.colors (i+1)).card
    have hBound := hLevels i hi
    have hi' : i+1 ≤ l := by omega
    have hH₀ : H ⊆ G := hH.trans inter_subset_left
    have hEq := tripartiteArcs_recover_subgraph hH₀
    have hResidual := tripartite_residual_prefix_degrees (β := β)
      hDense S hm hk hW (by linarith only [hρsmall]) hε hξ.le hSample i (by omega)
      hBound.roundXi (by rw [hEq]; exact hH₀) (by intro v; rw [hEq]; exact hLoss v)
    have hInterior : ∀ v, |(arcDivergence GU v : ℝ)| ≤ 2*ξ*nestedCoreSize ρ m (i+1)+1/2 := by
      change ∀ v, |(arcDivergence (H ∩ (U ×ˢ U)) v : ℝ)| ≤ _
      rw [hFull hi]
      apply induced_prefix_arcDivergence_bound S (i+1) E P Q
      · positivity
      · exact nested_prefix_imbalance E P Q S ξ hm hk hDense.sizeA hDense.sizeB hW
          hDense.balanced hSample _ hi'
    have ⟨hNN,hNlo,hNhi,hU⟩ :=
      cover_down_inner_order S i hi' hρ hρsmall hUpper (by linarith only [hBound.coreLarge])
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hK' := (div_le_iff₀ hmR).mp hUpper
    have hni : 1 ≤ nestedCoreSize ρ m i := by
      have hh := mul_le_mul_of_nonneg_right hρsmall (Nat.cast_nonneg (α := ℝ) (nestedCoreSize ρ m i))
      exact_mod_cast (show (1:ℝ) ≤ nestedCoreSize ρ m i by linarith only [hh,hBound.coreLarge])
    have hX : (((S.vertices i) \ U).card : ℝ) ≤ 4*nestedCoreSize ρ m i := by
      exact_mod_cast (card_le_card (sdiff_subset : (S.vertices i \ U) ⊆ S.vertices i)).trans
        (S.vertices_card_le hm hK' i (by omega) hni)
    have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
    have hh := hRound A B W m k l S i N hi' (baseRelation H) (leftColorRelation H) (rightColorRelation H) δ ξ
      hBound.outerThreshold (hBound.innerThreshold.trans hNN) hm hδ hξ hBound.coreLarge hBound.roundDelta
      hLower hUpper hBound.roundEta hBound.densityCost hBound.probWindow hBound.discrepancy
      hBound.samplingThreshold hBound.roundXi hBound.baseDegree hBound.colorDegree hBound.repairSmall
      hBound.repairDensity hBound.repairBudget hNlo hNhi hU hX hBound.matchingCost hBound.reservePart
      hBound.exteriorCost hBound.loadCost hBound.protection hResidual
      (by rw [hEq]; exact hH.trans inter_subset_right) (by rw [hEq]; exact hBal)
      (by rw [hEq]; exact hInterior)
    rw [hEq] at hh
    obtain ⟨T,M,hT,hCert,hCov,hM,hMDeg,hNext,_⟩ := hh
    have hout := cover_down_transition_degree_invariant G H M U K
      (coverDownProtected_subset S i) (by
        convert hFull hi using 1 <;> ext e <;> simp only [U,mem_inter,mem_product])
      (by intro e he; have hh := hM he; simpa only [mem_sdiff,mem_inter,mem_product] using hh)
      (20*μ*nestedCoreSize ρ m i) hMDeg
    obtain ⟨hSub,hSub',hKeep,hDegree⟩ := hout
    refine ⟨GU \ M,T,?_,⟨?_,?_,?_,?_⟩,hT,hCert,?_⟩
    · intro e he
      exact hSub (by simpa only [GU,mem_sdiff,mem_inter] using he)
    · intro e he
      have h := hSub' (by simpa only [GU,mem_sdiff,mem_inter] using he)
      simpa only [U,mem_inter,mem_product] using h
    · convert hNext using 1 <;> first | rfl | (ext e; simp only [GU,U,mem_sdiff,mem_inter,mem_product])
    · intro hi₂
      have hK : K = S.vertices (i+1+1) := by
        change coverDownProtected S i = S.vertices (i+1+1)
        rw [coverDownProtected,ite_eq_left (by omega : i+2 ≤ l)]
      have h := hKeep
      rw [hK] at h
      convert h using 1 <;> first | rfl |
        (ext e; simp only [GU,U,mem_inter,mem_sdiff,mem_product])
    · intro v
      have h := hDegree v
      have hScale : 20*μ*(nestedCoreSize ρ m i : ℝ) ≤ β*nestedCoreSize ρ m (i+1) := by
        dsimp only [β]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hρ).mpr
        have hn := mul_le_mul_of_nonneg_left (nestedCoreSize_step_lower ρ m i)
          (show 0 ≤ 20*μ by positivity)
        linarith only [hn]
      apply le_trans _ hScale
      convert h using 1 <;> congr 2 <;>
        first | rfl | (ext e; simp only [prefixLostArcs,GU,U,mem_inter,mem_sdiff,mem_product])
    · convert hCov using 1 <;> first | rfl |
        (ext e; simp only [GU,U,mem_inter,mem_sdiff,mem_product])
  obtain ⟨L,T,hL,hInv,hT,hCert,hCov⟩ := iterate_cover_down_triangles initial l Inv hInit (by
    intro i hi H hI
    obtain ⟨H',T,hsub,hI',ht,hcert,hcov⟩ := hStep i hi H hI
    refine ⟨H',T,hsub,hI',ht,hcert,?_⟩
    convert hcov using 1
    ext e
    simp only [mem_sdiff])
  exact ⟨L,T,hL,hInv.1,hInv.2.1,hT,hCert,by
    convert hCov using 1; ext e; simp only [initial,mem_sdiff]⟩

/-- Use the absorber of Step 1 on the balanced terminal leave and
recover an exact decomposition of the original arc graph. -/
theorem finish_all_levels_with_absorber
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (EA : A → B → Prop) (PA : A → W → Prop) (QA : B → W → Prop)
    (Z : Finset (TripartiteVertex A B W))
    (hAbs : tripartiteArcs EA PA QA ⊆ tripartiteArcs E P Q)
    (hAbsorb : ∀ (EL : A → B → Prop) (PL : A → W → Prop) (QL : B → W → Prop),
      tripartiteArcs EL PL QL ⊆ tripartiteArcs E P Q →
      tripartiteArcs EL PL QL ⊆ Z ×ˢ Z →
      TripartiteLocallyBalanced EL PL QL →
      Nonempty (TripartiteTriangleDecomposition
        (fun a b => EA a b ∨ EL a b) (fun a w => PA a w ∨ PL a w) (fun b w => QA b w ∨ QL b w)))
    (L : TripartiteArcSet A B W) (T : Finset (Finset (OrientedTripartiteEdge A B W)))
    (hL : L ⊆ tripartiteArcs E P Q \ tripartiteArcs EA PA QA)
    (hInside : L ⊆ Z ×ˢ Z) (hBalance : ArcBalanced L)
    (hT : (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id)
    (hCert : ∀ t ∈ T, IsCoverDownTriangle t)
    (hCov : coveredEdges T = (tripartiteArcs E P Q \ tripartiteArcs EA PA QA) \ L) :
    ∃ S : Finset (Finset (OrientedTripartiteEdge A B W)),
      (↑S : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      (∀ t ∈ S, IsCoverDownTriangle t) ∧ coveredEdges S = tripartiteArcs E P Q := by
  let G := tripartiteArcs E P Q
  let Abs := tripartiteArcs EA PA QA
  let initial := G \ Abs
  have hEq := tripartiteArcs_recover_subgraph (show L ⊆ G from hL.trans sdiff_subset)
  obtain ⟨D⟩ := hAbsorb (baseRelation L) (leftColorRelation L) (rightColorRelation L)
    (by rw [hEq]; exact hL.trans sdiff_subset) (by rw [hEq]; exact hInside)
    (tripartiteLocallyBalanced_of_arcBalanced (by rw [hEq]; exact hBalance))
  obtain ⟨S,hS,hCertS,hCovS⟩ := cover_down_packing_of_decomposition D
  have hUnion : coveredEdges S = Abs ∪ L := by
    rw [hCovS,← hEq]
    ext ⟨x,y⟩
    simp only [Abs,mem_union,mem_tripartiteArcs]
    rcases x with a | (b | w) <;> rcases y with a' | (b' | w') <;> simp [tripartiteArc]
  have hSep : Disjoint Abs initial := by
    apply disjoint_left.mpr
    intro e he he'
    exact (mem_sdiff.mp he').2 he
  have hAll : initial ∪ Abs = G := by
    ext e
    simp only [initial,mem_union,mem_sdiff]
    constructor
    · exact fun h => h.elim And.left (fun h => hAbs h)
    · intro he
      by_cases h : e ∈ Abs
      · exact Or.inr h
      · exact Or.inl ⟨he,h⟩
  obtain ⟨hPair,hCertAll,hFinish⟩ := finish_cover_down_directed_absorption initial Abs L
    hSep hL T S hT hS hCert hCertS
    (by convert hCov using 1; ext e; simp only [initial,G,Abs,mem_sdiff])
    (by convert hUnion using 1; ext e; simp only [mem_union])
  refine ⟨_,hPair,hCertAll,hFinish.trans ?_⟩
  convert hAll using 1
  ext e
  simp only [mem_union]

end OverfullWork.ChenShan
