module

public import OverfullWork.ChenShanCoverDownInnerMatchings
import OverfullWork.ChenShanAbsorberCatalogue
import OverfullWork.DenseHall
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

noncomputable def coverDownProtected (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    Finset (TripartiteVertex A B W) :=
  if i+2 ≤ l then S.vertices (i+2) else ∅

theorem coverDownProtected_subset (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    coverDownProtected S i ⊆ S.vertices (i+1) := by
  unfold coverDownProtected
  split
  · exact S.vertices_antitone (by omega)
  · exact empty_subset _

theorem mem_protectedCrossingPart_iff
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (c : Fin 3)
    {v : TripartiteVertex A B W} (hv : crossingPartTag v = c) :
    v ∈ protectedCrossingPart S i c ↔ v ∈ coverDownProtected S i := by
  by_cases hi : i+2 ≤ l
  · simp only [coverDownProtected,protectedCrossingPart,ite_eq_left hi,prefixPartVertices,mem_filter,hv,and_true]
  · simp only [coverDownProtected,protectedCrossingPart,ite_eq_right hi]

/-- Apply (4.26) in the third class, protecting the entire next prefix
at the source and the corresponding class of that prefix at the target. -/
theorem cover_down_concrete_protected_degree
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (R C J : TripartiteArcSet A B W)
    (v x : TripartiteVertex A B W) (hne : crossingPartTag v ≠ crossingPartTag x)
    {μ ξ ζ η n : ℝ} (hη : 0 ≤ η)
    (hSize : ∀ c, c ≠ crossingPartTag v →
      μ*(ρ*n)/4 ≤ ((arcNeighborsIn (prefixPartVertices S (i+1) c) R v).card : ℝ))
    (hOld : let c := remainingCrossingPart (crossingPartTag v) (crossingPartTag x)
      let Y := arcNeighborsIn (prefixPartVertices S (i+1) c) R v
      (1/2+8*η)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent E P Q x)).card)
    (hR5 : ∀ c, let K := protectedCrossingPart S i c
      ((arcNeighborsIn K R v).card : ℝ) ≤ 3*μ*(K.card : ℝ)+ξ*n)
    (hC : (incidentDegree C v : ℝ) ≤ ζ*n) (hJ : (incidentDegree J v : ℝ) ≤ ζ*n)
    (hSlack : ∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+ξ*n+(3/2+η)*(ζ*n) ≤
      7*η*(μ*(ρ*n)/4)) :
    let c := remainingCrossingPart (crossingPartTag v) (crossingPartTag x)
    let Y := arcNeighborsIn (prefixPartVertices S (i+1) c) ((R \ C) ∪ J) v
    let K := coverDownProtected S i
    (1/2+η)*(Y.card : ℝ) ≤
      (Y.filter (fun z => tripartiteAdjacent E P Q x z ∧ (x ∉ K ∨ z ∉ K))).card := by
  intro c Y K
  have h := cover_down_modified_protected_part (prefixPartVertices S (i+1) c)
    (protectedCrossingPart S i c) (protectedCrossingPart_subset S i c) R C J v
    (x ∉ K) (tripartiteAdjacent E P Q x) hη
    (hSize c (remainingCrossingPart_ne_left hne)) hOld (hR5 c) hC hJ (hSlack c)
  have hh : (1/2+η)*(Y.card : ℝ) ≤
      (Y.filter (fun z => tripartiteAdjacent E P Q x z ∧
        (x ∉ K ∨ z ∉ protectedCrossingPart S i c))).card := by
    convert h using 1 <;> congr 3 <;> ext z <;>
      simp only [Y,mem_filter,mem_arcNeighborsIn,mem_union,mem_sdiff]
  refine hh.trans_eq ?_
  congr 2
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨hz,ha,hk⟩
    have htag := (mem_filter.mp ((mem_arcNeighborsIn _ _ _ _).mp hz).1).2
    exact ⟨hz,ha,hk.imp_right (fun hn hv => hn ((mem_protectedCrossingPart_iff S i c htag).mpr hv))⟩
  · rintro ⟨hz,ha,hk⟩
    have htag := (mem_filter.mp ((mem_arcNeighborsIn _ _ _ _).mp hz).1).2
    exact ⟨hz,ha,hk.imp_right (fun hn hv => hn ((mem_protectedCrossingPart_iff S i c htag).mp hv))⟩

private theorem cover_down_protected_arc_iff
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (U K : Finset (TripartiteVertex A B W))
    {a b : TripartiteVertex A B W} (ha : a ∈ U) (hb : b ∈ U)
    (htag : crossingPartTag b = crossingPartTag a+1) :
    (a,b) ∈ (tripartiteArcs E P Q ∩ (U ×ˢ U)) \ (K ×ˢ K) ↔
      tripartiteAdjacent E P Q a b ∧ (a ∉ K ∨ b ∉ K) := by
  have hReverse (h : tripartiteArc E P Q b a) : False := by
    have he := crossingPartTag_eq_succ_of_arc h
    rw [htag] at he
    exact (show ∀ c : Fin 3, c ≠ c+1+1 by decide) _ he
  simp only [mem_sdiff,mem_inter,mem_product,mem_tripartiteArcs,ha,hb,and_true,
    tripartiteAdjacent]
  tauto

/-- The two directed matching shores satisfy the minimum degree of
(4.26) in the protected interior graph. -/
theorem cover_down_concrete_matching_degrees
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (R C J : TripartiteArcSet A B W)
    (v : TripartiteVertex A B W) (hv : v ∉ S.vertices (i+1))
    {μ ξ ζ η n : ℝ} (hη : 0 ≤ η)
    (hSize : ∀ c, c ≠ crossingPartTag v →
      μ*(ρ*n)/4 ≤ ((arcNeighborsIn (prefixPartVertices S (i+1) c) R v).card : ℝ))
    (hOld : ∀ x ∈ S.vertices (i+1), crossingPartTag v ≠ crossingPartTag x →
      let c := remainingCrossingPart (crossingPartTag v) (crossingPartTag x)
      let Y := arcNeighborsIn (prefixPartVertices S (i+1) c) R v
      (1/2+8*η)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent E P Q x)).card)
    (hR5 : ∀ c, let K := protectedCrossingPart S i c
      ((arcNeighborsIn K R v).card : ℝ) ≤ 3*μ*(K.card : ℝ)+ξ*n)
    (hC : (incidentDegree C v : ℝ) ≤ ζ*n) (hJ : (incidentDegree J v : ℝ) ≤ ζ*n)
    (hSlack : ∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+ξ*n+(3/2+η)*(ζ*n) ≤
      7*η*(μ*(ρ*n)/4))
    (hArc : (R \ C) ∪ J ⊆ tripartiteArcs E P Q)
    (hCross : ∀ e ∈ (R \ C) ∪ J, CrossesNestedPrefix S i e.1 e.2) :
    let U := S.vertices (i+1)
    let K := coverDownProtected S i
    let H := (tripartiteArcs E P Q ∩ (U ×ˢ U)) \ (K ×ˢ K)
    let F := arcOutNeighbors ((R \ C) ∪ J) v
    let G := arcInNeighbors ((R \ C) ∪ J) v
    (∀ x ∈ F, (1/2+η)*(G.card : ℝ) ≤ (G.filter (fun z => (x,z) ∈ H)).card) ∧
    (∀ x ∈ G, (1/2+η)*(F.card : ℝ) ≤ (F.filter (fun z => (z,x) ∈ H)).card) := by
  intro U K H F G
  have ⟨hF,hG⟩ := cover_down_exterior_neighbor_shores S i ((R \ C) ∪ J) hArc hCross v hv
  have hF' : F = _ := hF
  have hG' : G = _ := hG
  have hNext (c : Fin 3) : c ≠ c+1 := by fin_cases c <;> decide
  have hPrev (c : Fin 3) : c ≠ c+2 := by fin_cases c <;> decide
  have hDiff (c : Fin 3) : c+1 ≠ c+2 := by fin_cases c <;> decide
  have hCycle (c : Fin 3) : c+1+1 = c+2 := by fin_cases c <;> decide
  have hGet (x : TripartiteVertex A B W) (c : Fin 3)
      (h : x ∈ arcNeighborsIn (prefixPartVertices S (i+1) c) ((R \ C) ∪ J) v) :
      x ∈ U ∧ crossingPartTag x = c :=
    mem_filter.mp ((mem_arcNeighborsIn _ _ _ _).mp h).1
  constructor
  · intro x hx
    have hx' := hGet x _ (hF' ▸ hx)
    have hNe : crossingPartTag v ≠ crossingPartTag x := by rw [hx'.2]; exact hNext _
    have hc : remainingCrossingPart (crossingPartTag v) (crossingPartTag x) =
        crossingPartTag v+2 := by
      apply remainingCrossingPart_unique hNe (hPrev _)
      rw [hx'.2]
      exact hDiff _
    have hh := cover_down_concrete_protected_degree S i R C J v x hNe hη hSize
      (hOld x hx'.1 hNe) hR5 hC hJ hSlack
    dsimp only at hh
    rw [hc,← hG'] at hh
    refine hh.trans_eq ?_
    congr 2
    ext z
    simp only [mem_filter]
    apply and_congr_right
    intro hz
    have hz' := hGet z _ (hG' ▸ hz)
    exact (cover_down_protected_arc_iff U K hx'.1 hz'.1
      (by rw [hx'.2,hz'.2,hCycle])).symm
  · intro x hx
    have hx' := hGet x _ (hG' ▸ hx)
    have hNe : crossingPartTag v ≠ crossingPartTag x := by rw [hx'.2]; exact hPrev _
    have hc : remainingCrossingPart (crossingPartTag v) (crossingPartTag x) =
        crossingPartTag v+1 := by
      apply remainingCrossingPart_unique hNe (hNext _)
      rw [hx'.2]
      exact (hDiff _).symm
    have hh := cover_down_concrete_protected_degree S i R C J v x hNe hη hSize
      (hOld x hx'.1 hNe) hR5 hC hJ hSlack
    dsimp only at hh
    rw [hc,← hF'] at hh
    refine hh.trans_eq ?_
    congr 2
    ext z
    simp only [mem_filter]
    apply and_congr_right
    intro hz
    have hz' := hGet z _ (hF' ▸ hz)
    rw [cover_down_protected_arc_iff U K hz'.1 hx'.1 (by rw [hx'.2,hz'.2,hCycle])]
    unfold tripartiteAdjacent
    tauto

/-- Lift the neighborhood bounds to an actual end-of-round packing on
the current prefix. The bounds on the two matching shores follow from
(R2), (R4), (R5), and the degree budget for the exterior leave. -/
theorem exists_concrete_round_matching_end
    {μ η : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hμ : 0 < μ)
    (hμsmall : 10*μ ≤ 1) (hη : 0 ≤ η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
      (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
      (R C J : TripartiteArcSet A B W) (ξ ζ : ℝ),
    let n : ℝ := nestedCoreSize ρ m i
    let U := S.vertices (i+1)
    let X := S.vertices i \ U
    let K := coverDownProtected S i
    let GU := tripartiteArcs E P Q ∩ (U ×ˢ U)
    let R' := (R \ C) ∪ J
    ρ*n ≤ N → (N:ℝ) ≤ 4*ρ*n → U.card ≤ 3*N → (X.card : ℝ) ≤ 4*n →
    120000*μ^(3/2:ℝ)*n ≤ η*μ*(ρ*n)/8 → ζ*n ≤ μ*(ρ*n)/8 →
    (∀ c, 3*μ*((protectedCrossingPart S i c).card : ℝ)+ξ*n+(3/2+η)*(ζ*n) ≤
      7*η*(μ*(ρ*n)/4)) →
    R' ⊆ tripartiteArcs E P Q →
    (∀ e ∈ R', CrossesNestedPrefix S i e.1 e.2) → ArcBalanced (GU ∪ R') →
    (∀ v ∈ X, (incidentDegree C v : ℝ) ≤ ζ*n) →
    (∀ v, (incidentDegree J v : ℝ) ≤ ζ*n) →
    (∀ u ∈ X, ∀ c, c ≠ crossingPartTag u →
      μ*(ρ*n)/4 ≤ ((arcNeighborsIn (prefixPartVertices S (i+1) c) R u).card : ℝ)) →
    (∀ u ∈ X, ∀ x ∈ U, crossingPartTag u ≠ crossingPartTag x →
      let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
      let Y := arcNeighborsIn (prefixPartVertices S (i+1) c) R u
      (1/2+8*η)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent E P Q x)).card) →
    (∀ u ∈ X, ∀ c, let Kc := protectedCrossingPart S i c
      ((arcNeighborsIn Kc R u).card : ℝ) ≤ 3*μ*(Kc.card : ℝ)+ξ*n) →
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v →
      (((arcNeighborsIn U R' u) ∩ (arcNeighborsIn U R' v)).card : ℝ) ≤ 100*μ^2*ρ*n) →
    (∀ v, ((arcNeighborsIn X R' v).card : ℝ) ≤ 20*μ*n) →
    ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)), ∃ M : TripartiteArcSet A B W,
      (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      coveredEdges T = R' ∪ M ∧ M ⊆ GU \ (K ×ˢ K) ∧
      (∀ v, (incidentDegree M v : ℝ) ≤ 20*μ*n) ∧
      ArcBalanced (GU \ M) ∧ (GU \ M) ∩ (K ×ˢ K) = GU ∩ (K ×ˢ K) := by
  let b : ℕ := ⌈10/ρ⌉₊
  have hb : 0 < b := by
    have h : (10:ℝ)/ρ ≤ b := Nat.le_ceil _
    have hb' : (0:ℝ) < b := (by positivity : (0:ℝ) < 10/ρ).trans_le h
    exact_mod_cast hb'
  obtain ⟨N₀,hPack⟩ := exists_cover_down_round_end.{u} b hb (10*μ) η (by positivity) hμsmall
  refine ⟨N₀,?_⟩
  intro N hN₀ S i E P Q R C J ξ ζ n U X K GU R'
    hN hNup hU hX hMargin hSmall hSlack hArc hCross hBal hC hJ hSize hOld hR5 hOverlap hLoad
  let F (v : ↥X) := arcOutNeighbors R' v.val
  let G (v : ↥X) := arcInNeighbors R' v.val
  have hn : 0 ≤ n := by positivity
  obtain ⟨hCount,hCountOverlap,hCountLoad,hCost⟩ :=
    cover_down_matching_budgets hρ hρone hμ.le hn hN hNup hMargin
  have hX' : X.card ≤ 3*b*N := by
    exact_mod_cast hX.trans hCount
  have hXU : Disjoint X U := disjoint_sdiff_self_left
  have hUout (v : ↥X) : v.val ∉ U := (mem_sdiff.mp v.property).2
  have hPartition (v : ↥X) : F v ∪ G v = arcNeighborsIn U R' v.val := by
    have hh := (cover_down_exterior_neighbor_partition S i GU R' hArc hCross
      inter_subset_right hBal v.val (hUout v)).1
    exact hh
  have hMin (v : ↥X) : μ*(ρ*n)/8 ≤ ((F v).card : ℝ) := by
    have hh := cover_down_modified_part_lower (prefixPartVertices S (i+1) (crossingPartTag v.val+1))
      R C J v.val (hSize v.val v.property _ (by
        exact (show ∀ c : Fin 3, c+1 ≠ c by decide) _)) (hC v.val v.property) hSmall
    have hF := (cover_down_exterior_neighbor_shores S i R' hArc hCross v.val (hUout v)).1
    change F v = _ at hF
    rw [hF]
    convert hh using 1
    congr 2
    ext z
    simp only [R',mem_arcNeighborsIn,mem_union,mem_sdiff]
  have hDegrees (v : ↥X) := cover_down_concrete_matching_degrees S i R C J v.val
    (hUout v) hη (hSize v.val v.property) (hOld v.val v.property) (hR5 v.val v.property)
    (hC v.val v.property) (hJ v.val) hSlack hArc hCross
  have hOverlap' (v w : ↥X) (hne : v ≠ w) :
      (((F v ∪ G v) ∩ (F w ∪ G w)).card : ℝ) ≤ 6*(10*μ)^2*N := by
    rw [hPartition,hPartition]
    exact (hOverlap v.val v.property w.val w.property (fun h => hne (Subtype.ext h))).trans
      hCountOverlap
  have hLoad' (v : TripartiteVertex A B W) :
      ((univ.filter (fun j : ↥X => v ∈ F j ∪ G j)).card : ℝ) ≤ 20*μ*n := by
    have he : univ.filter (fun j : ↥X => v ∈ F j ∪ G j) =
        univ.filter (fun j : ↥X => (v,j.val) ∈ R' ∨ (j.val,v) ∈ R') := by
      ext j
      rw [mem_filter,mem_filter,hPartition,mem_arcNeighborsIn]
      exact and_congr_right fun _ => ⟨fun h => h.2.symm,fun h => ⟨by
        rcases h with h | h
        · exact ((hCross (v,j.val) h).resolve_right (fun h => hUout j h.2)).1
        · exact ((hCross (j.val,v) h).resolve_left (fun h => hUout j h.1)).2,h.symm⟩⟩
    rw [he]
    have hc := DenseHall.subtype_filter_card X (fun j => (v,j) ∈ R' ∨ (j,v) ∈ R')
    have hh : ((univ.filter (fun j : ↥X => (v,j.val) ∈ R' ∨ (j.val,v) ∈ R')).card : ℝ) =
        (arcNeighborsIn X R' v).card := by
      have h := congrArg (fun a : ℕ => (a:ℝ)) hc
      convert h using 1 <;> congr 4
      ext z
      simp only [mem_arcNeighborsIn,mem_filter]
    rw [hh]
    exact hLoad v
  have hAsym (a c) (he : (a,c) ∈ R') (he' : (c,a) ∈ R') : False := by
    have ha := mem_tripartiteArcs.mp (hArc he)
    have hc := mem_tripartiteArcs.mp (hArc he')
    rcases a with a | (a | a) <;> rcases c with c | (c | c) <;>
      first | exact ha | exact hc
  have h := hPack N hN₀ (TripartiteVertex A B W) U X K GU R' (20*μ*n)
    hU hX' (coverDownProtected_subset S i) hXU inter_subset_right
    (fun e he => (hCross e he).symm) hAsym
    (by convert hBal using 1; ext e; simp only [mem_union])
    (by
      intro v
      have hv := mul_le_mul_of_nonneg_left (hMin v) hη
      linarith only [hCost,hv])
    (by
      intro v a ha
      have hv := (hDegrees v).1 a ha
      convert hv using 1
      congr 2
      ext z
      simp only [GU,K,U,R',mem_filter,mem_arcInNeighbors,mem_sdiff,mem_inter,mem_union,mem_product])
    (by
      intro v a ha
      have hv := (hDegrees v).2 a ha
      convert hv using 1
      congr 2
      ext z
      simp only [GU,K,U,R',mem_filter,mem_arcOutNeighbors,mem_sdiff,mem_inter,mem_union,mem_product])
    (by
      intro v w hne
      have hv := hOverlap' v w hne
      convert hv using 1
      congr 2
      ext z
      simp only [F,G,mem_inter,mem_union])
    (by
      intro v
      have hv := hLoad' v
      convert hv using 1 <;> congr 2 <;> ext z <;>
        simp only [F,G,mem_filter,mem_union]) hCountLoad
  obtain ⟨T,M,hT,hCov,hM,hDegree,hNext,hKeep⟩ := h
  refine ⟨T,M,hT,?_,?_,hDegree,?_,?_⟩
  · convert hCov using 1
    ext e
    simp only [mem_union]
  · intro e he
    have h := hM he
    simp only [mem_sdiff] at h ⊢
    exact h
  · convert hNext using 1
    ext e
    simp only [mem_sdiff]
  · convert hKeep using 1 <;> ext e <;> simp only [mem_inter,mem_sdiff]

end OverfullWork.ChenShan
