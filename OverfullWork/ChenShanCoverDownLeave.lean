module

public import OverfullWork.ChenShanLemma410
public import OverfullWork.ChenShanLemma413
public import OverfullWork.ChenShanNestedIterationClosure
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe uA uB uW
variable {A : Type uA} {B : Type uB} {W : Type uW}
variable [Fintype A] [Fintype B] [Fintype W]

abbrev baseRelation (G : Finset (OrientedTripartiteEdge A B W)) (a : A) (b : B) : Prop :=
  (Sum.inl a, Sum.inr (Sum.inl b)) ∈ G

abbrev leftColorRelation (G : Finset (OrientedTripartiteEdge A B W)) (a : A) (w : W) : Prop :=
  (Sum.inr (Sum.inr w), Sum.inl a) ∈ G

abbrev rightColorRelation (G : Finset (OrientedTripartiteEdge A B W)) (b : B) (w : W) : Prop :=
  (Sum.inr (Sum.inl b), Sum.inr (Sum.inr w)) ∈ G

theorem tripartiteArcs_recover_subgraph
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {G : Finset (OrientedTripartiteEdge A B W)} (hG : G ⊆ tripartiteArcs E P Q) :
    tripartiteArcs (baseRelation G) (leftColorRelation G) (rightColorRelation G) = G := by
  ext ⟨x,y⟩
  have hs : (x,y) ∈ G → tripartiteArc E P Q x y :=
    fun h => (mem_filter.mp (hG h)).2
  rcases x with a | (b | w) <;> rcases y with a' | (b' | w') <;>
    simp only [mem_tripartiteArcs,tripartiteArc,baseRelation,
      leftColorRelation,rightColorRelation] at hs ⊢ <;> tauto

/-- Projecting a deletion onto a class pair loses at most its total
incident degree, in either orientation. -/
private theorem projected_degree_loss {X V : Type*} [Fintype X]
    (G D : Finset (V × V)) (v : V) (f : X ↪ (V × V))
    (hInc : ∀ x, (f x).1 = v ∨ (f x).2 = v) :
    (#(univ.filter (fun x => f x ∈ G)) : ℝ) ≤
        (#(univ.filter (fun x => f x ∈ G \ D)) : ℝ) + incidentDegree D v ∧
    (#(univ.filter (fun x => f x ∉ G \ D)) : ℝ) ≤
        (#(univ.filter (fun x => f x ∉ G)) : ℝ) + incidentDegree D v := by
  have hLost : #(univ.filter (fun x => f x ∈ D)) ≤ incidentDegree D v := by
    rw [← card_map f]
    apply card_le_card
    intro e he
    obtain ⟨x,hx,rfl⟩ := mem_map.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp hx).2,hInc x⟩
  have hDegree := card_filter_le_inter_add_missing (fun x => f x ∈ G) (fun x => f x ∉ D)
  have hNonneighbors := card_missing_conjunction_le (fun x => f x ∈ G) (fun x => f x ∉ D)
  simp only [not_not, ← mem_sdiff] at hDegree hNonneighbors
  constructor
  · have h := hDegree.trans (Nat.add_le_add_left hLost _)
    norm_cast
    convert h using 1
    congr 3
  · have h := hNonneighbors.trans (Nat.add_le_add_left hLost _)
    norm_cast
    convert h using 1
    congr 3

/-- The repair from Lemma 4.13 leaves the density and balance needed by
Lemma 4.10, provided its degree cost fits the density margins. -/
theorem exists_repaired_dense_remainder
    (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (n : ℕ) {η ξ ε : ℝ} (hη : 0 < η) (hξ : 0 ≤ ξ)
    (hSmall : Real.sqrt ξ ≤ min (η/32) (1/128))
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hW : (n : ℝ)/2 ≤ Fintype.card W ∧ (Fintype.card W : ℝ) ≤ 2*n)
    (hAB : ∀ a, (1/2+η)*n ≤ (#(univ.filter (E a)) : ℝ))
    (hBA : ∀ b, (1/2+η)*n ≤ (#(univ.filter (fun a => E a b)) : ℝ))
    (hε : ε ≤ 1/16)
    (hAW : ∀ a, (#(univ.filter (fun w => ¬ P a w)) : ℝ) ≤ ε*n)
    (hBW : ∀ b, (#(univ.filter (fun w => ¬ Q b w)) : ℝ) ≤ ε*n)
    (hWA : ∀ w, (#(univ.filter (fun a => ¬ P a w)) : ℝ) ≤ ε*n)
    (hWB : ∀ w, (#(univ.filter (fun b => ¬ Q b w)) : ℝ) ≤ ε*n)
    (hImbalance : ∀ v, |(arcDivergence (tripartiteArcs E P Q) v : ℝ)| ≤ ξ*n) :
    let G := tripartiteArcs E P Q
    ∃ D ⊆ G, (∀ v, (incidentDegree D v : ℝ) ≤ 5*Real.sqrt ξ*n) ∧
      DenseTripartite (baseRelation (G \ D)) (leftColorRelation (G \ D))
        (rightColorRelation (G \ D)) n (η/2) (ε+5*Real.sqrt ξ) := by
  let G := tripartiteArcs E P Q
  have hεn := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) n)
  have hSixteen : ε*(n:ℝ) ≤ (n:ℝ)/16 := by linarith only [hεn]
  obtain ⟨D,hD,hBalance,hDegree⟩ := exists_tripartite_balancing_deletion E P Q n η ξ hη hξ
    hSmall hA hB hW hAB hBA (fun a => (hAW a).trans hSixteen)
    (fun b => (hBW b).trans hSixteen) (fun w => (hWA w).trans hSixteen)
    (fun w => (hWB w).trans hSixteen) hImbalance
  have hSub : G \ D ⊆ tripartiteArcs E P Q := sdiff_subset
  have hBalance' := tripartiteLocallyBalanced_of_arcBalanced
    (by rw [tripartiteArcs_recover_subgraph hSub]; exact hBalance)
  have hηn := mul_le_mul_of_nonneg_right (hSmall.trans (min_le_left _ _))
    (Nat.cast_nonneg (α := ℝ) n)
  refine ⟨D,hD,hDegree,⟨hA,hB,hBalance',?_,?_,?_,?_,?_,?_⟩⟩
  · intro a
    let f : B ↪ OrientedTripartiteEdge A B W :=
      ⟨fun b => (.inl a,.inr (.inl b)),by intro x y h; simpa using congrArg Prod.snd h⟩
    have h := (projected_degree_loss G D (.inl a) f (fun _ => Or.inl rfl)).1
    have hLoss : (#(univ.filter (E a)) : ℝ) ≤ (#(univ.filter (baseRelation (G \ D) a)) : ℝ) + incidentDegree D (.inl a) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (1/2+η/2)*n ≤ (#(univ.filter (baseRelation (G \ D) a)) : ℝ) := by
      linarith only [hLoss,hAB a,hDegree (.inl a),hηn,mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) n)]
    convert hBound using 1
    congr 5
  · intro b
    let f : A ↪ OrientedTripartiteEdge A B W :=
      ⟨fun a => (.inl a,.inr (.inl b)),by intro x y h; simpa using congrArg Prod.fst h⟩
    have h := (projected_degree_loss G D (.inr (.inl b)) f (fun _ => Or.inr rfl)).1
    have hLoss : (#(univ.filter (fun a => E a b)) : ℝ) ≤ (#(univ.filter (fun a => baseRelation (G \ D) a b)) : ℝ) + incidentDegree D (.inr (.inl b)) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (1/2+η/2)*n ≤ (#(univ.filter (fun a => baseRelation (G \ D) a b)) : ℝ) := by
      linarith only [hLoss,hBA b,hDegree (.inr (.inl b)),hηn,mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) n)]
    convert hBound using 1
    congr 5
  · intro a
    let f : W ↪ OrientedTripartiteEdge A B W :=
      ⟨fun w => (.inr (.inr w),.inl a),by intro x y h; simpa using congrArg Prod.fst h⟩
    have h := (projected_degree_loss G D (.inl a) f (fun _ => Or.inr rfl)).2
    have hLoss : (#(univ.filter (fun w => ¬ leftColorRelation (G \ D) a w)) : ℝ) ≤ (#(univ.filter (fun w => ¬ P a w)) : ℝ) + incidentDegree D (.inl a) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (#(univ.filter (fun w => ¬ leftColorRelation (G \ D) a w)) : ℝ) ≤ (ε+5*Real.sqrt ξ)*n := by
      linarith only [hLoss,hAW a,hDegree (.inl a)]
    convert hBound using 1
    congr 5
  · intro b
    let f : W ↪ OrientedTripartiteEdge A B W :=
      ⟨fun w => (.inr (.inl b),.inr (.inr w)),by intro x y h; simpa using congrArg Prod.snd h⟩
    have h := (projected_degree_loss G D (.inr (.inl b)) f (fun _ => Or.inl rfl)).2
    have hLoss : (#(univ.filter (fun w => ¬ rightColorRelation (G \ D) b w)) : ℝ) ≤ (#(univ.filter (fun w => ¬ Q b w)) : ℝ) + incidentDegree D (.inr (.inl b)) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (#(univ.filter (fun w => ¬ rightColorRelation (G \ D) b w)) : ℝ) ≤ (ε+5*Real.sqrt ξ)*n := by
      linarith only [hLoss,hBW b,hDegree (.inr (.inl b))]
    convert hBound using 1
    congr 5
  · intro w
    let f : A ↪ OrientedTripartiteEdge A B W :=
      ⟨fun a => (.inr (.inr w),.inl a),by intro x y h; simpa using congrArg Prod.snd h⟩
    have h := (projected_degree_loss G D (.inr (.inr w)) f (fun _ => Or.inl rfl)).2
    have hLoss : (#(univ.filter (fun a => ¬ leftColorRelation (G \ D) a w)) : ℝ) ≤ (#(univ.filter (fun a => ¬ P a w)) : ℝ) + incidentDegree D (.inr (.inr w)) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (#(univ.filter (fun a => ¬ leftColorRelation (G \ D) a w)) : ℝ) ≤ (ε+5*Real.sqrt ξ)*n := by
      linarith only [hLoss,hWA w,hDegree (.inr (.inr w))]
    convert hBound using 1
    congr 5
  · intro w
    let f : B ↪ OrientedTripartiteEdge A B W :=
      ⟨fun b => (.inr (.inl b),.inr (.inr w)),by intro x y h; simpa using congrArg Prod.fst h⟩
    have h := (projected_degree_loss G D (.inr (.inr w)) f (fun _ => Or.inr rfl)).2
    have hLoss : (#(univ.filter (fun b => ¬ rightColorRelation (G \ D) b w)) : ℝ) ≤ (#(univ.filter (fun b => ¬ Q b w)) : ℝ) + incidentDegree D (.inr (.inr w)) := by
      convert h using 1 <;> congr 3 <;>
        first
        | funext x
          exact propext (by simp [G,f,tripartiteArc]; rfl)
        | ext x
          simp [G,f,tripartiteArc]
          rfl
    have hBound : (#(univ.filter (fun b => ¬ rightColorRelation (G \ D) b w)) : ℝ) ≤ (ε+5*Real.sqrt ξ)*n := by
      linarith only [hLoss,hWB w,hDegree (.inr (.inr w))]
    convert hBound using 1
    congr 5

/-- The repair and the triangle packing together establish the leave
bound and exact packed complement in (4.24). -/
theorem exists_repaired_packing_leave
    (η ζ : ℝ) (hη : 0 < η) (hηone : η < 1) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ n₀ : ℕ, ε₀ = coverDownPackingCap (η/2) ∧ 0 < ε₀ ∧
    ∀ (n : ℕ), n₀ ≤ n →
    ∀ (A : Type uA) (B : Type uB) (W : Type uW) [Fintype A] [Fintype B] [Fintype W],
    ∀ (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (ξ ε : ℝ), 0 ≤ ξ → 0 ≤ ε →
    (Real.sqrt ξ ≤ min (η/32) (1/128)) →
    (Fintype.card A = n) → (Fintype.card B = n) →
    ((n : ℝ)/2 ≤ Fintype.card W ∧ (Fintype.card W : ℝ) ≤ 2*n) →
    (∀ a, (1/2+η)*n ≤ (#(univ.filter (E a)) : ℝ)) →
    (∀ b, (1/2+η)*n ≤ (#(univ.filter (fun a => E a b)) : ℝ)) →
    (ε ≤ 1/16) →
    (∀ a, (#(univ.filter (fun w => ¬ P a w)) : ℝ) ≤ ε*n) →
    (∀ b, (#(univ.filter (fun w => ¬ Q b w)) : ℝ) ≤ ε*n) →
    (∀ w, (#(univ.filter (fun a => ¬ P a w)) : ℝ) ≤ ε*n) →
    (∀ w, (#(univ.filter (fun b => ¬ Q b w)) : ℝ) ≤ ε*n) →
    (ε + 5*Real.sqrt ξ ≤ ε₀) →
    (5*Real.sqrt ξ ≤ ζ/2) →
    (∀ v, |(arcDivergence (tripartiteArcs E P Q) v : ℝ)| ≤ ξ*n) →
    let G := tripartiteArcs E P Q
    ∃ L : Finset (OrientedTripartiteEdge A B W), ∃ T : Finset (A × B × W),
      L ⊆ G ∧ (∀ v, (incidentDegree L v : ℝ) ≤ ζ*n) ∧
      (↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      G \ L = coveredEdges (triangleHypergraph T) := by
  have hη₂ : 0 < η/2 := by positivity
  have hη₂' : η/2 < 1/2 := by linarith only [hηone]
  obtain ⟨ε₀,n₀,hCap,hε₀,hPack⟩ :=
    exists_triangle_packing_with_explicit_cap.{uA,uB,uW} (η/2) (ζ/2) hη₂ hη₂' (by positivity)
  refine ⟨ε₀,n₀,hCap,hε₀,?_⟩
  intro n hn A B W _ _ _ E P Q ξ ε hξ hε₁ hSmall hA hB hW hAB hBA hε hAW hBW hWA hWB hThreshold hRepair hImbalance
  let G := tripartiteArcs E P Q
  obtain ⟨D,hD,hDegree,hDense⟩ := exists_repaired_dense_remainder E P Q n hη hξ
    hSmall hA hB hW hAB hBA hε hAW hBW hWA hWB hImbalance
  let H := G \ D
  have hEq := tripartiteArcs_recover_subgraph (show H ⊆ tripartiteArcs E P Q from sdiff_subset)
  have hεnonneg : 0 ≤ ε+5*Real.sqrt ξ := by positivity
  obtain ⟨T,hSupported,hDisj,_,hLeave⟩ := hPack n hn A B W
    (baseRelation H) (leftColorRelation H) (rightColorRelation H)
    (ε+5*Real.sqrt ξ) hεnonneg hThreshold hDense
  let C := coveredEdges (triangleHypergraph T)
  have hC : C ⊆ G \ D := by
    rw [show G \ D = H from rfl, ← hEq]
    apply coveredEdges_subset
    intro S hS
    obtain ⟨t,ht,rfl⟩ := mem_map.mp hS
    apply triangleEdges_subset_tripartiteArcs
    have hs := hSupported ht
    simpa only [supportedTriangles,mem_filter,mem_univ,true_and] using hs
  rw [hEq] at hLeave
  have hD' : ∀ v, (incidentDegree D v : ℝ) ≤ (ζ/2)*n := fun v =>
    (hDegree v).trans (mul_le_mul_of_nonneg_right hRepair (Nat.cast_nonneg _))
  obtain ⟨hL,hCovered,hBudget⟩ := repair_and_packing_leave G D C hD
    (by convert hC using 1; congr 3; apply Subsingleton.elim)
    ((ζ/2)*n) ((ζ/2)*n) hD' (by
      intro v
      have h := hLeave v
      unfold packingLeave at h
      convert h using 1
      congr 6
      apply Subsingleton.elim)
  refine ⟨_,T,hL,fun v => (hBudget v).trans (by ring_nf; rfl),hDisj,?_⟩
  convert hCovered using 1
  congr 3
  apply Subsingleton.elim

/-- Remove the induced interior and the crossing reserve, then apply
the imbalance bound and obtain the leave in (4.24). -/
theorem exists_cover_down_leave_after_reserve
    (η ζ : ℝ) (hη : 0 < η) (hηone : η < 1) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ n₀ : ℕ, ε₀ = coverDownPackingCap (η/2) ∧ 0 < ε₀ ∧
    ∀ (n : ℕ), n₀ ≤ n →
    ∀ (A : Type uA) (B : Type uB) (W : Type uW) [Fintype A] [Fintype B] [Fintype W],
    ∀ (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
      (U : Finset (TripartiteVertex A B W)) (R : TripartiteArcSet A B W),
    let G := tripartiteArcs E P Q
    let GU := G ∩ (U ×ˢ U)
    let H := (G \ GU) \ R
    ∀ (ξ s ε : ℝ), 0 ≤ ξ → s ≤ n → 1/2 ≤ ξ*n → 0 ≤ ε →
    R ⊆ G \ GU → ArcBalanced G →
    (∀ v, |(arcDivergence GU v : ℝ)| ≤ 2*ξ*s+1/2) →
    (∀ v, |(arcDivergence R v : ℝ)| ≤ ξ*n) →
    Real.sqrt (4*ξ) ≤ min (η/32) (1/128) →
    Fintype.card A = n → Fintype.card B = n →
    ((n : ℝ)/2 ≤ Fintype.card W ∧ (Fintype.card W : ℝ) ≤ 2*n) →
    (∀ a, (1/2+η)*n ≤ (#(univ.filter (baseRelation H a)) : ℝ)) →
    (∀ b, (1/2+η)*n ≤ (#(univ.filter (fun a => baseRelation H a b)) : ℝ)) →
    ε ≤ 1/16 →
    (∀ a, (#(univ.filter (fun w => ¬ leftColorRelation H a w)) : ℝ) ≤ ε*n) →
    (∀ b, (#(univ.filter (fun w => ¬ rightColorRelation H b w)) : ℝ) ≤ ε*n) →
    (∀ w, (#(univ.filter (fun a => ¬ leftColorRelation H a w)) : ℝ) ≤ ε*n) →
    (∀ w, (#(univ.filter (fun b => ¬ rightColorRelation H b w)) : ℝ) ≤ ε*n) →
    ε+5*Real.sqrt (4*ξ) ≤ ε₀ →
    5*Real.sqrt (4*ξ) ≤ ζ/2 →
    ∃ L : TripartiteArcSet A B W, ∃ T : Finset (A × B × W),
      L ⊆ H ∧ (∀ v, (incidentDegree L v : ℝ) ≤ ζ*n) ∧
      (↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      H \ L = coveredEdges (triangleHypergraph T) ∧ ArcBalanced (GU ∪ R ∪ L) := by
  obtain ⟨ε₀,n₀,hCap,hε₀,hPack⟩ := exists_repaired_packing_leave.{uA,uB,uW}
    η ζ hη hηone hζ
  refine ⟨ε₀,n₀,hCap,hε₀,?_⟩
  intro n hn A B W _ _ _ E P Q U R G GU H ξ s ε hξ hs hRound hε₀' hR hG hUdeg hRdeg hSmall hA hB hW hAB hBA
    hε hAW hBW hWA hWB hThreshold hRepair
  have hGU : GU ⊆ G := inter_subset_left
  have hR' : R ⊆ G \ GU := hR
  have hH : H ⊆ tripartiteArcs E P Q := sdiff_subset.trans sdiff_subset
  have hEq := tripartiteArcs_recover_subgraph hH
  have hImbalance : ∀ v, |(arcDivergence H v : ℝ)| ≤ (4*ξ)*n := by
    intro v
    have h := remainder_imbalance_after_cut_deletions G GU R hG hGU
      (by convert hR' using 1; congr 3; apply Subsingleton.elim) hξ hs hRound hUdeg hRdeg v
    convert h using 1
    congr 6
    ext e
    simp only [H,mem_sdiff]
  have hResult := hPack n hn A B W
    (baseRelation H) (leftColorRelation H) (rightColorRelation H) (4*ξ) ε
    (by positivity) hε₀' hSmall hA hB hW
    (by intro a; convert hAB a using 1; congr 4)
    (by intro b; convert hBA b using 1; congr 4) hε
    (by intro a; convert hAW a using 1; congr 4)
    (by intro b; convert hBW b using 1; congr 4)
    (by intro w; convert hWA w using 1; congr 4)
    (by intro w; convert hWB w using 1; congr 4) hThreshold hRepair
    (by rw [hEq]; exact hImbalance)
  obtain ⟨L,T,hL,hDegree,hDisj,hCovered⟩ := hResult
  rw [hEq] at hL hCovered
  have hCovered' : H \ L = coveredEdges (triangleHypergraph T) := by
    convert hCovered using 1
  let C := coveredEdges (triangleHypergraph T)
  have hC : C ⊆ G := by rw [show C = H \ L from hCovered'.symm]; exact sdiff_subset.trans hH
  have hBalC : ArcBalanced C := by
    apply arcBalanced_coveredEdges _ hDisj
    intro S hS
    obtain ⟨t,_,rfl⟩ := mem_map.mp hS
    exact triangleEdges_balanced t
  have hRemain : G \ C = GU ∪ R ∪ L := by
    rw [show C = H \ L from hCovered'.symm]
    ext e
    have hu (he : e ∈ GU) : e ∈ G := hGU he
    have hr (he : e ∈ R) : e ∈ G := (mem_sdiff.mp (hR' he)).1
    have hl (he : e ∈ L) : e ∈ G := hH (hL he)
    change e ∈ G \ (((G \ GU) \ R) \ L) ↔ _
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hg,hn⟩
      by_cases heu : e ∈ GU
      · exact Or.inl (Or.inl heu)
      by_cases her : e ∈ R
      · exact Or.inl (Or.inr her)
      exact Or.inr (not_not.mp (fun hel => hn ⟨⟨⟨hg,heu⟩,her⟩,hel⟩))
    · rintro ((heu | her) | hel)
      · exact ⟨hu heu,fun h => h.1.1.2 heu⟩
      · exact ⟨hr her,fun h => h.1.2 her⟩
      · exact ⟨hl hel,fun h => h.2 hel⟩
  have hBal : ArcBalanced (GU ∪ R ∪ L) := by
    have h := arcBalanced_sdiff hC hG hBalC
    rw [← hRemain]
    convert h using 1
    congr 2
    apply Subsingleton.elim
  exact ⟨L,T,hL,hDegree,hDisj,hCovered',hBal⟩

end OverfullWork.ChenShan
