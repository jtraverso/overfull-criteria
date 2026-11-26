module

public import OverfullWork.ChenShanTriangleHypergraph
public import OverfullWork.ChenShanFractionalDecomposition

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

noncomputable def supportedTriangles (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) :
    Finset (A × B × W) :=
  univ.filter (fun t => E t.1 t.2.1 ∧ L t.1 t.2.2 ∧ R t.2.1 t.2.2)

private theorem ab_incident_sum (f : A → B → W → ℝ) (a : A) (b : B) :
    (∑ t ∈ univ.filter (fun t => (.inl a,.inr (.inl b)) ∈ triangleEdges t),
      f t.1 t.2.1 t.2.2) = ∑ w, f a b w := by
  let i : W ↪ A × B × W := ⟨fun w => (a,b,w),fun _ _ h => congrArg (fun t => t.2.2) h⟩
  have hEq : (univ : Finset (A × B × W)).filter
      (fun t => (.inl a,.inr (.inl b)) ∈ triangleEdges t) = univ.map i := by
    ext ⟨x,y,w⟩
    simp [triangleEdges,i,eq_comm]
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨w,rfl⟩
    · rintro ⟨z,h⟩
      have h' : (x,y,w) = (a,b,z) := h
      exact ⟨(congrArg Prod.fst h').symm,(congrArg (fun t => t.2.1) h').symm⟩
  rw [hEq,sum_map]
  rfl

private theorem aw_incident_sum (f : A → B → W → ℝ) (a : A) (w : W) :
    (∑ t ∈ univ.filter (fun t => (.inr (.inr w),.inl a) ∈ triangleEdges t),
      f t.1 t.2.1 t.2.2) = ∑ b, f a b w := by
  let i : B ↪ A × B × W := ⟨fun b => (a,b,w),fun _ _ h => congrArg (fun t => t.2.1) h⟩
  have hEq : (univ : Finset (A × B × W)).filter
      (fun t => (.inr (.inr w),.inl a) ∈ triangleEdges t) = univ.map i := by
    ext ⟨x,b,y⟩
    simp [triangleEdges,i,eq_comm,and_comm]
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨z,h⟩
      have h' : (x,b,y) = (a,z,w) := h
      exact ⟨(congrArg Prod.fst h').symm,(congrArg (fun t => t.2.2) h').symm⟩
  rw [hEq,sum_map]
  rfl

private theorem bw_incident_sum (f : A → B → W → ℝ) (b : B) (w : W) :
    (∑ t ∈ univ.filter (fun t => (.inr (.inl b),.inr (.inr w)) ∈ triangleEdges t),
      f t.1 t.2.1 t.2.2) = ∑ a, f a b w := by
  let i : A ↪ A × B × W := ⟨fun a => (a,b,w),fun _ _ h => congrArg Prod.fst h⟩
  have hEq : (univ : Finset (A × B × W)).filter
      (fun t => (.inr (.inl b),.inr (.inr w)) ∈ triangleEdges t) = univ.map i := by
    ext ⟨a,x,y⟩
    simp [triangleEdges,i,eq_comm]
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨a,rfl⟩
    · rintro ⟨z,h⟩
      have h' : (a,x,y) = (z,b,w) := h
      exact ⟨(congrArg (fun t => t.2.1) h').symm,(congrArg (fun t => t.2.2) h').symm⟩
  rw [hEq,sum_map]
  rfl

/-- In Lemma 4.10, independently retaining a triangle with probability
(k/3) times its fractional weight gives total retention mass k/3 on
every graph edge. -/
theorem triangle_retention_mass_eq (ω : A → B → W → ℝ)
    (hω : TriangleSupported E L R ω) (hMargins : triangleBoundary ω = edgeOnes E L R)
    (e : OrientedTripartiteEdge A B W) (he : e ∈ tripartiteArcs E L R) :
    (∑ t ∈ (supportedTriangles E L R).filter (fun t => e ∈ triangleEdges t),
      (Fintype.card W : ℝ)/3 * ω t.1 t.2.1 t.2.2) = (Fintype.card W : ℝ)/3 := by
  rw [← mul_sum]
  suffices hUnit : (∑ t ∈ (supportedTriangles E L R).filter (fun t => e ∈ triangleEdges t),
      ω t.1 t.2.1 t.2.2) = 1 by rw [hUnit,mul_one]
  let S : Finset (A × B × W) := univ.filter (fun t => e ∈ triangleEdges t)
  have hSub : (supportedTriangles E L R).filter (fun t => e ∈ triangleEdges t) ⊆ S :=
    filter_subset_filter _ (subset_univ _)
  have hSum : (∑ t ∈ (supportedTriangles E L R).filter (fun t => e ∈ triangleEdges t),
      ω t.1 t.2.1 t.2.2) = ∑ t ∈ S, ω t.1 t.2.1 t.2.2 := by
    apply sum_subset hSub
    intro t ht hn
    have he' : e ∈ triangleEdges t := (mem_filter.mp ht).2
    apply hω
    intro hl
    exact hn (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hl⟩,he'⟩)
  rw [hSum]
  have hm := mem_tripartiteArcs.mp he
  rcases e with ⟨v,u⟩
  rcases v with a | (b | w) <;> rcases u with a' | (b' | w') <;>
    simp only [tripartiteArc] at hm
  · dsimp only [S]
    rw [ab_incident_sum]
    have hh := congrArg (fun r => TripartiteEdgeWeights.ab r a b') hMargins
    simpa [triangleBoundary,edgeOnes,hm] using hh
  · dsimp only [S]
    rw [bw_incident_sum]
    have hh := congrArg (fun r => TripartiteEdgeWeights.bw r b w') hMargins
    simpa [triangleBoundary,edgeOnes,hm] using hh
  · dsimp only [S]
    rw [aw_incident_sum]
    have hh := congrArg (fun r => TripartiteEdgeWeights.aw r a' w) hMargins
    simpa [triangleBoundary,edgeOnes,hm] using hh

theorem triangle_retention_probability_bounds {k x : ℝ} (hk : 0 < k)
    (hx : 1/(2*k) ≤ x ∧ x ≤ 3/(2*k)) :
    1/6 ≤ k/3*x ∧ k/3*x ≤ 1/2 := by
  have h₁ := mul_le_mul_of_nonneg_left hx.1 (show 0 ≤ k/3 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ k/3 by positivity)
  have hL : k/3*(1/(2*k)) = 1/6 := by field_simp; norm_num
  have hU : k/3*(3/(2*k)) = 1/2 := by field_simp
  exact ⟨hL ▸ h₁,hU ▸ h₂⟩

/-- Local balance makes the three pairs of vertex classes contribute
the same number of edges. -/
theorem tripartite_arc_count_eq_three_base (h : TripartiteLocallyBalanced E L R) :
    (tripartiteArcs E L R).card = 3*(∑ a, #(univ.filter (E a))) := by
  have hCount :
      (tripartiteArcs E L R).card =
        (∑ a, #(univ.filter (E a))) +
          ((∑ b, #(univ.filter (R b))) + (∑ w, #(univ.filter (fun a => L a w)))) := by
    rw [tripartiteArcs,card_filter,Fintype.sum_prod_type,Fintype.sum_sum_type]
    simp [Fintype.sum_sum_type,tripartiteArc]
    simp only [card_filter]
    congr 1
  have hLeft (a : A) : #(univ.filter (E a)) = #(univ.filter (L a)) := by
    simpa only [Fintype.card_subtype] using h.1 a
  have hRight (b : B) : #(univ.filter (fun a => E a b)) = #(univ.filter (R b)) := by
    simpa only [Fintype.card_subtype] using h.2.1 b
  have hSwapL :
      (∑ w, #(univ.filter (fun a => L a w))) = ∑ a, #(univ.filter (L a)) := by
    simp only [card_filter]
    exact sum_comm
  have hSwapE :
      (∑ b, #(univ.filter (fun a => E a b))) = ∑ a, #(univ.filter (E a)) := by
    simp only [card_filter]
    exact sum_comm
  rw [hCount,hSwapL]
  simp_rw [← hLeft,← hRight,hSwapE]
  omega

theorem tripartite_arc_count_le_three_sq {m : ℕ}
    (hA : Fintype.card A = m) (hB : Fintype.card B = m) (hb : TripartiteLocallyBalanced E L R) :
    (tripartiteArcs E L R).card ≤ 3*m*m := by
  have h : (∑ a, #(univ.filter (E a))) ≤ ∑ _a : A, m := by
    apply sum_le_sum
    intro a _
    exact (card_filter_le _ _).trans_eq (by rw [card_univ,hB])
  simp only [sum_const,card_univ,nsmul_eq_mul,hA] at h
  rw [tripartite_arc_count_eq_three_base hb,mul_assoc]
  exact Nat.mul_le_mul_left _ h

end OverfullWork.ChenShan
