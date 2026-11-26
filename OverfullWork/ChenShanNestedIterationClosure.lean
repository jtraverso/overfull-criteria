module

public import OverfullWork.ChenShanIterationBase
public import OverfullWork.ChenShanPathImbalance
public import OverfullWork.ChenShanRepairPathCounts
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- When the edges used inside U are exactly a subset M avoiding
the protected level V, the next remainder preserves the protected
induced graph and loses exactly M from the original graph on U. -/
theorem protected_iteration_update {X : Type*}
    (G Gᵢ M : Finset (X × X)) (U V : Finset X)
    (hVU : V ⊆ U) (hFull : Gᵢ ∩ (U ×ˢ U) = G ∩ (U ×ˢ U))
    (hM : M ⊆ Gᵢ ∩ (U ×ˢ U)) (hDisj : Disjoint M (V ×ˢ V)) :
    let Gnext := (Gᵢ ∩ (U ×ˢ U)) \ M
    Gnext ∩ (V ×ˢ V) = G ∩ (V ×ˢ V) ∧
      (G ∩ (U ×ˢ U)) \ Gnext = M := by
  dsimp only
  rw [hFull] at hM ⊢
  constructor
  · ext e
    have hVU' : e ∈ V ×ˢ V → e ∈ U ×ˢ U := by
      intro he
      exact mem_product.mpr ⟨hVU (mem_product.mp he).1,hVU (mem_product.mp he).2⟩
    have hNo : e ∈ V ×ˢ V → e ∉ M := fun hv hm => disjoint_left.mp hDisj hm hv
    simp only [mem_inter,mem_sdiff]
    tauto
  · ext e
    have hIn : e ∈ M → e ∈ G ∩ (U ×ˢ U) := fun he => hM he
    simp only [mem_inter,mem_sdiff] at hIn ⊢
    tauto

variable {A B W : Type*}

/-- Step 3 of Theorem 4.15. A decomposition outside the absorber and
final leave combines with the decomposition supplied by absorption. -/
theorem finish_with_absorbed_leave
    {E H L : A → B → Prop} {EA HA LA : A → W → Prop} {EB HB LB : B → W → Prop}
    (hH : ∀ a b, H a b → E a b) (hHA : ∀ a w, HA a w → EA a w)
    (hHB : ∀ b w, HB b w → EB b w)
    (hL : ∀ a b, L a b → E a b) (hLA : ∀ a w, LA a w → EA a w)
    (hLB : ∀ b w, LB b w → EB b w)
    (packed : Nonempty (TripartiteTriangleDecomposition
      (fun a b => E a b ∧ ¬H a b ∧ ¬L a b)
      (fun a w => EA a w ∧ ¬HA a w ∧ ¬LA a w)
      (fun b w => EB b w ∧ ¬HB b w ∧ ¬LB b w)))
    (absorbed : Nonempty (TripartiteTriangleDecomposition
      (fun a b => H a b ∨ L a b) (fun a w => HA a w ∨ LA a w)
      (fun b w => HB b w ∨ LB b w))) :
    Nonempty (TripartiteTriangleDecomposition E EA EB) := by
  obtain ⟨D⟩ := packed
  obtain ⟨D'⟩ := absorbed
  have hD := D.union D' (by intro a b h h'; tauto) (by intro a w h h'; tauto)
    (by intro b w h h'; tauto)
  have he {p q r : Prop} (hq : q → p) (hr : r → p) :
      ((p ∧ ¬q ∧ ¬r) ∨ (q ∨ r)) = p := propext (by tauto)
  simpa only [he (hH _ _) (hL _ _),he (hHA _ _) (hLA _ _),he (hHB _ _) (hLB _ _)] using
    (Nonempty.intro hD)


/-- In Step 2 the original balance, the induced-level imbalance
bound, and (R1) control the remainder to which Lemma 4.13 is applied. -/
theorem remainder_imbalance_after_cut_deletions {V : Type*}
    (G U R : Finset (V × V)) (hG : ArcBalanced G)
    (hU : U ⊆ G) (hR : R ⊆ G \ U)
    {ξ n s : ℝ} (hξ : 0 ≤ ξ) (hs : s ≤ n) (hRound : 1/2 ≤ ξ*n)
    (hUdeg : ∀ v, |(arcDivergence U v : ℝ)| ≤ 2*ξ*s+1/2)
    (hRdeg : ∀ v, |(arcDivergence R v : ℝ)| ≤ ξ*n) :
    ∀ v, |(arcDivergence ((G \ U) \ R) v : ℝ)| ≤ 4*ξ*n := by
  intro v
  have hZero : arcDivergence G v = 0 := by
    unfold arcDivergence
    exact sub_eq_zero.mpr (congrArg (fun x : ℕ => (x:ℤ)) (hG v))
  rw [arcDivergence_sdiff hR,arcDivergence_sdiff hU,hZero,Int.cast_sub,Int.cast_sub,Int.cast_zero,
    zero_sub]
  rw [show -(arcDivergence U v:ℝ)-(arcDivergence R v:ℝ) =
    -((arcDivergence U v:ℝ)+(arcDivergence R v:ℝ)) by ring,abs_neg]
  have hSize := mul_le_mul_of_nonneg_left hs hξ
  exact (abs_add_le _ _).trans (by linarith only [hSize,hRound,hUdeg v,hRdeg v])


/-- The transfer from Theorem 4.15 to the available-color formulation
of Theorem 4.16. The degree identities are those of a regular precolored
completion, and the missing incidences count the prescribed colors. -/
theorem residual_coloring_from_dense_decomposition
    [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (usedLeft : A → W → Prop) (usedRight : B → W → Prop)
    (m : ℕ) (η ε : ℝ)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (hLeft : ∀ a, Fintype.card {b // E a b} + Fintype.card {w // usedLeft a w} = Fintype.card W)
    (hRight : ∀ b, Fintype.card {a // E a b} + Fintype.card {w // usedRight b w} = Fintype.card W)
    (hUsed : ∀ w, Fintype.card {a // usedLeft a w} = Fintype.card {b // usedRight b w})
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hAW : ∀ a, ((univ.filter (usedLeft a)).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (usedRight b)).card : ℝ) ≤ ε*m)
    (hWA : ∀ w, ((univ.filter (fun a => usedLeft a w)).card : ℝ) ≤ ε*m)
    (hWB : ∀ w, ((univ.filter (fun b => usedRight b w)).card : ℝ) ≤ ε*m)
    (hDecompose : ∀ (R : A → B → Prop) (S : A → W → Prop) (T : B → W → Prop),
      DenseTripartite R S T m η ε → Nonempty (TripartiteTriangleDecomposition R S T)) :
    Nonempty (SaturatedResidualColoring E (fun a w => ¬usedLeft a w) (fun b w => ¬usedRight b w)) := by
  have hBal := (residual_tripartite_balanced E usedLeft usedRight
    (hA.trans hB.symm) hLeft hRight hUsed).1
  apply (residual_coloring_iff_triangle_decomposition _ _ _).mpr
  apply hDecompose
  refine ⟨hA,hB,hBal,hDegreeA,hDegreeB,?_,?_,?_,?_⟩
  · intro a
    simpa only [not_not] using hAW a
  · intro b
    simpa only [not_not] using hBW b
  · intro w
    simpa only [not_not] using hWA w
  · intro w
    simpa only [not_not] using hWB w


/-- The union of the repair deletions and the packing leave has the
combined degree budget. Its complement is exactly the packed edges,
as required in (4.24). -/
theorem repair_and_packing_leave {V : Type*}
    (G D C : Finset (V × V)) (hD : D ⊆ G) (hC : C ⊆ G \ D) (a b : ℝ)
    (hDegreeD : ∀ v, (incidentDegree D v : ℝ) ≤ a)
    (hDegreeL : ∀ v, (incidentDegree ((G \ D) \ C) v : ℝ) ≤ b) :
    let L := D ∪ ((G \ D) \ C)
    L ⊆ G ∧ G \ L = C ∧ (∀ v, (incidentDegree L v : ℝ) ≤ a+b) := by
  dsimp only
  have hL : (G \ D) \ C ⊆ G := sdiff_subset.trans sdiff_subset
  refine ⟨union_subset hD hL,?_,?_⟩
  · ext e
    have he : e ∈ C → e ∈ G \ D := fun h => hC h
    simp only [mem_sdiff,mem_union] at he ⊢
    tauto
  · have hDisj : Disjoint D ((G \ D) \ C) :=
      disjoint_left.mpr fun e heD heL => (mem_sdiff.mp (mem_sdiff.mp heL).1).2 heD
    intro v
    rw [incidentDegree_union_disjoint hDisj,Nat.cast_add]
    exact add_le_add (hDegreeD v) (hDegreeL v)

end OverfullWork.ChenShan
