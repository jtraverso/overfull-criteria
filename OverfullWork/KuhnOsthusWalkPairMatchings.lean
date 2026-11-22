module

public import OverfullWork.KuhnOsthusWrappedPairCoordinates
public import OverfullWork.MergeReservePacking

@[expose] public section


/-! Kühn–Osthus Lemma 9.3(ii). Repeated Hall matchings on a prepared
subcluster pair with an explicit degree and rectangle budget. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Choose the perfect matchings one at a time. The union already
chosen costs at most one arc per round and endpoint. -/
theorem exists_disjoint_matchings_of_rectangle_budget (D : Digraph V) (k r : ℕ)
    (hOut : ∀ v, r+k ≤ outDegree D v) (hIn : ∀ v, r+k ≤ inDegree D v)
    (hRect : ∀ X Y : Finset V, r ≤ X.card → r ≤ Y.card →
      Y.card*k < incidences D X Y) :
    ∃ M : Fin k → Equiv.Perm V, (∀ j v, D.Adj v (M j v)) ∧
      ∀ i j, i ≠ j → ∀ v, M i v ≠ M j v := by
  have pack (t : ℕ) (ht : t ≤ k) : ∃ M : Fin t → Equiv.Perm V,
      (∀ j v, D.Adj v (M j v)) ∧ ∀ i j, i ≠ j → ∀ v, M i v ≠ M j v := by
    induction t with
    | zero => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
    | succ t ih =>
      have ht' : t ≤ k := (Nat.le_succ t).trans ht
      obtain ⟨M,hM,hApart⟩ := ih ht'
      let E := matchingUnion M
      let R := D \ E
      have hE : E ≤ D := by
        rintro x y ⟨j,rfl⟩
        exact hM j x
      have hR (x : V) : r ≤ inDegree R x ∧ r ≤ outDegree R x := by
        obtain ⟨hi,ho⟩ := residual_semidegrees D E hE x
        change inDegree R x + inDegree E x = inDegree D x at hi
        change outDegree R x + outDegree E x = outDegree D x at ho
        obtain ⟨hi',ho'⟩ := matchingUnion_semidegrees M x
        have hInX := hIn x
        have hOutX := hOut x
        change inDegree E x ≤ t at hi'
        change outDegree E x ≤ t at ho'
        constructor <;> omega
      have hPos (X Y : Finset V) (hX : r ≤ X.card) (hY : r ≤ Y.card) :
          0 < incidences R X Y := by
        have hPart := DirectedArcSelection.incidence_partition D E hE X Y
        have hCap : incidences E X Y ≤ Y.card*k :=
          (incidences_le_card_mul_indegree E X Y t (fun v => (matchingUnion_semidegrees M v).1)).trans
            (Nat.mul_le_mul_left Y.card ht')
        have h := hRect X Y hX hY
        change incidences R X Y + incidences E X Y = incidences D X Y at hPart
        omega
      obtain ⟨f,hf⟩ := exists_matching_of_rectangle_threshold R.Adj r rfl
        (fun v => (hR v).2) (fun v => (hR v).1) (by
          intro X Y hX hY
          by_contra! hNone
          have hZero : incidences R X Y = 0 := by
            apply sum_eq_zero
            intro y hy
            apply card_eq_zero.mpr
            rw [eq_empty_iff_forall_notMem]
            intro x hx
            have he := (@mem_filter _ _ (Classical.decPred _) _ _).mp hx
            exact hNone x he.1 y hy he.2
          exact (Nat.ne_of_gt (hPos X Y hX hY)) hZero)
      refine ⟨Fin.snoc M f,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.snoc_last] using fun v => (hf v).1
        · simpa only [Fin.snoc_castSucc] using hM i
      · intro i j
        refine Fin.lastCases ?_ (fun a => ?_) i
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ v h => ?_) j
          exact (hf v).2 ⟨b,by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using h.symm⟩
        · refine Fin.lastCases (fun _ v h => ?_) (fun b h v => ?_) j
          · exact (hf v).2 ⟨a,by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using h⟩
          · simpa only [Fin.snoc_castSucc] using hApart a b
              (fun he => h (congrArg Fin.castSucc he)) v
  exact pack k le_rfl

/-- The explicit version of the paper's repeated matching step for
one pair of quarters. Unequal density centres may be used in
different pairs as long as they all exceed the same floor. -/
theorem IsLowerSuperregularPair.exists_disjoint_matchings (G : Digraph V) (A B : Finset V)
    (ε d : ℝ) (k r : ℕ) (hSize : A.card = B.card) (hr : 0 < r)
    (hCut : (A.card:ℝ)*ε ≤ r) (hBudget : (k:ℝ) < (d-2*ε)*r)
    (hDegrees : ((r+k : ℕ):ℝ) ≤ (d-ε)*(A.card:ℝ))
    (hG : IsLowerSuperregularPair G ε d A B) :
    ∃ M : Fin k → A ≃ B, (∀ j (a : A), G.Adj a (M j a)) ∧
      ∀ i j, i ≠ j → ∀ a, M i a ≠ M j a := by
  obtain ⟨δ,hδ,_,hPair⟩ := hG
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hSize)
  let a : A ↪ V := Function.Embedding.subtype (· ∈ A)
  let b : A ↪ V := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ B))
  have ha : (univ : Finset A).map a = A := by
    ext x
    simp [a]
  have hb : (univ : Finset A).map b = B := by
    ext x
    constructor
    · rintro hx
      obtain ⟨y,_,rfl⟩ := mem_map.mp hx
      exact (e y).prop
    · intro hx
      refine mem_map.mpr ⟨e.symm ⟨x,hx⟩,mem_univ _,?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  let D := pullDirectedPair a b G
  have hPull : IsSuperregularPair D ε δ univ univ :=
    superregular_pullDirectedPair G a b univ univ ε δ (by rwa [ha,hb])
  have ⟨hOut,hIn,hRect⟩ := IsSuperregularPair.physical_lower_bounds D univ univ δ ε hPull
  have hDegree : ((r+k:ℕ):ℝ) ≤ (δ-ε)*(A.card:ℝ) :=
    hDegrees.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hδ _) (Nat.cast_nonneg _))
  have hOut' (x : A) : r+k ≤ outDegree D x := by
    have hx := hOut x (mem_univ _)
    rw [card_univ,Fintype.card_coe] at hx
    exact_mod_cast hDegree.trans hx
  have hIn' (x : A) : r+k ≤ inDegree D x := by
    have hx := hIn x (mem_univ _)
    rw [card_univ,Fintype.card_coe] at hx
    exact_mod_cast hDegree.trans hx
  obtain ⟨M,hM,hDis⟩ := exists_disjoint_matchings_of_rectangle_budget D k r hOut' hIn' (by
    intro X Y hx hy
    have hx' : (r:ℝ) ≤ X.card := by exact_mod_cast hx
    have hy' : (r:ℝ) ≤ Y.card := by exact_mod_cast hy
    have hScale : (((univ : Finset A).card:ℝ)*ε) ≤ r := by
      simpa only [card_univ,Fintype.card_coe] using hCut
    have hLower := hRect X (subset_univ _) Y (subset_univ _) (hScale.trans hx') (hScale.trans hy')
    have hr' : (0:ℝ) < r := by exact_mod_cast hr
    have hPos : 0 < δ-2*ε := by
      by_contra! hn
      have hCost := mul_nonpos_of_nonpos_of_nonneg (show d-2*ε ≤ 0 by linarith only [hδ,hn]) hr'.le
      linarith only [hCost,hBudget,Nat.cast_nonneg (α := ℝ) k]
    have hCost : (k:ℝ) < (δ-2*ε)*(X.card:ℝ) := hBudget.trans_le
      ((mul_le_mul_of_nonneg_right (sub_le_sub_right hδ _) hr'.le).trans
        (mul_le_mul_of_nonneg_left hx' hPos.le))
    have hPay := (mul_lt_mul_of_pos_right hCost (hr'.trans_le hy')).trans_le hLower
    rw [mul_comm (k:ℝ)] at hPay
    exact_mod_cast hPay)
  refine ⟨fun i => (M i).trans e,fun i x => hM i x,?_⟩
  intro i j hij x h
  exact hDis i j hij x (e.injective h)

/-- Once the four physical quarters of each fine cluster satisfy
the pair bounds, select the required banks of disjoint perfect
matchings simultaneously on every arc of the fine successor cycle. -/
theorem exists_universal_walk_quarter_matchings {I : Type*} (G : Digraph V) (s : Equiv.Perm I)
    (Q : I → Fin 4 → Finset V) (m k r : ℕ)
    (ε d : ℝ) (hSize : ∀ i j, (Q i j).card = m) (hr : 0 < r)
    (hCut : (m:ℝ)*ε ≤ r) (hBudget : (k:ℝ) < (d-2*ε)*r)
    (hDegrees : ((r+k : ℕ):ℝ) ≤ (d-ε)*(m:ℝ))
    (hPairs : ∀ i j, IsLowerSuperregularPair G ε d (Q i j) (Q (s i) j)) :
    ∃ M : ∀ i j, Fin k → Q i j ≃ Q (s i) j,
      (∀ i j b (a : Q i j), G.Adj a (M i j b a)) ∧
      ∀ i j b c, b ≠ c → ∀ a, M i j b a ≠ M i j c a := by
  have h : ∀ i j, ∃ M : Fin k → Q i j ≃ Q (s i) j,
      (∀ b (a : Q i j), G.Adj a (M b a)) ∧ ∀ b c, b ≠ c → ∀ a, M b a ≠ M c a := by
    intro i j
    exact IsLowerSuperregularPair.exists_disjoint_matchings G (Q i j) (Q (s i) j)
      ε d k r ((hSize i j).trans (hSize (s i) j).symm) hr
      (by rwa [hSize]) hBudget (by rwa [hSize]) (hPairs i j)
  choose M hM using h
  exact ⟨M,fun i j => (hM i j).1,fun i j => (hM i j).2⟩

end OverfullWork.DirectedRobustExpansion
