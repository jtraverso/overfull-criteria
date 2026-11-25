module

public import OverfullWork.ChenShanAuxiliaryCompletion

@[expose] public section

/-! The balanced selection of cross edges for Chen–Shan, Lemma 3.24. -/
namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- One row of the greedy construction: increment the degrees of `d`
distinct least-loaded columns, preserving a degree spread of at most one. -/
theorem exists_balanced_increment [Nonempty W] (load : W → ℕ) (d : ℕ)
    (hd : d ≤ Fintype.card W) (hBalance : ∀ w z, load w ≤ load z + 1) :
    ∃ S : Finset W, S.card = d ∧ ∀ w z,
      load w + (if w ∈ S then 1 else 0) ≤ load z + (if z ∈ S then 1 else 0) + 1 := by
  obtain ⟨w₀, _, hMin⟩ := (univ : Finset W).exists_min_image load univ_nonempty
  let b := load w₀
  let low := (univ : Finset W).filter (fun w => load w = b)
  have hLower (w : W) : b ≤ load w := hMin w (mem_univ _)
  have hUpper (w : W) : load w ≤ b + 1 := hBalance w w₀
  have hLow (w : W) : w ∈ low ↔ load w = b := by simp [low]
  have hHigh (w : W) (hw : w ∉ low) : load w = b + 1 := by
    have hne : load w ≠ b := fun he => hw ((hLow w).mpr he)
    exact le_antisymm (hUpper w) (Nat.succ_le_of_lt (lt_of_le_of_ne (hLower w) hne.symm))
  by_cases h : d ≤ low.card
  · obtain ⟨S, hS, hCard⟩ := exists_subset_card_eq h
    have hBetween (w : W) : b ≤ load w + (if w ∈ S then 1 else 0) ∧
        load w + (if w ∈ S then 1 else 0) ≤ b + 1 := by
      by_cases hw : w ∈ S
      · simp only [ite_eq_left hw, (hLow w).mp (hS hw)]
        omega
      · simpa only [ite_eq_right hw, add_zero] using ⟨hLower w, hUpper w⟩
    exact ⟨S, hCard, fun w z => by have h₁ := (hBetween w).2; have h₂ := (hBetween z).1; omega⟩
  · have hAvail : d - low.card ≤ lowᶜ.card := by
      rw [card_compl]
      omega
    obtain ⟨T, hT, hCard⟩ := exists_subset_card_eq hAvail
    let S := low ∪ T
    have hDj : Disjoint low T := Disjoint.mono_right hT disjoint_compl_right
    have hSize : S.card = d := by
      dsimp only [S]
      rw [card_union_of_disjoint hDj, hCard]
      omega
    have hBetween (w : W) : b + 1 ≤ load w + (if w ∈ S then 1 else 0) ∧
        load w + (if w ∈ S then 1 else 0) ≤ b + 2 := by
      by_cases hw : w ∈ low
      · have hwS : w ∈ S := mem_union_left _ hw
        simp only [ite_eq_left hwS, (hLow w).mp hw]
        omega
      · rw [hHigh w hw]
        split <;> omega
    exact ⟨S, hSize, fun w z => by have h₁ := (hBetween w).2; have h₂ := (hBetween z).1; omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assign distinct neighbors to the vertices of deficit one, then process
the remaining vertices one at a time. Each row is a set, and no
auxiliary vertex receives two neighbors of deficit one. -/
theorem exists_balanced_auxiliary_neighbours [Nonempty W] (d : V → ℕ)
    (hDegree : ∀ v, d v ≤ Fintype.card W)
    (hOnes : ((univ : Finset V).filter (fun v => d v = 1)).card ≤ Fintype.card W) :
    ∃ f : V → Finset W, (∀ v, (f v).card = d v) ∧
      (∀ w z : W, ((univ : Finset V).filter (fun v => w ∈ f v)).card ≤
        ((univ : Finset V).filter (fun v => z ∈ f v)).card + 1) ∧
      ∀ w : W, (((univ : Finset V).filter (fun v => d v = 1)).filter (fun v => w ∈ f v)).card ≤ 1 := by
  let ones := (univ : Finset V).filter (fun v => d v = 1)
  let N (f : V → Finset W) (w : W) := (univ : Finset V).filter (fun v => w ∈ f v)
  let D (f : V → Finset W) (w : W) := ones.filter (fun v => w ∈ f v)
  have hOnes' : Fintype.card ↥ones ≤ Fintype.card W := by simpa only [Fintype.card_coe] using hOnes
  let e : ↥ones ↪ W := (Fintype.equivFin ↥ones).toEmbedding.trans
    ((Fin.castLEEmb hOnes').trans (Fintype.equivFin W).symm.toEmbedding)
  have hBuild (R : Finset V) (hR : Disjoint R ones) :
      ∃ f : V → Finset W, (∀ v, (f v).card = if v ∈ ones ∪ R then d v else 0) ∧
        (∀ w z : W, (N f w).card ≤ (N f z).card + 1) ∧
        ∀ w : W, (D f w).card ≤ 1 := by
    induction R using Finset.induction_on with
    | empty =>
      let f (v : V) : Finset W := if hv : v ∈ ones then {e ⟨v, hv⟩} else ∅
      have hEq (v : V) (hv : v ∈ ones) : f v = {e ⟨v, hv⟩} := dite_eq_left hv
      have hPoint (v : V) (hv : v ∈ ones) : d v = 1 := (mem_filter.mp hv).2
      have hBound (w : W) : (N f w).card ≤ 1 := by
        apply card_le_one.mpr
        intro u hu v hv
        have hu' : w ∈ f u := (mem_filter.mp hu).2
        have hv' : w ∈ f v := (mem_filter.mp hv).2
        by_cases huOne : u ∈ ones
        · by_cases hvOne : v ∈ ones
          · rw [hEq u huOne, mem_singleton] at hu'
            rw [hEq v hvOne, mem_singleton] at hv'
            exact congrArg Subtype.val (e.injective (hu'.symm.trans hv'))
          · simp [f, hvOne] at hv'
        · simp [f, huOne] at hu'
      refine ⟨f, ?_, ?_, ?_⟩
      · intro v
        by_cases hv : v ∈ ones
        · simp [hEq v hv, hv, hPoint v hv]
        · simp [f, hv]
      · intro w z
        have h := hBound w
        omega
      · intro w
        exact (card_le_card (show D f w ⊆ N f w from fun v hv =>
          mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩)).trans (hBound w)
    | @insert v R hv ih =>
      have hR' : Disjoint R ones := Disjoint.mono_left (subset_insert v R) hR
      have hvOne : v ∉ ones := fun h => Finset.disjoint_left.mp hR (mem_insert_self _ _) h
      obtain ⟨f, hRows, hBalanced, hDistinct⟩ := ih hR'
      obtain ⟨S, hSize, hNext⟩ := exists_balanced_increment (fun w => (N f w).card)
        (d v) (hDegree v) hBalanced
      let g := Function.update f v S
      have hEmpty : f v = ∅ := by
        apply card_eq_zero.mp
        simpa only [mem_union, hvOne, hv, or_self, ite_false] using hRows v
      have hUpdate (w : W) : (N g w).card = (N f w).card + if w ∈ S then 1 else 0 := by
        have hOld : v ∉ N f w := by simp [N, hEmpty]
        have updateSet : N g w = if w ∈ S then insert v (N f w) else N f w := by
          ext u
          by_cases hu : u = v
          · subst u
            by_cases hw : w ∈ S <;> simp [N, g, hw, hOld]
          · by_cases hw : w ∈ S <;> simp [N, g, hw, hu]
        rw [updateSet]
        by_cases hw : w ∈ S
        · simp [hw, card_insert_of_notMem hOld]
        · simp [hw]
      refine ⟨g, ?_, ?_, ?_⟩
      · intro u
        by_cases hu : u = v
        · subst u
          simp [g, hSize]
        · rw [show g u = f u from Function.update_of_ne hu _ _, hRows]
          simp only [mem_union, mem_insert, hu, false_or]
      · intro w z
        rw [hUpdate w, hUpdate z]
        exact hNext w z
      · intro w
        have hEq : D g w = D f w := by
          apply filter_congr
          intro u hu
          have hne : u ≠ v := fun he => hvOne (he ▸ hu)
          rw [show g u = f u from Function.update_of_ne hne _ _]
        rw [hEq]
        exact hDistinct w
  obtain ⟨f, hRows, hBalanced, hDistinct⟩ := hBuild ((univ : Finset V) \ ones)
    (Finset.disjoint_left.mpr fun _ h₁ h₂ => (mem_sdiff.mp h₁).2 h₂)
  refine ⟨f, ?_, hBalanced, hDistinct⟩
  intro v
  have hAll : v ∈ ones ∪ ((univ : Finset V) \ ones) := by simp
  simpa only [ite_eq_left hAll] using hRows v

omit [DecidableEq V] in
/-- Balanced auxiliary degrees are at most the ceiling of the mean.
The hypothesis on `b` is the multiplicative form of that ceiling. -/
theorem auxiliary_degree_le_of_balance (f : V → Finset W) (d : V → ℕ) (b : ℕ)
    (hRows : ∀ v, (f v).card = d v)
    (hBalanced : ∀ w z : W, ((univ : Finset V).filter (fun v => w ∈ f v)).card ≤
      ((univ : Finset V).filter (fun v => z ∈ f v)).card + 1)
    (hBudget : (∑ v : V, d v) ≤ b * Fintype.card W) (w : W) :
    ((univ : Finset V).filter (fun v => w ∈ f v)).card ≤ b := by
  let c (w : W) := ((univ : Finset V).filter (fun v => w ∈ f v)).card
  have hSum : (∑ z : W, c z) = ∑ v : V, d v := by
    unfold c
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [← card_filter, show ((univ : Finset W).filter (fun z => z ∈ f v)) = f v by ext z; simp]
    exact hRows v
  change c w ≤ b
  by_contra! h
  have hFloor (z : W) : b ≤ c z := by
    have h' : c w ≤ c z + 1 := hBalanced w z
    omega
  have hStrict : (∑ _ : W, b) < ∑ z : W, c z :=
    sum_lt_sum (fun z _ => hFloor z) ⟨w, mem_univ _, h⟩
  rw [hSum] at hStrict
  have hB : (∑ _ : W, b) = b * Fintype.card W := by simp [Nat.mul_comm]
  rw [hB] at hStrict
  exact (not_lt_of_ge hBudget) hStrict

/-- The assigned edges form a simple bipartite graph. -/
def auxiliaryCrossGraph (f : V → Finset W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl v, .inr w => w ∈ f v
    | .inr w, .inl v => w ∈ f v
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

omit [DecidableEq V] [DecidableEq W] in
theorem auxiliaryCrossGraph_degree_left (f : V → Finset W) (v : V) :
    (auxiliaryCrossGraph f).degree (.inl v) = (f v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (auxiliaryCrossGraph f).neighborFinset (.inl v) = (f v).map Function.Embedding.inr := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x
    · simp [auxiliaryCrossGraph, mem_map]
    · simp [auxiliaryCrossGraph, mem_map]
  rw [h, card_map]

omit [DecidableEq V] in
theorem auxiliaryCrossGraph_degree_right (f : V → Finset W) (w : W) :
    (auxiliaryCrossGraph f).degree (.inr w) =
      ((univ : Finset V).filter (fun v => w ∈ f v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (auxiliaryCrossGraph f).neighborFinset (.inr w) =
      ((univ : Finset V).filter (fun v => w ∈ f v)).map Function.Embedding.inl := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x
    · simp [auxiliaryCrossGraph, mem_map]
    · simp [auxiliaryCrossGraph, mem_map]
  rw [h, card_map]

/-- The cross graph required in Lemma 3.24, with one edge per neighbor,
balanced auxiliary degrees, and at most one deficit-one neighbor per
auxiliary vertex. -/
theorem exists_balanced_auxiliary_crossGraph [Nonempty W] (d : V → ℕ) (b : ℕ)
    (hDegree : ∀ v, d v ≤ Fintype.card W)
    (hOnes : ((univ : Finset V).filter (fun v => d v = 1)).card ≤ Fintype.card W)
    (hBudget : (∑ v : V, d v) ≤ b * Fintype.card W) :
    ∃ F : SimpleGraph (V ⊕ W),
      (∀ v v', ¬ F.Adj (.inl v) (.inl v')) ∧ (∀ w w', ¬ F.Adj (.inr w) (.inr w')) ∧
      (∀ v : V, F.degree (.inl v) = d v) ∧
      (∀ w z : W, F.degree (.inr w) ≤ F.degree (.inr z) + 1) ∧
      (∀ w : W, F.degree (.inr w) ≤ b) ∧
      ∀ w : W, ((univ : Finset V).filter (fun v => d v = 1 ∧ F.Adj (.inl v) (.inr w))).card ≤ 1 := by
  obtain ⟨f, hRows, hBalance, hOne⟩ := exists_balanced_auxiliary_neighbours d hDegree hOnes
  refine ⟨auxiliaryCrossGraph f, fun _ _ h => h, fun _ _ h => h, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [auxiliaryCrossGraph_degree_left, hRows]
  · intro w z
    rw [auxiliaryCrossGraph_degree_right, auxiliaryCrossGraph_degree_right]
    exact hBalance w z
  · intro w
    rw [auxiliaryCrossGraph_degree_right]
    exact auxiliary_degree_le_of_balance f d b hRows hBalance hBudget w
  · intro w
    have h : ((univ : Finset V).filter (fun v => d v = 1 ∧
        (auxiliaryCrossGraph f).Adj (.inl v) (.inr w))) =
        ((univ : Finset V).filter (fun v => d v = 1)).filter (fun v => w ∈ f v) := by
      ext v
      simp [auxiliaryCrossGraph, and_comm]
    rw [h]
    exact hOne w

end OverfullWork.ChenShan
