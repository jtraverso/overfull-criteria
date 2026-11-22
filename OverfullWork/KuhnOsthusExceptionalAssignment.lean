module

public import OverfullWork.KuhnOsthusCompatibleOrdering
public import OverfullWork.KuhnOsthusOrderedResidue

@[expose] public section


/-! Kühn–Osthus Lemma 9.6 on the ordinary vertices of the basic
digraph. The two incidence bounds concern entire interval supports.
The conflict bound concerns complete exceptional path systems. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V A : Type*} [Fintype A]

private def nearby {n : ℕ} (h : ℕ) (i j : Fin n) : Prop :=
  i = j ∨ residueCyclicClose h i j

private theorem nearby_symm {n h : ℕ} {i j : Fin n} (he : nearby h i j) : nearby h j i :=
  he.elim (fun hh => Or.inl hh.symm) (fun hh => Or.inr (residueCyclicClose_symm hh))

private theorem card_cyclic_nearby {n : ℕ} [NeZero n] (h : ℕ) (i : Fin n) :
    (finiteSatisfying (nearby h i)).card ≤ 2*h+1 := by
  have hSet : finiteSatisfying (nearby h i) =
      insert i ((univ : Finset (Fin n)).filter (residueCyclicClose h i)) := by
    ext j
    simp only [mem_finiteSatisfying,nearby,mem_insert,mem_filter,mem_univ,true_and,eq_comm (a := i)]
  rw [hSet]
  exact (card_insert_le _ _).trans (Nat.add_le_add_right (card_residue_cyclic_neighborhood h i) 1)

/-- Assign the complete exceptional path systems to the ordered
matchings. Each label over an interval belongs to a common finite
set of copies, so the two estimates for bad intervals convert to
bounds on the two sides of the auxiliary bipartite graph. -/
theorem exists_spaced_exceptional_assignment {n f : ℕ} [NeZero n]
    (H : Fin n → Finset V) (C : Fin f → Finset V) (Q : Fin f × A → Finset V)
    (index : Fin n ≃ Fin f × A) (h a b c : ℕ)
    (hH : ∀ i j, residueCyclicClose h i j → Disjoint (H i) (H j))
    (hSupport : ∀ e, Q e ⊆ C e.1)
    (hRow : ∀ i, (finiteSatisfying (fun j => ¬ Disjoint (H i) (C j))).card ≤ a)
    (hCol : ∀ j, (finiteSatisfying (fun i => ¬ Disjoint (H i) (C j))).card ≤ b)
    (hConflict : ∀ e, (finiteSatisfying (fun e' => ¬ Disjoint (Q e) (Q e'))).card ≤ c)
    (hSize : 2*(2*h)*c+2*h+1+(2*h+1)*(a*Fintype.card A)+(2*h+1)*b < n) :
    ∃ assign : Fin n ≃ Fin f × A, (∀ i, Disjoint (H i) (Q (assign i))) ∧
      ∀ i j, residueCyclicClose h i j →
        Disjoint (H i ∪ Q (assign i)) (H j ∪ Q (assign j)) := by
  let bad (i : Fin n) (e : Fin f × A) :=
    ∃ j, nearby h i j ∧ ¬ Disjoint (H j) (C e.1)
  have hBadRow (i : Fin n) : (finiteSatisfying (bad i)).card ≤ (2*h+1)*(a*Fintype.card A) := by
    let S := finiteSatisfying (nearby h i)
    let B (j : Fin n) :=
      (finiteSatisfying (fun k => ¬ Disjoint (H j) (C k))) ×ˢ (univ : Finset A)
    calc
      _ ≤ (S.biUnion B).card := by
        apply card_le_card
        intro e he
        obtain ⟨j,hj,hNo⟩ := (mem_finiteSatisfying (p := bad i)).mp he
        exact mem_biUnion.mpr ⟨j,mem_finiteSatisfying.mpr hj,
          mem_product.mpr ⟨mem_finiteSatisfying.mpr hNo,mem_univ _⟩⟩
      _ ≤ ∑ j ∈ S,(B j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ S,a*Fintype.card A := by
        apply sum_le_sum
        intro j _
        dsimp only [B]
        rw [card_product,card_univ]
        exact Nat.mul_le_mul_right _ (hRow j)
      _ = S.card*(a*Fintype.card A) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (card_cyclic_nearby h i)
  have hBadCol (e : Fin f × A) :
      (finiteSatisfying (fun i => bad i e)).card ≤ (2*h+1)*b := by
    let S := finiteSatisfying (fun j => ¬ Disjoint (H j) (C e.1))
    let B (j : Fin n) := finiteSatisfying (nearby h j)
    calc
      _ ≤ (S.biUnion B).card := by
        apply card_le_card
        intro i hi
        obtain ⟨j,hj,hNo⟩ := (mem_finiteSatisfying (p := fun i => bad i e)).mp hi
        exact mem_biUnion.mpr ⟨j,mem_finiteSatisfying.mpr hNo,mem_finiteSatisfying.mpr (nearby_symm hj)⟩
      _ ≤ ∑ j ∈ S,(B j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ S,(2*h+1) := sum_le_sum (fun j _ => card_cyclic_nearby h j)
      _ = (2*h+1)*S.card := by simp [Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (hCol e.1)
  obtain ⟨assign,hAllowed,hApart⟩ := exists_compatible_ordering (residueCyclicClose h)
    (fun e e' => ¬ Disjoint (Q e) (Q e')) bad index residueCyclicClose_symm
    (fun hn hd => hn hd.symm) (fun _ hh => hh.1 rfl) (2*h) c
    ((2*h+1)*(a*Fintype.card A)) ((2*h+1)*b)
    (by intro i; exact card_residue_cyclic_neighborhood h i) hConflict hBadRow hBadCol
    (by simpa only [Fintype.card_fin] using hSize)
  have hCross (i j : Fin n) (hc : nearby h i j) : Disjoint (H j) (Q (assign i)) := by
    have hDis : Disjoint (H j) (C (assign i).1) := by
      by_contra hh
      exact hAllowed i ⟨j,hc,hh⟩
    exact hDis.mono_right (hSupport _)
  refine ⟨assign,fun i => hCross i i (Or.inl rfl),?_⟩
  intro i j hj
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hH i j hj,hCross j i
    (Or.inr (residueCyclicClose_symm hj))⟩,disjoint_union_right.mpr
      ⟨(hCross i j (Or.inr hj)).symm,not_not.mp (hApart i j hj)⟩⟩

/-- When there are at most one hundredth as many bad intervals,
bad positions and conflicts as the corresponding totals, the
exchange works for cyclic distance ten. -/
theorem kuhn_osthus_lemma_9_6 {n f : ℕ} [NeZero n]
    (H : Fin n → Finset V) (C : Fin f → Finset V) (Q : Fin f × A → Finset V)
    (index : Fin n ≃ Fin f × A) (a b c : ℕ) (hn : 200 ≤ n)
    (ha : 100*a ≤ f) (hb : 100*b ≤ n) (hc : 100*c ≤ n)
    (hH : ∀ i j, residueCyclicClose 10 i j → Disjoint (H i) (H j))
    (hSupport : ∀ e, Q e ⊆ C e.1)
    (hRow : ∀ i, (finiteSatisfying (fun j => ¬ Disjoint (H i) (C j))).card ≤ a)
    (hCol : ∀ j, (finiteSatisfying (fun i => ¬ Disjoint (H i) (C j))).card ≤ b)
    (hConflict : ∀ e, (finiteSatisfying (fun e' => ¬ Disjoint (Q e) (Q e'))).card ≤ c) :
    ∃ assign : Fin n ≃ Fin f × A, (∀ i, Disjoint (H i) (Q (assign i))) ∧
      ∀ i j, residueCyclicClose 10 i j →
        Disjoint (H i ∪ Q (assign i)) (H j ∪ Q (assign j)) := by
  have hN : n = f*Fintype.card A := by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr index
  have hPay : 100*(a*Fintype.card A) ≤ n := by
    rw [←Nat.mul_assoc,hN]
    exact Nat.mul_le_mul_right _ ha
  apply exists_spaced_exceptional_assignment H C Q index 10 a b c hH hSupport hRow hCol hConflict
  norm_num
  omega

end OverfullWork.DirectedRobustExpansion
