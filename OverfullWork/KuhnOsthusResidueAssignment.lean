module

public import OverfullWork.KuhnOsthusExceptionalAssignmentCells
public import OverfullWork.KuhnOsthusPathPartition

@[expose] public section


/-! The interval geometry used to apply Lemma 9.6 in the proof of
Lemma 9.7. The smaller intervals have a coarse owner on the cycle;
their terminal vertices may lie in the next interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V S : Type*} [Fintype V]

/-- The vertices incident to a matching are supported on its two
coarse intervals. -/
theorem OrderedResidueMatchings.incident_support {H : Digraph V} {g n c m h : ℕ} [NeZero g]
    {coarse : V → Fin g} (P : OrderedResidueMatchings H coarse n c m h) (i : Fin n)
    {v : V} (hv : IncidentTo (P.matching i) v) : coarse v ∈ (P.doubleType i).val := by
  rcases hv with ⟨w,hw⟩ | ⟨w,hw⟩
  · exact (P.endpoints _ _ _ hw).1
  · exact (P.endpoints _ _ _ hw).2

/-- Each matching meets at most four coarse fibers' worth of closed
intervals. Each closed interval meets matchings from at most twice
the number of types through one coarse label. -/
theorem residue_interval_incidence_bounds {H : Digraph V} {g n c m h f : ℕ} [NeZero g]
    {coarse : V → Fin g} (P : OrderedResidueMatchings H coarse n c m h)
    (s : Equiv.Perm (Fin f)) (A : Fin f → Finset V) (owner : Fin f → Fin g) (u : ℕ)
    (hOwner : ∀ i v, v ∈ A i → coarse v = owner i)
    (hFiber : ∀ a, (finiteSatisfying (fun j => owner j = a)).card ≤ u) :
    let F (i : Fin n) := finiteSatisfying (IncidentTo (P.matching i))
    (∀ i, (finiteSatisfying (fun j => ¬ Disjoint (F i) (A j ∪ A (s j)))).card ≤ 4*u) ∧
    ∀ j, (finiteSatisfying (fun i => ¬ Disjoint (F i) (A j ∪ A (s j)))).card ≤ 2*g*c := by
  intro F
  have hTouch {i : Fin n} {j : Fin f} {v : V} (hv : v ∈ F i) (ha : v ∈ A j) :
      owner j ∈ (P.doubleType i).val := by
    rw [←hOwner j v ha]
    exact P.incident_support i ((mem_finiteSatisfying (p := IncidentTo (P.matching i))).mp hv)
  constructor
  · intro i
    let K := (P.doubleType i).val
    let B := K.biUnion (fun a => finiteSatisfying (fun j => owner j = a))
    have hK : K.card = 2 := (mem_powersetCard.mp (P.doubleType i).prop).2
    have hB : B.card ≤ 2*u :=
      card_biUnion_le.trans (by
        calc
          _ ≤ ∑ _ ∈ K,u := sum_le_sum (fun a _ => hFiber a)
          _ = 2*u := by simp only [sum_const,hK,nsmul_eq_mul,Nat.cast_id])
    have hHit (j : Fin f) (ht : owner j ∈ (P.doubleType i).val) : j ∈ B :=
      mem_biUnion.mpr ⟨_,ht,mem_finiteSatisfying.mpr rfl⟩
    calc
      _ ≤ (B ∪ B.image s.symm).card := by
        apply card_le_card
        intro j hj
        have hNo : ¬ Disjoint (F i) (A j ∪ A (s j)) :=
          (mem_finiteSatisfying (p := fun j => ¬ Disjoint (F i) (A j ∪ A (s j)))).mp hj
        obtain ⟨v,hv,ha⟩ := not_disjoint_iff.mp hNo
        rcases mem_union.mp ha with ha | ha
        · exact mem_union_left _ (hHit j (hTouch hv ha))
        · exact mem_union_right _ (mem_image.mpr ⟨s j,hHit (s j) (hTouch hv ha),s.symm_apply_apply j⟩)
      _ ≤ B.card+(B.image s.symm).card := card_union_le _ _
      _ ≤ 4*u := by
        have hIm := card_image_le (s := B) (f := s.symm)
        omega
  · intro j
    let T (a : Fin g) := finiteSatisfying (fun t : ResidueDoubleType g => a ∈ t.val)
    let M (t : ResidueDoubleType g) := finiteSatisfying (fun i => P.doubleType i = t)
    let B (a : Fin g) := (T a).biUnion M
    have hT (a : Fin g) : (T a).card ≤ g := by
      have he : T a = (univ : Finset (ResidueDoubleType g)).filter (fun t => a ∈ t.val) := by
        ext t
        simp [T]
      rw [he]
      exact card_double_types_through a
    have hM (t : ResidueDoubleType g) : (M t).card = c := by
      have he : M t = (univ : Finset (Fin n)).filter (fun i => P.doubleType i = t) := by
        ext i
        simp [M]
      rw [he]
      exact P.typeCount t
    have hB (a : Fin g) : (B a).card ≤ g*c := card_biUnion_le.trans (by
      simp only [hM,sum_const,nsmul_eq_mul,Nat.cast_id]
      exact Nat.mul_le_mul_right _ (hT a))
    have hHit (i : Fin n) (a : Fin g) (ht : a ∈ (P.doubleType i).val) : i ∈ B a :=
      mem_biUnion.mpr ⟨P.doubleType i,mem_finiteSatisfying.mpr ht,mem_finiteSatisfying.mpr rfl⟩
    calc
      _ ≤ (B (owner j) ∪ B (owner (s j))).card := by
        apply card_le_card
        intro i hi
        have hNo : ¬ Disjoint (F i) (A j ∪ A (s j)) :=
          (mem_finiteSatisfying (p := fun i => ¬ Disjoint (F i) (A j ∪ A (s j)))).mp hi
        obtain ⟨v,hv,ha⟩ := not_disjoint_iff.mp hNo
        rcases mem_union.mp ha with ha | ha
        · exact mem_union_left _ (hHit i _ (hTouch hv ha))
        · exact mem_union_right _ (hHit i _ (hTouch hv ha))
      _ ≤ (B (owner j)).card + (B (owner (s j))).card := card_union_le _ _
      _ ≤ 2*g*c := by rw [Nat.mul_assoc,two_mul]; exact Nat.add_le_add (hB _) (hB _)

/-- The ordered matchings from Lemma 8.7 satisfy the hypotheses of
Lemma 9.6 when fitted to the finer interval cells of Lemma 9.7.
Only the normalized ownership, size and disjointness margins are
needed for this assignment. -/
theorem assign_exceptional_systems_to_ordered_residue {H : Digraph V} {g n c m f t : ℕ}
    [NeZero g] [NeZero n] [Fintype S] {coarse : V → Fin g}
    (P : OrderedResidueMatchings H coarse n c m 10)
    (s : Equiv.Perm (Fin f)) (A : Fin f → Finset V) (owner : Fin f → Fin g)
    (cell : Fin f × S → Finset V) (Q : Fin f × (S × Fin t) → Finset V)
    (index : Fin n ≃ Fin f × (S × Fin t)) (u : ℕ)
    (hn : 200 ≤ n) (hCount : n = c*g.choose 2)
    (hCoarse : 200*g ≤ g.choose 2) (hFine : 400*u ≤ f) (ht : 300*t ≤ n)
    (hOwner : ∀ i v, v ∈ A i → coarse v = owner i)
    (hFiber : ∀ a, (finiteSatisfying (fun j => owner j = a)).card ≤ u)
    (hCellSub : ∀ e, cell e ⊆ A e.1)
    (hCell : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hQ : ∀ e, Q e ⊆ cell (e.1,e.2.1) ∪ cell (s e.1,e.2.1)) :
    let F (i : Fin n) := finiteSatisfying (IncidentTo (P.matching i))
    ∃ assign : Fin n ≃ Fin f × (S × Fin t), (∀ i, Disjoint (F i) (Q (assign i))) ∧
      ∀ i j, residueCyclicClose 10 i j →
        Disjoint (F i ∪ Q (assign i)) (F j ∪ Q (assign j)) := by
  intro F
  have hApart (i j : Fin n) (hij : residueCyclicClose 10 i j) : Disjoint (F i) (F j) := by
    rw [disjoint_left]
    intro v hi hj
    have hTake (k : Fin n) (hk : v ∈ F k) : coarse v ∈ residueTypeClosure (P.doubleType k) :=
      subset_residue_type_closure _ (P.incident_support k
        ((mem_finiteSatisfying (p := IncidentTo (P.matching k))).mp hk))
    exact disjoint_left.mp (P.separated i j hij) (hTake i hi) (hTake j hj)
  obtain ⟨hRow,hCol⟩ := residue_interval_incidence_bounds P s A owner u hOwner hFiber
  apply kuhn_osthus_lemma_9_6_of_interval_cells s F A cell Q index (4*u) (2*g*c) hn
    _ _ ht hApart hCellSub hCell hQ hRow hCol
  · simpa only [←Nat.mul_assoc,Nat.reduceMul] using hFine
  · rw [←Nat.mul_assoc,←Nat.mul_assoc,hCount,Nat.mul_comm c]
    exact Nat.mul_le_mul_right c hCoarse

end OverfullWork.DirectedRobustExpansion
