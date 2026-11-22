module

public import OverfullWork.CanonicalBipartiteRealization
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section


/-! # Pair prescribed half-edges without pairing equal labels

This is the half-edge form of CMS, Towards the Overfull Conjecture II,
Lemma 3.2. Hall's condition has only two cases: a set has one label,
or two distinct labels already see every right half-edge.
-/
namespace OverfullWork.OffDiagonalStubPairing
open Finset
open scoped Classical
set_option maxHeartbeats 3000000

theorem exists_label_avoiding_equiv
    {A B I : Type*} [Fintype A] [Fintype B] [DecidableEq I]
    (left : A → I) (right : B → I)
    (hcard : Fintype.card A = Fintype.card B)
    (hbound : ∀ i, (univ.filter fun x => left x = i).card +
      (univ.filter fun y => right y = i).card ≤ Fintype.card B) :
    ∃ e : A ≃ B, ∀ x, left x ≠ right (e x) := by
  classical
  let t : A → Finset B := fun x => univ.filter fun y => left x ≠ right y
  have hHall : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨x, hx⟩ := hs
      by_cases hsingle : ∀ z ∈ s, left z = left x
      · have hleft : s.card ≤ (univ.filter fun z => left z = left x).card :=
          card_le_card (by intro z hz; exact mem_filter.mpr ⟨mem_univ _, hsingle z hz⟩)
        have hright : (univ.filter fun y => right y ≠ left x).card ≤
            (s.biUnion t).card := by
          apply card_le_card
          intro y hy
          exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr
            ⟨mem_univ _, ((mem_filter.mp hy).2).symm⟩⟩
        have hsplit : (univ.filter fun y => right y = left x).card +
            (univ.filter fun y => right y ≠ left x).card = Fintype.card B := by
          exact card_filter_add_card_filter_not (s := univ) (fun y => right y = left x)
        have h := hbound (left x)
        omega
      · push Not at hsingle
        obtain ⟨z, hz, hzx⟩ := hsingle
        have hall : s.biUnion t = univ := by
          apply eq_univ_of_forall
          intro y
          by_cases hxy : left x = right y
          · exact mem_biUnion.mpr ⟨z, hz, mem_filter.mpr
              ⟨mem_univ _, fun hzy => hzx (hzy.trans hxy.symm)⟩⟩
          · exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨mem_univ _, hxy⟩⟩
        rw [hall, card_univ, ← hcard]
        exact card_le_univ s
    · have hempty := not_nonempty_iff_eq_empty.mp hs
      simp [hempty]
  obtain ⟨f, hfinj, hf⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  let e := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩)
  exact ⟨e, fun x => (mem_filter.mp (hf x)).2⟩

theorem stub_fiber_card {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℕ) (i : I) :
    (univ.filter fun z : Sigma (fun j => Fin (c j)) => z.1 = i).card = c i := by
  symm
  rw [← Fintype.card_fin (c i), ← card_univ]
  apply card_bij (fun k _ => ⟨i, k⟩)
  · intro k _; simp
  · intro k _ l _ h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · rintro ⟨j, k⟩ hz
    have hji : j = i := (mem_filter.mp hz).2
    subst j
    exact ⟨k, mem_univ _, rfl⟩

/-- A genuine bijection of all half-edge copies, including empty fibres. -/
theorem exists_stub_equiv {I : Type*} [Fintype I] [DecidableEq I]
    (c d : I → ℕ) (hbalance : ∑ i, c i = ∑ i, d i)
    (hbound : ∀ i, c i + d i ≤ ∑ j, c j) :
    ∃ e : (Σ i, Fin (c i)) ≃ (Σ i, Fin (d i)), ∀ z, z.1 ≠ (e z).1 := by
  apply exists_label_avoiding_equiv Sigma.fst Sigma.fst
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using hbalance
  · intro i
    rw [stub_fiber_card, stub_fiber_card]
    simpa only [Fintype.card_sigma, Fintype.card_fin, ← hbalance] using hbound i

/-- The degree-sequence hypothesis is exactly the one printed in Lemma 3.2. -/
theorem exists_stub_equiv_of_complement_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (c d : I → ℕ) (hbalance : ∑ i, c i = ∑ i, d i)
    (hbound : ∀ i, c i + d i ≤ ∑ j ∈ univ.erase i, (c j + d j)) :
    ∃ e : (Σ i, Fin (c i)) ≃ (Σ i, Fin (d i)), ∀ z, z.1 ≠ (e z).1 := by
  apply exists_stub_equiv c d hbalance
  intro i
  have hsum := sum_erase_add (univ : Finset I) (fun j => c j + d j) (mem_univ i)
  have htotal : (∑ j, (c j + d j)) = 2 * ∑ j, c j := by
    rw [sum_add_distrib, ← hbalance]
    omega
  rw [htotal] at hsum
  have h := hbound i
  omega

end OverfullWork.OffDiagonalStubPairing
