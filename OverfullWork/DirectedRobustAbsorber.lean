module

public import OverfullWork.DirectedAbsorberAssembly
public import OverfullWork.DirectedCoveringPairs
public import OverfullWork.DirectedDisjointLadders

@[expose] public section


/-! A finite-budget version of Lo–Patel Theorem 4.11. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset DirectedRobustExpansion DirectedCoveringPairs
open scoped Classical
variable {V : Type*} [Fintype V] [Nonempty V]
set_option maxHeartbeats 4000000

/-- Construct a small absorbing cycle from robust out-expansion and
minimum semidegree, under explicit numerical budgets for the cover,
the ladders and the connectors. -/
theorem exists_robust_absorbing_cycle (D : Digraph V) {m d g r s t r' L P B : ℕ} (δ : ℝ)
    (hm : 0 < m) (hg : 2 ≤ g) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hDensity : δ*(Fintype.card V:ℝ)^2 ≤ (g:ℝ)*(g-1))
    (hCoverIn : ∀ v, 2*m+g ≤ inDegree D v) (hCoverOut : ∀ v, 2*m+g ≤ outDegree D v)
    (hSmall : (Fintype.card V:ℝ)^2*(1-δ/2)^m < (1/2:ℝ)^d)
    (hs : 0 < s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hRevBudget : s*Fintype.card V ≤ r*(r-s))
    (hIn : ∀ v, 2*t+s ≤ inDegree D v) (hOut : ∀ v, 2*t+s ≤ outDegree D v)
    (hRobust : IsRobustAt D r t) (hr' : 0 < r') (hL : Fintype.card V/r'+4 ≤ L)
    (hP : Fintype.card V/s+8 ≤ P) (hB : P+P/4*L ≤ B)
    (hSpine : 2*m+m*B+P ≤ s)
    (hLadders : 2*m+m*B+B+r' ≤ r)
    (hConnect : m*B+m*(P/4+1)*L+r' ≤ r)
    (hOutLadders : ∀ v, t+2*m+m*B+B ≤ outDegree D v)
    (hOutConnect : ∀ v, t+m*B+m*(P/4+1)*L ≤ outDegree D v) :
    ∃ C : AbsorbingCycle D d, C.vertices.length ≤ m*B+m*(P/4+1)*L := by
  classical
  obtain ⟨S, hSize, hDisj, hCov⟩ :=
    exists_disjoint_cover D m d g δ hg hδ hδ' hDensity hCoverIn hCoverOut hSmall
  let J := {p : V × V // p ∈ S}
  let _ : Nonempty J :=
    ⟨⟨(card_pos.mp (hSize.symm ▸ hm)).choose, (card_pos.mp (hSize.symm ▸ hm)).choose_spec⟩⟩
  have hJ : Fintype.card J = m := (Fintype.card_coe S).trans hSize
  let x : J → V := fun p => p.val.1
  let y : J → V := fun p => p.val.2
  have hPair : ∀ p q : J, p ≠ q →
      x p ≠ x q ∧ x p ≠ y q ∧ y p ≠ x q ∧ y p ≠ y q :=
    fun p q hn => hDisj.2 p.prop q.prop (fun he => hn (Subtype.ext he))
  have hx : Function.Injective x := by
    intro p q he
    by_contra hn
    exact (hPair p q hn).1 he
  have hy : Function.Injective y := by
    intro p q he
    by_contra hn
    exact (hPair p q hn).2.2.2 he
  have hxy : ∀ p q, x p ≠ y q := by
    intro p q
    by_cases h : p = q
    · subst q
      exact hDisj.1 p.val p.prop
    · exact (hPair p q h).2.1
  have hUsed : (used S).card ≤ 2*m :=
    (card_union_le _ _).trans (by
      have he : (S.image Prod.fst).card+(S.image Prod.snd).card ≤ S.card+S.card :=
        Nat.add_le_add card_image_le card_image_le
      rwa [hSize, ← two_mul] at he)
  have hMarks : ∀ p, x p ∈ used S ∧ y p ∈ used S := fun p =>
    ⟨mem_union_left _ (mem_image_of_mem _ p.prop), mem_union_right _ (mem_image_of_mem _ p.prop)⟩
  obtain ⟨F, hF, hFDisj⟩ :=
    exists_disjoint_ladders D hs hsr hrt hRevBudget hIn hOut hRobust hr' hL hP hB
      (used S) x y hx hy hxy hMarks univ ∅ (by simp)
      (by simp only [card_empty, zero_add, card_univ, hJ]; omega)
      (by simp only [card_empty, zero_add, card_univ, hJ]; omega)
      (fun v => by simp only [card_empty, add_zero, card_univ, hJ]; have := hOutLadders v; omega)
  choose q A hEq hPq hBq _ _ using fun j => hF j (mem_univ j)
  have hDisjoint : ∀ j k, j ≠ k → Disjoint (A j).vertices (A k).vertices :=
    fun j k h => hFDisj j (mem_univ _) k (mem_univ _) h _ _ (hEq j) (hEq k)
  let M := (univ : Finset J).biUnion (fun j => (A j).vertices)
  have hM : ∀ j, (A j).vertices ⊆ M := fun j => subset_biUnion_of_mem (fun j : J => (A j).vertices) (mem_univ j)
  have hMCard : M.card ≤ m*B := by
    apply card_biUnion_le.trans
    simpa [hJ] using
      (sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hBq j) :
        (∑ j : J, (A j).vertices.card) ≤ ∑ _j : J, B)
  have hQ : (∑ j : J, (q j+1)) ≤ m*(P/4+1) := by
    have hEach : ∀ j, q j+1 ≤ P/4+1 := by intro j; have := hPq j; omega
    simpa [hJ] using
      (sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hEach j) :
        (∑ j : J, (q j+1)) ≤ ∑ _j : J, (P/4+1))
  have hPaid := Nat.add_le_add hMCard (Nat.mul_le_mul_right L hQ)
  have hCover : ∀ u v, d ≤ (covering D x y u v).card := by
    intro u v
    let e : J ↪ (V × V) := ⟨Subtype.val, Subtype.val_injective⟩
    have he : (covering D x y u v).map e = S.filter (fun p => Covers D p (u,v)) := by
      ext p
      constructor
      · intro hp
        obtain ⟨j, hj, rfl⟩ := mem_map.mp hp
        exact mem_filter.mpr ⟨j.prop, (mem_filter.mp hj).2⟩
      · intro hp
        obtain ⟨hS, hEdge⟩ := mem_filter.mp hp
        exact mem_map.mpr ⟨⟨p,hS⟩, mem_filter.mpr ⟨mem_univ _, hEdge⟩, rfl⟩
    rw [← card_map e, he]
    exact hCov (u,v)
  obtain ⟨C, hC⟩ := exists_absorbing_cycle_of_ladders D hRobust hr' hL x y q A
    hDisjoint hCover M hM (by omega) (fun v => by have := hIn v; omega)
    (fun v => by have := hOutConnect v; omega)
  exact ⟨C, hC.trans hPaid⟩

end OverfullWork.DirectedAbsorbingLadder
