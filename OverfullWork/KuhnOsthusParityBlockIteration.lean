module

public import OverfullWork.KuhnOsthusLemma103

@[expose] public section


/-! Iterate the six-permutation deletion budget in Lemma 10.5.
Each block owns its prescribed original exceptional arcs, which
are reserved outside the shared ordinary routing graph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V Z : Type*}

/-- Iterate a parity block construction valid below the stated
budget on earlier blocks. In round i, their ordinary arcs are
covered by at most 6*i matchings. -/
theorem exists_iterated_parity_blocks (R : Digraph V) {n : ℕ}
    (E : Fin n → Digraph (V ⊕ Z)) (valid : Fin n → Digraph (V ⊕ Z) → Prop)
    (hApart : Pairwise fun i j => Disjoint (E i) (E j))
    (hReserve : ∀ i, Disjoint (liftOrdinaryCycleArcs Z R) (E i))
    (hBuild : ∀ (i : Fin n) (H : Digraph V) (M : Fin (i.val*6) → Equiv.Perm V),
      H ≤ R → H ≤ matchingUnion M →
      ∃ (P : Digraph (V ⊕ Z)) (F : Fin 6 → Equiv.Perm V),
        valid i P ∧ E i ≤ P ∧
        P ≤ liftOrdinaryCycleArcs Z (R \ H) ⊔ E i ∧ ordinaryCycleHost P ≤ matchingUnion F) :
    ∃ P : Fin n → Digraph (V ⊕ Z),
      (∀ i, valid i (P i) ∧ E i ≤ P i ∧ P i ≤ liftOrdinaryCycleArcs Z R ⊔ E i) ∧
      Pairwise fun i j => Disjoint (P i) (P j) := by
  have hPrefix (t : ℕ) (ht : t ≤ n) :
      ∃ (P : Fin t → Digraph (V ⊕ Z)) (F : Fin t → Fin 6 → Equiv.Perm V),
        (∀ i, valid (Fin.castLE ht i) (P i) ∧ E (Fin.castLE ht i) ≤ P i ∧
          P i ≤ liftOrdinaryCycleArcs Z R ⊔ E (Fin.castLE ht i) ∧
          ordinaryCycleHost (P i) ≤ matchingUnion (F i)) ∧
        Pairwise fun i j => Disjoint (P i) (P j) := by
    induction t with
    | zero =>
      exact ⟨Fin.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
    | succ t ih =>
      have ht' : t ≤ n := by omega
      obtain ⟨P,F,hOld,hDis⟩ := ih ht'
      let H := R ⊓ ⨆ j, ordinaryCycleHost (P j)
      let index : Fin t × Fin 6 ≃ Fin (t*6) := finProdFinEquiv
      let M (a : Fin (t*6)) := F (index.symm a).1 (index.symm a).2
      have hCover : H ≤ matchingUnion M := by
        intro x y h
        obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp h.2
        obtain ⟨l,hl⟩ := (hOld j).2.2.2 hj
        exact ⟨index (j,l),by simpa only [M,Equiv.symm_apply_apply] using hl⟩
      let i := Fin.castLE ht (Fin.last t)
      obtain ⟨L,G,hValid,hOwn,hIn,hOrd⟩ := hBuild i H M inf_le_left hCover
      have hNewLe : L ≤ liftOrdinaryCycleArcs Z R ⊔ E i := by
        intro x y h
        rcases hIn h with h' | h'
        · left
          rcases x with x | x <;> rcases y with y | y
          · exact h'.1
          · exact h'.elim
          · exact h'.elim
          · exact h'.elim
        · exact .inr h'
      have hFresh (j : Fin t) : Disjoint (P j) L := by
        let j' := Fin.castLE ht' j
        have hNe : j' ≠ i := by
          intro h
          have h' := congrArg Fin.val h
          change j.val = t at h'
          omega
        rw [disjoint_iff_inf_le]
        intro x y h
        rcases (hOld j).2.2.1 h.1 with ho | he <;> rcases hIn h.2 with hn | hf
        · rcases x with x | x <;> rcases y with y | y
          · exact hn.2 ⟨ho,Digraph.iSup_adj.mpr ⟨j,h.1⟩⟩
          · exact hn
          · exact hn
          · exact hn
        · exact (disjoint_iff_inf_le.mp (hReserve i)) ⟨ho,hf⟩
        · exact (disjoint_iff_inf_le.mp (hReserve j')) ⟨by
            rcases x with x | x <;> rcases y with y | y
            · exact hn.1
            · exact hn
            · exact hn
            · exact hn,he⟩
        · exact (disjoint_iff_inf_le.mp (hApart hNe)) ⟨he,hf⟩
      have hCast (j : Fin t) : Fin.castLE ht j.castSucc = Fin.castLE ht' j := Fin.ext rfl
      refine ⟨Fin.snoc P L,Fin.snoc F G,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_last] using And.intro hValid (And.intro hOwn (And.intro hNewLe hOrd))
        · simpa only [Fin.snoc_castSucc,hCast] using hOld j
      · intro a b
        refine Fin.lastCases ?_ (fun a => ?_) a
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) b
          simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hFresh b).symm
        · refine Fin.lastCases (fun _ => ?_) (fun b h => ?_) b
          · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hFresh a
          · simpa only [Fin.snoc_castSucc] using hDis (fun e => h (congrArg Fin.castSucc e))
  obtain ⟨P,_,hP,hDis⟩ := hPrefix n le_rfl
  exact ⟨P,fun i => ⟨(hP i).1,(hP i).2.1,(hP i).2.2.1⟩,hDis⟩

/-- A single quantitative margin pays for every prefix of an
iteration. The block constructor sees only the remaining ordinary
graph and its superregular successor pairs. -/
theorem exists_iterated_parity_blocks_of_cluster_pairs [Fintype V]
    {k n m : ℕ} (R : Digraph V) (X : Fin k → Finset V)
    (E : Fin n → Digraph (V ⊕ Z)) (valid : Fin n → Digraph (V ⊕ Z) → Prop)
    (hApart : Pairwise fun i j => Disjoint (E i) (E j))
    (hReserve : ∀ i, Disjoint (liftOrdinaryCycleArcs Z R) (E i))
    (hm : 0 < m) (hSize : ∀ i, (X i).card = 2*m)
    (ε η d a : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hLoss : ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, IsLowerSuperregularPair R ε d (X i) (X (finRotate k i)))
    (hBuild : ∀ (i : Fin n) (T : Digraph V), T ≤ R →
      (∀ j, IsLowerSuperregularPair T η d (X j) (X (finRotate k j))) →
      ∃ (P : Digraph (V ⊕ Z)) (F : Fin 6 → Equiv.Perm V),
        valid i P ∧ E i ≤ P ∧
        P ≤ liftOrdinaryCycleArcs Z T ⊔ E i ∧ ordinaryCycleHost P ≤ matchingUnion F) :
    ∃ P : Fin n → Digraph (V ⊕ Z),
      (∀ i, valid i (P i) ∧ E i ≤ P i ∧ P i ≤ liftOrdinaryCycleArcs Z R ⊔ E i) ∧
      Pairwise fun i j => Disjoint (P i) (P j) := by
  apply exists_iterated_parity_blocks R E valid hApart hReserve
  intro i H M _ hMatch
  have hMargin : ((i.val*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*η) :=
    (show ((i.val*6:ℕ):ℝ) ≤ ((n*6:ℕ):ℝ) by
      exact_mod_cast Nat.mul_le_mul_right 6 i.isLt.le).trans hLoss
  exact hBuild i (R \ H) (fun _ _ h => h.1) (fun j =>
    residual_pairs_after_matchings M hMatch _ _ hm (hSize j) (hSize _) ε η d a
      hη hη₁ ha hd hTol hMargin (hPairs j))

end OverfullWork.DirectedRobustExpansion
