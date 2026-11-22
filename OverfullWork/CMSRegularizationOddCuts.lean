module

public import OverfullWork.CMSCanonicalTheorem42
public import OverfullWork.StarBudgetOddCuts

@[expose] public section


/-! The large-set and ranked small-set cut reduction in CMS Claim 4.3.
Only triples through both exceptional vertices can obstruct the
regular completion. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion PrunedCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem robust_cut_lower (M : MultiGraph V) (S : Finset V) (r t : ℕ)
    (hRob : IsRobustAt M.supportGraph r t)
    (hLo : t ≤ S.card) (hHi : S.card+t ≤ Fintype.card V) :
    r*r ≤ M.cutSize S := by
  let R := neighbourhood M.supportGraph r S
  have hExpand : S.card+r ≤ R.card := hRob S hLo hHi
  have hSplit := card_sdiff_add_card_inter R S
  have hLoss : (R ∩ S).card ≤ S.card := card_le_card inter_subset_right
  have hCount : r ≤ (R\S).card := by omega
  have hRows : ∀ v ∈ R\S, r ≤ neighboursIn M.supportGraph S v := by
    intro v hv
    exact (mem_filter.mp (mem_sdiff.mp hv).1).2
  exact (Nat.mul_le_mul_left r hCount).trans
    (BipartiteRobustCuts.incidences_le_cut M S (R\S) r
      (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2) hRows)

theorem support_pair_le_cut_add_internal (D : MultiGraph V) (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    D.supportGraph.degree x+D.supportGraph.degree y ≤ D.cutSize S+2*S.card := by
  have hSplit (v : V) : neighboursIn D.supportGraph S v+
      neighboursIn D.supportGraph Sᶜ v = D.supportGraph.degree v :=
    LowSetEdgePreprocessing.neighboursIn_add_compl D.supportGraph S v
  have hCard (v : V) : neighboursIn D.supportGraph S v ≤ S.card := by
    rw [neighboursIn_eq_filter_card]
    exact card_filter_le _ _
  have hCut : (∑ v ∈ ({x,y} : Finset V), ∑ w ∈ Sᶜ, D.mult s(v,w)) ≤ D.cutSize S :=
    sum_le_sum_of_subset_of_nonneg (insert_subset hx (singleton_subset_iff.mpr hy))
      (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hxy] at hCut
  have hWeight (v : V) := BipartiteRobustCuts.neighbours_le_weight D Sᶜ v
  have hxSplit := hSplit x
  have hySplit := hSplit y
  have hxCard := hCard x
  have hyCard := hCard y
  have hxWeight := hWeight x
  have hyWeight := hWeight y
  omega

/-- The remaining obstruction is the cut of a triple with both
anchors. The pair bound is supplied by ranks two and three or higher
in the proof of Claim 4.3. -/
theorem no_overfull_iff_two_anchor_triples (D M : MultiGraph V) (d m r t : ℕ) (a b : V)
    (hab : a ≠ b) (hCard : Fintype.card V = 2*m)
    (hReg : M.IsRegularOfDegree d) (hSub : ∀ e, D.mult e ≤ M.mult e)
    (hRob : IsRobustAt D.supportGraph r t) (hRate : d ≤ r*r)
    (hOrd : ∀ x y, x ≠ a → x ≠ b → y ≠ a → y ≠ b → x ≠ y →
      d+2*t ≤ D.supportGraph.degree x+D.supportGraph.degree y) :
    (¬M.HasOverfullSubset d) ↔
      ∀ v, v ≠ a → v ≠ b → d ≤ M.cutSize {a,b,v} := by
  rw [M.noOverfull_iff_odd_cut_bound hReg]
  constructor
  · intro h v hva hvb
    apply h
    have hThree : ({a,b,v} : Finset V).card = 3 := by simp [hab,hva.symm,hvb.symm]
    rw [hThree]
    exact ⟨1,rfl⟩
  · intro hTriples
    have hSmallSide (S : Finset V) (hOdd : Odd S.card) (hHalf : S.card ≤ m) : d ≤ M.cutSize S := by
      have hMono := StarBudgetOddCuts.cut_mono D M hSub S
      by_cases hBig : t ≤ S.card
      · exact hRate.trans ((robust_cut_lower D S r t hRob hBig (by omega)).trans hMono)
      let T := S.filter (fun v => v ≠ a ∧ v ≠ b)
      by_cases hTwo : 1 < T.card
      · obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hTwo
        obtain ⟨hxS,hxa,hxb⟩ := mem_filter.mp hx
        obtain ⟨hyS,hya,hyb⟩ := mem_filter.mp hy
        have hPair := support_pair_le_cut_add_internal D S x y hxS hyS hxy
        have hLower := hOrd x y hxa hxb hya hyb hxy
        omega
      have hTotal : S.card ≤ T.card+2 := by
        have hSub' : S ⊆ T ∪ {a,b} := by
          intro v hv
          by_cases hv' : v ∈ ({a,b} : Finset V)
          · exact mem_union_right _ hv'
          · have hn : v ≠ a ∧ v ≠ b := by simpa using hv'
            exact mem_union_left _ (mem_filter.mpr ⟨hv,hn⟩)
        have hUnion := (card_le_card hSub').trans (card_union_le _ _)
        rw [card_pair hab] at hUnion
        exact hUnion
      have hOneOrThree : S.card = 1 ∨ S.card = 3 := by
        obtain ⟨j,hj⟩ := hOdd
        omega
      rcases hOneOrThree with hs | hs
      · obtain ⟨v,rfl⟩ := card_eq_one.mp hs
        rw [CanonicalAdmissibility.cut_singleton,hReg]
      · have hT : T.card = 1 := by omega
        obtain ⟨v,hv⟩ := card_eq_one.mp hT
        have hvT : v ∈ T := by rw [hv]; exact mem_singleton_self _
        obtain ⟨hvS,hva,hvb⟩ := mem_filter.mp hvT
        have hEq : S = {a,b,v} := by
          apply eq_of_subset_of_card_le
          · intro x hx
            by_cases he : x ∈ ({a,b} : Finset V)
            · simpa only [mem_insert,mem_singleton] using (show x = a ∨ x = b ∨ x = v by
                rcases mem_insert.mp he with hh|hh
                · exact Or.inl hh
                · exact Or.inr (Or.inl (mem_singleton.mp hh)))
            · have hxT : x ∈ T := mem_filter.mpr ⟨hx,by simpa using he⟩
              rw [hv] at hxT
              simp [mem_singleton.mp hxT]
          · simp [hs,hab,hva.symm,hvb.symm]
        rw [hEq]
        exact hTriples v hva hvb
    intro S hOdd
    by_cases hHalf : S.card ≤ m
    · exact hSmallSide S hOdd hHalf
    · have hEven : Even (Fintype.card V) := ⟨m,by omega⟩
      rw [←M.cutSize_compl S]
      apply hSmallSide _ (MultiGraph.odd_card_compl hEven hOdd)
      rw [card_compl,hCard]
      omega

end OverfullWork.CanonicalRegularization
