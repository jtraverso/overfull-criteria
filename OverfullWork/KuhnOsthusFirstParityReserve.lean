module

public import OverfullWork.KuhnOsthusParityReserveClosure

@[expose] public section


/-! The first parity reserve of Lemma 10.5, with its two repair
pairs, the first matching of the K₂,₃, and the exceptional system
of the sixth canonical interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

structure FirstParityReserve (D E : Digraph V) (A B : Finset V) where
  triple : ParityTripleSwitch D A B
  factor : OrderedParityFactor D E
  triple_arcs : ∀ l, factor.mark (l,2) = (triple.source l).val ∧
    factor.permutation (factor.mark (l,2)) = ((triple.matching 0).target l).val
  unused : ∀ i : Fin 3, i ≠ 0 → ∀ l,
    (D \ (factor.ordinary ⊔ E)).Adj (triple.source l) ((triple.matching i).target l)

variable [Fintype V]

/-- Construct B₁ on the precise pairs of Lemma 10.5, in zero-based
coordinates. Its first two marked arcs in each lane are the free
repair arcs, and the third is one of the triple-switch arcs. -/
theorem kuhn_osthus_lemma_10_5_first_reserve {D H : Digraph V}
    {q m r : ℕ} {ε d : ℝ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m)
    (hCover : ∀ v, ∃ i, v ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (hPair : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate (14*q) i)))
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let A := cyclicCluster X (by omega)
    ∀ (P₀ : PrescribedSwitchMatching D (A 11) (A 12))
      (P₁ : PrescribedSwitchMatching D (A (7*q+11)) (A (7*q+12)))
      (E₆ : IntervalPathCover H (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q))),
      ∃ B₁ : FirstParityReserve D E₆.digraph (A (7*q+15)) (A (7*q+16)),
        (∀ l, B₁.factor.mark (l,0) = (P₀.source l).val ∧
          B₁.factor.permutation (B₁.factor.mark (l,0)) = (P₀.target l).val) ∧
        ∀ l, B₁.factor.mark (l,1) = (P₁.source l).val ∧
          B₁.factor.permutation (B₁.factor.mark (l,1)) = (P₁.target l).val := by
  intro A P₀ P₁ E₆
  have hk : 0 < 14*q := by omega
  have hA (i : ℕ) : IsLowerSuperregularPair D ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair D ε d (A i) (cyclicCluster X hk (i+1))
    rw [cyclicCluster_successor]
    exact hPair _
  obtain ⟨K⟩ := (hA (7*q+15)).exists_parity_triple_switch (hSize _) (hSize _) hm hε hGap hd hBudget
  have hApart (i j : ℕ) (hi : i ≤ 10*q) (hj : j ≤ 10*q) (hne : i ≠ j) :
      Disjoint (A i) (A j) := cyclicCluster_distinct hk hDis
    (by rwa [Nat.mod_eq_of_lt (by omega : i < 14*q),Nat.mod_eq_of_lt (by omega : j < 14*q)])
  let j₀ : Fin m := ⟨0,hm⟩
  obtain ⟨P,hP₀,hP₁,hP₂⟩ := exists_parity_forward_paths (r := r) (c := 10*q)
    P₀ P₁ (K.matching 0) j₀ (by omega) (by omega) (by omega)
    (fun _ _ _ => hSize _) (fun i j _ hi _ hj => hApart i j hi hj) (fun i _ _ => hA i)
    hε hGap hd hr hCut hBudget
  obtain ⟨F,hF₀,hF₁,hF₂⟩ := P.exists_closed_parity_factor X hk
    (show 11 < 7*q+11 by omega) (show 7*q+11 < 7*q+15 by omega) (by omega)
    (by omega) (by omega) (by omega) hCover hDis hSize j₀ E₆ hPair hε hGap hd hr hCut hBudget
  have hTriple (l : Bool) : F.mark (l,2) = (K.source l).val ∧
      F.permutation (F.mark (l,2)) = ((K.matching 0).target l).val :=
    ⟨(hF₂ l).1.trans (hP₂ l).1,(hF₂ l).2.trans (hP₂ l).2⟩
  refine ⟨⟨K,F,hTriple,?_⟩,?_,?_⟩
  · intro i hi l
    refine ⟨(K.matching i).edge l,?_⟩
    intro h
    have he := (F.exact_factor _ _).mp h
    rw [←(hTriple l).1,(hTriple l).2] at he
    have hT : (K.matching 0).target l = (K.matching i).target l := Subtype.ext he
    have hIndex := K.target.injective hT
    cases l
    · exact hi hIndex.symm
    · exact hi ((finRotate 3).injective hIndex).symm
  · intro l
    exact ⟨(hF₀ l).1.trans (hP₀ l).1,(hF₀ l).2.trans (hP₀ l).2⟩
  · intro l
    exact ⟨(hF₁ l).1.trans (hP₁ l).1,(hF₁ l).2.trans (hP₁ l).2⟩

end OverfullWork.DirectedRobustExpansion
