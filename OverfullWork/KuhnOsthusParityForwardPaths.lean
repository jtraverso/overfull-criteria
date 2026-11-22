module

public import OverfullWork.KuhnOsthusParitySwitchMatchings

@[expose] public section


/-! Join the ordered switch matchings through the ordinary cluster
pairs of the parity reserve. The two marked tracks retain their
specified physical edges. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V J : Type*} [Fintype V]

/-- Fill the gap between two bundles while retaining their existing
path labels and all of their previously prescribed vertices. -/
theorem OrderedClusterPaths.exists_join_through_long_route {D : Digraph V}
    {A : ℕ → Finset V} {s a b t : ℕ}
    (P : OrderedClusterPaths D A J s a) (Q : OrderedClusterPaths D A J b t)
    (hsa : s ≤ a) (hbt : b ≤ t) (hab : a+3 ≤ b)
    (m r : ℕ) (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hr : 0 < r) (hCut : (m:ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ)))
    (hSize : ∀ i, a ≤ i → i ≤ b → (A i).card = m)
    (hDis : ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → i ≠ j → Disjoint (A i) (A j))
    (hPair : ∀ i, a ≤ i → i < b → IsLowerSuperregularPair D ε d (A i) (A (i+1))) :
    ∃ R : OrderedClusterPaths D A J s t,
      (∀ i ≤ a, ∀ j, R.vertex i j = P.vertex i j) ∧
      ∀ i, b ≤ i → ∀ j, R.vertex i j = Q.vertex i j := by
  obtain ⟨M,hL,hR⟩ := exists_ordered_cluster_paths D A a b m r hab
    (P.orderAt a hsa le_rfl) (Q.orderAt b le_rfl hbt) ε d hε hGap hd hr hCut hBudget hSize hDis hPair
  let L := P.concat M (fun j => (hL j).symm)
  have hJoin (j : J) : L.vertex b j = Q.vertex b j :=
    (P.concat_right M _ (by omega) j).trans (hR j)
  let R := L.concat Q hJoin
  refine ⟨R,?_,fun i hi j => L.concat_right Q hJoin hi j⟩
  intro i hi j
  exact (L.concat_left Q hJoin (by omega) j).trans (P.concat_left M _ hi j)

/-- The three marked matchings of B₁ occur in their prescribed
order. The ordinary forward part spans the full interval up to
the entrance of the exceptional system. -/
theorem exists_parity_forward_paths {D : Digraph V} {A : ℕ → Finset V}
    {s a b c m r : ℕ} {ε d : ℝ}
    (P₀ : PrescribedSwitchMatching D (A s) (A (s+1)))
    (P₁ : PrescribedSwitchMatching D (A a) (A (a+1)))
    (P₂ : PrescribedSwitchMatching D (A b) (A (b+1))) (j₀ : Fin m)
    (hsa : s+4 ≤ a) (hab : a+4 ≤ b) (hbc : b+4 ≤ c)
    (hSize : ∀ i, s ≤ i → i ≤ c → (A i).card = 2*m)
    (hDis : ∀ i j, s ≤ i → i ≤ c → s ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hPair : ∀ i, s ≤ i → i < c → IsLowerSuperregularPair D ε d (A i) (A (i+1)))
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ T : OrderedClusterPaths D A (Fin m × Fin 2) s c,
      (∀ l, T.vertex s (j₀,cycleAbsorberLane l) = (P₀.source l).val ∧
        T.vertex (s+1) (j₀,cycleAbsorberLane l) = (P₀.target l).val) ∧
      (∀ l, T.vertex a (j₀,cycleAbsorberLane l) = (P₁.source l).val ∧
        T.vertex (a+1) (j₀,cycleAbsorberLane l) = (P₁.target l).val) ∧
      (∀ l, T.vertex b (j₀,cycleAbsorberLane l) = (P₂.source l).val ∧
        T.vertex (b+1) (j₀,cycleAbsorberLane l) = (P₂.target l).val) := by
  have matching {i : ℕ} (hi : s ≤ i) (hic : i < c)
      (P : PrescribedSwitchMatching D (A i) (A (i+1))) :=
    P.exists_ordered_pair j₀ (hPair i hi hic) (hSize i hi hic.le) (hSize (i+1) (by omega) (by omega))
      hε hGap hd hr hCut hBudget
  obtain ⟨M₀,hM₀⟩ := matching le_rfl (by omega) P₀
  obtain ⟨M₁,hM₁⟩ := matching (by omega) (by omega) P₁
  obtain ⟨M₂,hM₂⟩ := matching (by omega) (by omega) P₂
  have join {l t u : ℕ} (P : OrderedClusterPaths D A (Fin m × Fin 2) s l)
      (Q : OrderedClusterPaths D A (Fin m × Fin 2) t u)
      (hsl : s ≤ l) (htu : t ≤ u) (hlt : l+3 ≤ t) (huc : u ≤ c) :=
    P.exists_join_through_long_route Q hsl htu hlt (2*m) r ε d hε hGap hd hr hCut hBudget
      (fun i hi hi' => hSize i (by omega) (by omega))
      (fun i j hi hi' hj hj' h => hDis i j (by omega) (by omega) (by omega) (by omega) h)
      (fun i hi hi' => hPair i (by omega) (by omega))
  obtain ⟨L,hL₀,hL₁⟩ := join M₀ M₁ (by omega) (by omega) (by omega) (by omega)
  obtain ⟨Q,hQ₀,hQ₁⟩ := join L M₂ (by omega) (by omega) (by omega) (by omega)
  let e : Fin m × Fin 2 ≃ A c := (cycleAbsorberSwitchSlot m).trans
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hSize c (by omega) le_rfl)).symm
  obtain ⟨R,hR,_⟩ := exists_ordered_cluster_paths D A (b+1) c (2*m) r (by omega)
    (Q.orderAt (b+1) (by omega) le_rfl) e ε d hε hGap hd hr hCut hBudget
    (fun i hi hi' => hSize i (by omega) hi')
    (fun i j hi hi' hj hj' h => hDis i j (by omega) hi' (by omega) hj' h)
    (fun i hi hi' => hPair i (by omega) hi')
  let T := Q.concat R (fun j => (hR j).symm)
  have hKeep (i : ℕ) (hi : i ≤ b+1) (j : Fin m × Fin 2) :
      T.vertex i j = Q.vertex i j := Q.concat_left R _ hi j
  refine ⟨T,?_,?_,?_⟩
  · intro l
    constructor
    · exact (hKeep _ (by omega) _).trans ((hQ₀ _ (by omega) _).trans ((hL₀ _ (by omega) _).trans (hM₀ l).1))
    · exact (hKeep _ (by omega) _).trans ((hQ₀ _ (by omega) _).trans ((hL₀ _ (by omega) _).trans (hM₀ l).2))
  · intro l
    constructor
    · exact (hKeep _ (by omega) _).trans ((hQ₀ _ (by omega) _).trans ((hL₁ _ (by omega) _).trans (hM₁ l).1))
    · exact (hKeep _ (by omega) _).trans ((hQ₀ _ (by omega) _).trans ((hL₁ _ (by omega) _).trans (hM₁ l).2))
  · intro l
    constructor
    · exact (hKeep _ (by omega) _).trans ((hQ₁ _ (by omega) _).trans (hM₂ l).1)
    · exact (hKeep _ (by omega) _).trans ((hQ₁ _ (by omega) _).trans (hM₂ l).2)

end OverfullWork.DirectedRobustExpansion
