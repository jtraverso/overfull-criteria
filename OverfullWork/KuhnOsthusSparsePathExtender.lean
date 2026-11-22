module

public import OverfullWork.KuhnOsthusSparseSuccessorPairs

@[expose] public section


/-! The prepared extension of Lemma 8.3 with sparse cycle pairs.
The untouched styles protect the residual semidegrees. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
universe u

/-- Starting from scheduled routes and the physical reserve estimates,
extend the prescribed system using the sparse-superregular conditions
of the paper. -/
theorem exists_hamilton_extension_of_sparse_prepared_routes
    (d ε μ ζ ν τ γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ) (hζ : 0 < ζ) (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ*d)
    (hScale : 160*ε ≤ (ζ*μ)^2) (hDiscard : 8*ν ≤ τ*(ζ*d)^2)
    (hνDensity : ν < (1-ε)*d*ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n : ℕ}
      (G : Digraph (Fin (n+1))) (Q H R : Digraph V)
      (cluster : V → Fin (n+1)) (l : Arc Q → List (Fin (n+1)))
      (A B : Fin (n+1) → Finset V) (m e : ℕ) (η c : ℝ),
      let s := finRotate (n+1)
      let U i := (univ : Finset V).filter (fun x => cluster x = i)
      IsDirectedPathSystem Q →
      (∀ i, ¬ G.Adj i i) →
      (∀ j : Arc Q, DirectedListRoutes.Route (reindexSources G s.symm)
        (cluster j.val.2) (s (cluster j.val.1)) (l j)) →
      0 < m → 50*e ≤ m →
      (∀ i, 50*(A i).card = 24*m) →
      (∀ i, A i ⊆ U i) → (∀ i, B i ⊆ U i) →
      (∀ i, (U i).card = m) →
      (∀ i x, x ∈ A i ∨ x ∈ B i → ¬ IncidentTo Q x) →
      (∀ i, Disjoint (A i) (B i)) →
      (∀ i j, G.Adj i j → ∀ S ⊆ A i, ∀ T ⊆ A j,
        e < S.card → e < T.card → 0 < incidences H S T) →
      (∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ m) →
      (∀ i, 10*(∑ j : Arc Q, if s.symm (cluster j.val.2) = i then (1:ℕ) else 0) ≤ m) →
      (∀ i, 10*(∑ j : Arc Q, if s (cluster j.val.1) = i then (1:ℕ) else 0) ≤ m) →
      (∀ i, (B i).Nonempty ∧ N ≤ (B i).card) →
      (∀ i, η*m ≤ ε*((B i).card:ℝ)) →
      (∀ i, 16 ≤ (ζ*d)^2*((B i).card:ℝ)) →
      (∀ i, c ≤ (d/μ)^2*((B i).card:ℝ)) →
      (∀ i, ∀ X ⊆ U i, ∀ Y ⊆ U (s i), η*m ≤ (X.card:ℝ) → η*m ≤ (Y.card:ℝ) →
        (1-ε)*d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ)) →
      (∀ i v, v ∈ U (s i) → ζ*d*m ≤ (inNeighbours R (B i) v:ℝ)) →
      (∀ i v, v ∈ U i → ζ*d*m ≤ (outTo R (B (s i)) v:ℝ)) →
      (∀ i, ∀ x ∈ U (s i), ∀ y ∈ U (s i), x ≠ y →
        (((U i).filter (fun v => R.Adj v x ∧ R.Adj v y)).card:ℝ) ≤ c) →
      (∀ i, ∀ x ∈ U i, ∀ y ∈ U i, x ≠ y →
        (((U (s i)).filter (fun v => R.Adj x v ∧ R.Adj y v)).card:ℝ) ≤ c) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, Q.Adj x y → ρ x = y) ∧ (∀ x, ((Q ⊔ H) ⊔ R).Adj x (ρ x)) := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_sparse_successor_pairs.{u} d ε μ ζ ν τ γ
    hd hε hε1 hμ hζ hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
  refine ⟨N,?_⟩
  intro V _ n G Q H R cluster l A B m e η c s U hQ hG hRoute hm he hA hAU hBU hU hFresh hDis
    hChord hInt hFrom hTo hB hScale hDiag hCodeg hRect hIn hOut hCI hCO
  obtain ⟨D,hDQ,hDSub,hPath,hBalance,hUntouched⟩ :=
    exists_balanced_extension_for_routes G Q H cluster s hQ l hG hRoute A m e hm he hA
      (fun i x hx => (mem_filter.mp (hAU i hx)).2)
      (fun i x hx => hFresh i x (Or.inl hx)) hChord hInt (by
        intro i
        convert hFrom i using 2
        apply sum_congr rfl
        intro j _
        by_cases h : s.symm (cluster j.val.2) = i <;> simp [h]) (by
        intro i
        convert hTo i using 2
        apply sum_congr rfl
        intro j _
        by_cases h : s (cluster j.val.1) = i <;> simp [h]) (by
        intro i
        have he (j : Fin (n+1)) :
            (@Finset.filter V (fun x => cluster x = j) (fun _ => Classical.propDecidable _) univ).card =
              (U j).card := by
          congr 1
          ext x
          simp only [U,mem_filter]
        exact (he i).trans ((hU i).trans ((hU (s i)).symm.trans (he (s i)).symm)))
  let S := freeOut D cluster
  let T i := freeIn D cluster (s i)
  have hFree (i : Fin (n+1)) {x : V} (hx : x ∈ B i) :
      x ∈ freeOut D cluster i ∧ x ∈ freeIn D cluster i := by
    have hc := (mem_filter.mp (hBU i hx)).2
    have hApart : x ∉ A (cluster x) := fun ha => disjoint_left.mp (hDis i) (hc ▸ ha) hx
    exact hc ▸ hUntouched x (hFresh i x (Or.inr hx)) hApart
  have hSB (i : Fin (n+1)) : B i ⊆ S i := fun _ hx => (hFree i hx).1
  have hTB (i : Fin (n+1)) : B (s i) ⊆ T i := fun _ hx => (hFree (s i) hx).2
  have hSU (i : Fin (n+1)) : S i ⊆ U i :=
    fun _ hx => mem_filter.mpr ⟨mem_univ _,(mem_freeOut.mp hx).1⟩
  have hTU (i : Fin (n+1)) : T i ⊆ U (s i) :=
    fun _ hx => mem_filter.mpr ⟨mem_univ _,(mem_freeIn.mp hx).1⟩
  have hLow (i : Fin (n+1)) : ((B i).card:ℝ) ≤ (S i).card := by
    exact_mod_cast card_le_card (hSB i)
  have hHigh (i : Fin (n+1)) : ((S i).card:ℝ) ≤ m := by
    exact_mod_cast (card_le_card (hSU i)).trans_eq (hU i)
  have hScale' (i : Fin (n+1)) : η*m ≤ ε*((S i).card:ℝ) :=
    (hScale i).trans (mul_le_mul_of_nonneg_left (hLow i) hε.le)
  have hN' (i : Fin (n+1)) : N ≤ (S i).card := (hB i).2.trans (card_le_card (hSB i))
  have hO (i : Fin (n+1)) : ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i := by
    obtain ⟨x,hx⟩ := (hB i).1
    exact ⟨x,(hFree i hx).2,(hFree i hx).1⟩
  have hdg (i : Fin (n+1)) : (16:ℝ)*(S i).card ≤ (ζ*d*(S i).card)^2 := by
    have h₁ := (hDiag i).trans (mul_le_mul_of_nonneg_left (hLow i) (sq_nonneg (ζ*d)))
    have h₂ := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg (S i).card : (0:ℝ) ≤ _)
    nlinarith only [h₂]
  have hPairs (i : Fin (n+1)) : ∃ f : S i ≃ T i,
      SparseSuccessorPairBounds (pairOnSources R (S i) (T i) f) d ε μ ζ := by
    have hCard : Fintype.card (S i) = Fintype.card (T i) := by
      simpa only [Fintype.card_coe] using hBalance i
    obtain ⟨f⟩ := Fintype.card_eq.mp hCard
    refine ⟨f,sparse_pair_bounds_of_physical R (S i) (T i) f d ε μ ζ ?_ ?_ ?_ ?_ ?_⟩
    · intro y hy
      have hMono : inNeighbours R (B i) y ≤ inNeighbours R (S i) y :=
        card_le_card (filter_subset_filter _ (hSB i))
      have hc : (inNeighbours R (B i) y:ℝ) ≤ (inNeighbours R (S i) y:ℝ) := by
        exact_mod_cast hMono
      exact (mul_le_mul_of_nonneg_left (hHigh i) (mul_nonneg hζ.le hd.le)).trans
        ((hIn i y (hTU i hy)).trans hc)
    · intro x hx
      have hMono : outTo R (B (s i)) x ≤ outTo R (T i) x :=
        card_le_card (filter_subset_filter _ (hTB i))
      have hc : (outTo R (B (s i)) x:ℝ) ≤ (outTo R (T i) x:ℝ) := by
        exact_mod_cast hMono
      exact (mul_le_mul_of_nonneg_left (hHigh i) (mul_nonneg hζ.le hd.le)).trans
        ((hOut i x (hSU i hx)).trans hc)
    · intro x hx y hy hxy
      have hc : (((S i).filter (fun v => R.Adj v x ∧ R.Adj v y)).card:ℝ) ≤
          (((U i).filter (fun v => R.Adj v x ∧ R.Adj v y)).card:ℝ) := by
        exact_mod_cast card_le_card (filter_subset_filter (fun v => R.Adj v x ∧ R.Adj v y) (hSU i))
      exact hc.trans ((hCI i x (hTU i hx) y (hTU i hy) hxy).trans
        ((hCodeg i).trans (mul_le_mul_of_nonneg_left (hLow i) (sq_nonneg (d/μ)))))
    · intro x hx y hy hxy
      have hc : (((T i).filter (fun v => R.Adj x v ∧ R.Adj y v)).card:ℝ) ≤
          (((U (s i)).filter (fun v => R.Adj x v ∧ R.Adj y v)).card:ℝ) := by
        exact_mod_cast card_le_card (filter_subset_filter (fun v => R.Adj x v ∧ R.Adj y v) (hTU i))
      exact hc.trans ((hCO i x (hSU i hx) y (hSU i hy) hxy).trans
        ((hCodeg i).trans (mul_le_mul_of_nonneg_left (hLow i) (sq_nonneg (d/μ)))))
    · intro X hX Y hY hXL hYL
      exact hRect i X (hX.trans (hSU i)) Y (hY.trans (hTU i))
        ((hScale' i).trans hXL) ((hScale' i).trans hYL)
  obtain ⟨ρ,hCycle,hKeep,hEdge⟩ := hN D R cluster hPath hO hN' hdg hPairs
  exact ⟨ρ,hCycle,fun x y h => hKeep x y (hDQ h),
    fun x => (sup_le_sup_right hDSub R) (hEdge x)⟩

end OverfullWork.DirectedRobustExpansion
