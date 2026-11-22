module

public import OverfullWork.KuhnOsthusExceptionalIntervalBalance
public import OverfullWork.KuhnOsthusExceptionalPairStability

@[expose] public section


/-! Convert the matching budget of the exceptional interval into
the free successor pairs needed in Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {W I : Type*} [Fintype W]

private theorem free_successor_pairs_of_centred_exceptional_budget
    (D R : Digraph W) (cluster : W → I) (s : Equiv.Perm I)
    (m loss N r : ℕ) (d δ ε : ℝ) (c : I → ℝ)
    (hd : 2*ε < d) (hdc : ∀ i, d ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hTol : 2*δ ≤ ε)
    (hm : loss < m) (hN : N ≤ m-loss) (hr : 0 < r)
    (hCut : ε*(m:ℝ) ≤ r) (hDegree : (r:ℝ) ≤ (d-2*ε)*((m-loss:ℕ):ℝ))
    (hPay : (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε)
    (hSize : ∀ i, (intervalCluster cluster i).card = m)
    (hFree : ∀ i, m ≤ (freeOut D cluster i ∩ freeIn D cluster i).card + loss)
    (hPair : ∀ i, IsSuperregularPair R δ (c i) (intervalCluster cluster i) (intervalCluster cluster (s i))) :
    (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ freeOut D cluster i) ∧
    (∀ i, N ≤ (freeOut D cluster i).card) ∧
    (∀ i, 0 < r ∧ ε*((freeOut D cluster i).card:ℝ) ≤ (r:ℝ) ∧
      (r:ℝ) ≤ (d-2*ε)*((freeOut D cluster i).card:ℝ)) ∧
    ∀ i, IsSuperregularPair R ε (c i) (freeOut D cluster i) (freeIn D cluster (s i)) := by
  have hSubOut (i : I) : freeOut D cluster i ⊆ intervalCluster cluster i :=
    fun x hx => (mem_intervalCluster cluster i x).mpr (mem_freeOut.mp hx).1
  have hSubIn (i : I) : freeIn D cluster i ⊆ intervalCluster cluster i :=
    fun x hx => (mem_intervalCluster cluster i x).mpr (mem_freeIn.mp hx).1
  have hLower (i : I) : m-loss ≤ (freeOut D cluster i ∩ freeIn D cluster i).card := by
    have h := hFree i
    omega
  have hLowerO (i : I) : m-loss ≤ (freeOut D cluster i).card :=
    (hLower i).trans (card_le_card inter_subset_left)
  have hLowerI (i : I) : m-loss ≤ (freeIn D cluster i).card :=
    (hLower i).trans (card_le_card inter_subset_right)
  have hPos : 0 < m-loss := by omega
  refine ⟨?_,fun i => hN.trans (hLowerO i),?_,?_⟩
  · intro i
    obtain ⟨x,hx⟩ := card_pos.mp (hPos.trans_le (hLower i))
    exact ⟨x,(mem_inter.mp hx).2,(mem_inter.mp hx).1⟩
  · intro i
    have hSmall : ((freeOut D cluster i).card:ℝ) ≤ m := by
      exact_mod_cast (card_le_card (hSubOut i)).trans_eq (hSize i)
    have hLarge : ((m-loss:ℕ):ℝ) ≤ (freeOut D cluster i).card := by exact_mod_cast hLowerO i
    exact ⟨hr,(mul_le_mul_of_nonneg_left hSmall hε.le).trans hCut,
      hDegree.trans (mul_le_mul_of_nonneg_left hLarge (sub_nonneg.mpr hd.le))⟩
  · intro i
    have hBudget (j : I) (A : Finset W) (hSub : A ⊆ intervalCluster cluster j)
        (hCard : m-loss ≤ A.card) :
        ((intervalCluster cluster j).card:ℝ)*δ +
          (((intervalCluster cluster j) \ A).card:ℝ) ≤ (A.card:ℝ)*ε := by
      have h := card_sdiff_add_card_eq_card hSub
      rw [hSize j] at h
      have hr : (((intervalCluster cluster j) \ A).card:ℝ) ≤ loss := by
        exact_mod_cast (show ((intervalCluster cluster j) \ A).card ≤ loss by omega)
      have hs : ((m-loss:ℕ):ℝ) ≤ A.card := by exact_mod_cast hCard
      rw [hSize j]
      exact (add_le_add le_rfl hr).trans (hPay.trans (mul_le_mul_of_nonneg_right hs hε.le))
    apply IsSuperregularPair.on_free_subcells R _ _ _ _ (hSubOut i) (hSubIn (s i))
      (card_pos.mp (hPos.trans_le (hLowerO i))) (card_pos.mp (hPos.trans_le (hLowerI (s i))))
      (c i) δ ε (by linarith only [hd,hdc i,hε]) (hc1 i) hε hε1 hTol
      (hBudget i _ (hSubOut i) (hLowerO i))
      (hBudget (s i) _ (hSubIn (s i)) (hLowerI (s i))) (hPair i)

/-- A bound on all touched vertices of a cluster at once guarantees
overlap of the free sides and pays for the regularity lost by trimming.
The same integer threshold works for every successor pair. -/
theorem free_successor_pairs_of_exceptional_budget
    (D R : Digraph W) (cluster : W → I) (s : Equiv.Perm I)
    (m loss N r : ℕ) (d δ ε : ℝ) (hd : 2*ε < d) (hd1 : d ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hTol : 2*δ ≤ ε)
    (hm : loss < m) (hN : N ≤ m-loss) (hr : 0 < r)
    (hCut : ε*(m:ℝ) ≤ r) (hDegree : (r:ℝ) ≤ (d-2*ε)*((m-loss:ℕ):ℝ))
    (hPay : (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε)
    (hSize : ∀ i, (intervalCluster cluster i).card = m)
    (hFree : ∀ i, m ≤ (freeOut D cluster i ∩ freeIn D cluster i).card + loss)
    (hPair : ∀ i, IsSuperregularPair R δ d (intervalCluster cluster i) (intervalCluster cluster (s i))) :
    (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ freeOut D cluster i) ∧
    (∀ i, N ≤ (freeOut D cluster i).card) ∧
    (∀ i, 0 < r ∧ ε*((freeOut D cluster i).card:ℝ) ≤ (r:ℝ) ∧
      (r:ℝ) ≤ (d-2*ε)*((freeOut D cluster i).card:ℝ)) ∧
    ∀ i, IsSuperregularPair R ε d (freeOut D cluster i) (freeIn D cluster (s i)) := by
  exact free_successor_pairs_of_centred_exceptional_budget D R cluster s m loss N r d δ ε
    (fun _ => d) hd (fun _ => le_rfl) (fun _ => hd1) hε hε1 hTol hm hN hr hCut hDegree
    hPay hSize hFree hPair

/-- A bound on all touched vertices of a cluster at once guarantees
overlap of the free sides and pays for the regularity lost by trimming.
The same integer threshold works for every successor pair. -/
theorem free_lower_successor_pairs_of_exceptional_budget
    (D R : Digraph W) (cluster : W → I) (s : Equiv.Perm I)
    (m loss N r : ℕ) (d δ ε : ℝ) (hd : 2*ε < d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hTol : 2*δ ≤ ε)
    (hm : loss < m) (hN : N ≤ m-loss) (hr : 0 < r)
    (hCut : ε*(m:ℝ) ≤ r) (hDegree : (r:ℝ) ≤ (d-2*ε)*((m-loss:ℕ):ℝ))
    (hPay : (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε)
    (hSize : ∀ i, (intervalCluster cluster i).card = m)
    (hFree : ∀ i, m ≤ (freeOut D cluster i ∩ freeIn D cluster i).card + loss)
    (hPair : ∀ i, IsLowerSuperregularPair R δ d (intervalCluster cluster i) (intervalCluster cluster (s i))) :
    (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ freeOut D cluster i) ∧
    (∀ i, N ≤ (freeOut D cluster i).card) ∧
    (∀ i, 0 < r ∧ ε*((freeOut D cluster i).card:ℝ) ≤ (r:ℝ) ∧
      (r:ℝ) ≤ (d-2*ε)*((freeOut D cluster i).card:ℝ)) ∧
    ∀ i, IsLowerSuperregularPair R ε d (freeOut D cluster i) (freeIn D cluster (s i)) := by
  classical
  choose c hdc hc1 hc using hPair
  obtain ⟨hOverlap,hMin,hThreshold,hPairs⟩ := free_successor_pairs_of_centred_exceptional_budget
    D R cluster s m loss N r d δ ε c hd hdc hc1 hε hε1 hTol hm hN hr hCut hDegree hPay hSize hFree hc
  exact ⟨hOverlap,hMin,hThreshold,fun i => ⟨c i,hdc i,hc1 i,hPairs i⟩⟩

/-- The residual reduced pair in Claim 1 of Lemma 7.5 supplies
positive rectangles for the chord matching. -/
theorem chord_rectangles_of_uniform_residual_pair
    (H : Digraph W) (A B : Finset W) (e : ℕ) (δ d : ℝ)
    (hReg : IsUniform H δ A B) (hDensity : d ≤ density H A B) (hGap : δ < d)
    (hA : (A.card:ℝ)*δ ≤ (e:ℝ)+1) (hB : (B.card:ℝ)*δ ≤ (e:ℝ)+1) :
    ∀ X ⊆ A, ∀ Y ⊆ B, e < X.card → e < Y.card → 0 < incidences H X Y := by
  intro X hX Y hY hx hy
  have hx' : (e:ℝ)+1 ≤ X.card := by exact_mod_cast (show e+1 ≤ X.card by omega)
  have hy' : (e:ℝ)+1 ≤ Y.card := by exact_mod_cast (show e+1 ≤ Y.card by omega)
  have xs : X.Nonempty := card_pos.mp (Nat.zero_lt_of_lt hx)
  have ys : Y.Nonempty := card_pos.mp (Nat.zero_lt_of_lt hy)
  have h := uniform_incidences_lower H hReg hDensity hX hY (hA.trans hx') (hB.trans hy') xs ys
  have hx₂ : (0:ℝ) < X.card := by exact_mod_cast xs.card_pos
  have hy₂ : (0:ℝ) < Y.card := by exact_mod_cast ys.card_pos
  exact_mod_cast (mul_pos (mul_pos (sub_pos.mpr hGap) hx₂) hy₂).trans h

end OverfullWork.DirectedRobustExpansion
