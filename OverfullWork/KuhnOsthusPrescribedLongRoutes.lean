module

public import OverfullWork.KuhnOsthusPrescribedRoutes

@[expose] public section


/-! Corollary 4.15 for an arbitrary chain of at least four clusters.
A perfect matching removes one end of the chain and transports the
prescribed bijection to the new end. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A spanning disjoint bundle of paths through consecutive clusters,
with an arbitrary prescribed bijection between its two end clusters. -/
theorem kuhn_osthus_corollary_4_15 (G : Digraph V)
    (m r : ℕ) (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hr : 0 < r) (hCut : (m:ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ)))
    (q : ℕ) (A : ℕ → Finset V) (f : A 0 ≃ A (q+3))
    (hSize : ∀ i ≤ q+3, (A i).card = m)
    (hDis : ∀ i j, i ≤ q+3 → j ≤ q+3 → i ≠ j → Disjoint (A i) (A j))
    (hPairs : ∀ i < q+3, IsLowerSuperregularPair G ε d (A i) (A (i+1))) :
    ∃ P : ∀ i : Fin (q+4), A 0 ≃ A i.val,
      P 0 = Equiv.refl _ ∧ P (Fin.last (q+3)) = f ∧
      ∀ i : Fin (q+3), ∀ x : A 0, G.Adj (P i.castSucc x) (P i.succ x) := by
  induction q generalizing A with
  | zero =>
    obtain ⟨p,q,hp⟩ := kuhn_osthus_corollary_4_15_four_clusters G (A 0) (A 1) (A 2) (A 3)
      m r ε d f (hSize 0 (by decide)) (hSize 1 (by decide)) (hSize 2 (by decide))
      (hSize 3 (by decide)) (hDis 0 1 (by decide) (by decide) (by decide))
      (hDis 0 2 (by decide) (by decide) (by decide)) (hDis 0 3 (by decide) (by decide) (by decide))
      (hDis 1 2 (by decide) (by decide) (by decide))
      (hPairs 0 (by decide)) (hPairs 1 (by decide)) (hPairs 2 (by decide)) hε hGap hd hr hCut hBudget
    let P : ∀ i : Fin 4, A 0 ≃ A i.val :=
      Fin.cases (Equiv.refl _) (Fin.cases p (Fin.cases q (Fin.cases f (fun i => i.elim0))))
    refine ⟨P,rfl,rfl,?_⟩
    intro i x
    fin_cases i
    · exact (hp x).1
    · exact (hp x).2.1
    · exact (hp x).2.2
  | succ q ih =>
    have hη : 0 ≤ d-2*ε := by linarith
    have hη₁ : d-2*ε ≤ 1 := by linarith
    have hδ : 0 ≤ (d-ε)*(m:ℝ) := mul_nonneg (by linarith) (by positivity)
    have hScale : (d-2*ε)^14*((d-ε)*(m:ℝ)) ≤ (d-ε)*(m:ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hη hη₁) hδ
    have hMargin : (r:ℝ) ≤ (d-ε)*(m:ℝ) := by linarith only [hBudget,hScale,Nat.cast_nonneg (α := ℝ) r]
    obtain ⟨c,hc,_,hp⟩ := hPairs 0 (by omega)
    have hS₀ := hSize 0 (by omega)
    have hS₁ := hSize 1 (by omega)
    obtain ⟨e,he⟩ := hp.exists_perfect_matching G (A 0) (A 1) c ε r (hGap.trans_le hc) hr
      (hS₀.trans hS₁.symm) (by rwa [hS₀]) (by
        rw [hS₀]
        exact hMargin.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
    let B (i : ℕ) := A (i+1)
    obtain ⟨Q,hQ₀,hQEnd,hQ⟩ := ih B (e.symm.trans f)
      (fun i hi => hSize (i+1) (by omega))
      (fun i j hi hj hij => hDis (i+1) (j+1) (by omega) (by omega) (by omega))
      (fun i hi => hPairs (i+1) (by omega))
    let P : ∀ i : Fin (q+1+4), A 0 ≃ A i.val :=
      Fin.cases (Equiv.refl _) (fun i => e.trans (Q i))
    refine ⟨P,rfl,?_,?_⟩
    · change e.trans (Q (Fin.last (q+3))) = f
      rw [hQEnd]
      ext x
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        change G.Adj x (Q 0 (e x))
        rw [hQ₀]
        exact he x
      · intro x
        exact hQ j (e x)

end OverfullWork.DirectedRobustExpansion
