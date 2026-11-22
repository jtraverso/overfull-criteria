module

public import OverfullWork.KuhnOsthusResidualExceptionalInterval
public import OverfullWork.OsthusStadenPreparedSlices

@[expose] public section


/-! The four uniform quarters used in Kühn–Osthus Lemma 9.3.
They are chosen in the original host. The pair estimates survive
deletion of the already allocated arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- Simultaneously refine all fine clusters into four equal cells
and retain lower superregularity after deletions with bounded
semidegrees. The size threshold is uniform over the fine clusters. -/
theorem exists_universal_walk_quarters (C ε η d a : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (ha : 0 ≤ a) (hFloor : 2*ε ≤ d) (hTol : 2*(4*ε+a) ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type*} (G H : Digraph V) (_hHG : H ≤ G)
      (s : Equiv.Perm I) (A : I → Finset V) (m k : ℕ), 0 < m →
      (∀ i, N ≤ (A i).card) → (∀ i, (A i).card = 4*m) →
      (2*(Fintype.card V:ℝ) ≤ C*(4*m:ℕ)) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      ((k:ℝ) ≤ a*((m:ℝ)*η)) →
      (∀ i x, x ∈ A i → inDegree H x ≤ k ∧ outDegree H x ≤ k) →
      (∀ i, IsLowerSuperregularPair G ε d (A i) (A (s i))) →
      ∃ Q : I × Fin 4 → Finset V,
        (∀ i, (univ : Finset (Fin 4)).biUnion (fun j => Q (i,j)) = A i) ∧
        (∀ i, (Q i).card = m) ∧
        (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
        ∀ i j, IsLowerSuperregularPair (G \ H) η d (Q (i,j)) (Q (s i,j)) := by
  obtain ⟨N,hN⟩ := exists_ambient_uniform_refinement.{u,u} C ε hC hε 4 (by decide)
  refine ⟨N,?_⟩
  intro W _ I G H hHG s A m k hm hLarge hSize hProfiles hDis hBudget hLoss hPair
  let profiles := arcProfiles (fun _ : Unit => G)
  have hProfile (i : I) : (Fintype.card (Unit × Bool × W):ℝ) ≤ C*((A i).card:ℝ) := by
    rw [hSize]
    simpa only [Fintype.card_prod,Fintype.card_unit,Fintype.card_bool,one_mul,Nat.cast_mul,
      Nat.cast_ofNat] using hProfiles
  let R (i : I) := Classical.choice (hN profiles (A i) m (hLarge i) (hSize i) (hProfile i))
  let Q (i : I × Fin 4) := (R i.1).cells i.2
  refine ⟨Q,fun i => (R i).cover,fun i => (R i.1).size i.2,?_,?_⟩
  · rintro ⟨i,j⟩ ⟨i',j'⟩ hne
    by_cases he : i = i'
    · subst i'
      exact (R i).disjoint j j' (fun hj => hne (Prod.ext rfl hj))
    · exact (hDis i i' he).mono ((R i).subset j) ((R i').subset j')
  · intro i j
    have heA : (A i).card = 4*((Q (i,j)).card) := by rw [hSize,(R i).size j]
    have heB : (A (s i)).card = 4*((Q (s i,j)).card) := by rw [hSize,(R (s i)).size j]
    have hAnon : (Q (i,j)).Nonempty := card_pos.mp (by rwa [(R i).size j])
    have hBal : (Q (i,j)).card = (Q (s i,j)).card :=
      ((R i).size j).trans ((R (s i)).size j).symm
    have hTol' : 2*(max (2:ℝ) (4:ℕ)*ε+a) ≤ η := by
      simpa [max_eq_right (by norm_num : (2:ℝ) ≤ 4)] using hTol
    have hQBudget : (k:ℝ) ≤ a*(((Q (i,j)).card:ℝ)*η) := by
      change (k:ℝ) ≤ a*((((R i).cells j).card:ℝ)*η)
      rwa [(R i).size j]
    exact IsLowerSuperregularPair.on_residual_style_cells G H hHG (A i) (A (s i))
      (Q (i,j)) (Q (s i,j)) ((R i).subset j) ((R (s i)).subset j) hAnon hBal
      4 k d ε η a (by decide) hε.le hη hη1 ha hFloor heA heB
      ((R i).uniform j |>.inProfile ()) ((R (s i)).uniform j |>.outProfile ())
      hTol' hQBudget
      (fun x hx => (hLoss i x hx).2) (fun y hy => (hLoss (s i) y hy).1)
      (hPair i)

end OverfullWork.DirectedRobustExpansion
