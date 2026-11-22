module

public import OverfullWork.DirectedMultigraphFactors
public import OverfullWork.SuperregularDegreeDemands

@[expose] public section


/-! Assemble regular spanning subgraphs from the balanced successor pairs
and the prescribed red arcs of Osthus–Staden §5.10. -/
namespace OverfullWork.DirectedMultigraphFactors
open Finset DirectedRobustExpansion
open scoped Classical
variable {W I E : Type*} [Fintype W] [Fintype I] [Fintype E]

theorem balanced_cluster_deficits (p q : W → ℕ) (k : ℕ)
    (hp : ∀ v, p v ≤ k) (hq : ∀ v, q v ≤ k) (hBal : (∑ v,p v) = ∑ v,q v) :
    (∑ v : W,(k-p v)) = ∑ v : W,(k-q v) := by
  have hP : (∑ v : W,(k-p v))+(∑ v,p v) = ∑ _ : W,k := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun v _ => Nat.sub_add_cancel (hp v)
  have hQ : (∑ v : W,(k-q v))+(∑ v,q v) = ∑ _ : W,k := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun v _ => Nat.sub_add_cancel (hq v)
  omega

noncomputable def successorPairArcs (s : Equiv.Perm I) (H : I → Digraph W) :
    (E ⊕ (I × W)) → (E ⊕ (I × W)) → ℕ
  | .inr (i,v), .inr (j,w) => if j = s i ∧ (H i).Adj v w then 1 else 0
  | _, _ => 0

/-- Complete a reserved arc set to a regular matrix using one subdigraph
of each successor pair, and partition the completed matrix into 1-factors. -/
theorem exists_cluster_factorization (s : Equiv.Perm I)
    (red : (E ⊕ (I × W)) → (E ⊕ (I × W)) → ℕ) (D : I → Digraph W) (k : ℕ)
    (hOut : ∀ x, ∑ y,red x y ≤ k) (hIn : ∀ y, ∑ x,red x y ≤ k)
    (hExOut : ∀ z : E, (∑ y,red (.inl z) y) = k)
    (hExIn : ∀ z : E, (∑ x,red x (.inl z)) = k)
    (hPair : ∀ i : I, ∃ H : Digraph W, H ≤ D i ∧
      (∀ v, outDegree H v = k - ∑ y, red (.inr (i,v)) y) ∧
      ∀ w, inDegree H w = k - ∑ x, red x (.inr (s i,w))) :
    ∃ F : Fin k → Equiv.Perm (E ⊕ (I × W)), ∃ H : I → Digraph W,
      (∀ i, H i ≤ D i) ∧ ∀ x y,
      ((univ : Finset (Fin k)).filter (fun j => F j x = y)).card =
        red x y + successorPairArcs s H x y := by
  choose H hH hHo hHi using hPair
  let B : (E ⊕ (I × W)) → (E ⊕ (I × W)) → ℕ := successorPairArcs s H
  have ho (i : I) (v : W) : (∑ y,B (.inr (i,v)) y) = outDegree (H i) v := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,B,successorPairArcs,sum_const_zero,zero_add]
    calc
      _ = ∑ j : I, if j = s i then ∑ w : W, if (H i).Adj v w then (1:ℕ) else 0 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases h : j = s i <;> simp [h]
      _ = _ := by simp only [sum_ite_eq',mem_univ,if_true,outDegree,card_filter]
  have hi (j : I) (w : W) : (∑ x,B x (.inr (j,w))) = inDegree (H (s.symm j)) w := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,B,successorPairArcs,sum_const_zero,zero_add]
    calc
      _ = ∑ i : I, if s.symm j = i then ∑ v : W, if (H i).Adj v w then (1:ℕ) else 0 else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases h : s.symm j = i
        · simp [s.symm_apply_eq.mp h]
        · simp [h,mt s.symm_apply_eq.mpr h]
      _ = _ := by simp only [sum_ite_eq,mem_univ,if_true,inDegree,inNeighbours,card_filter]
  have hRow (x : E ⊕ (I × W)) : (∑ y,(red x y+B x y)) = k := by
    rw [sum_add_distrib]
    rcases x with z | ⟨i,v⟩
    · simpa [B,successorPairArcs] using hExOut z
    · rw [ho,hHo,add_comm,Nat.sub_add_cancel (hOut _)]
  have hColumn (y : E ⊕ (I × W)) : (∑ x,(red x y+B x y)) = k := by
    rw [sum_add_distrib]
    rcases y with z | ⟨j,w⟩
    · simpa [B,successorPairArcs] using hExIn z
    · rw [hi,hHi,s.apply_symm_apply,add_comm,Nat.sub_add_cancel (hIn _)]
  obtain ⟨F,hF⟩ := exists_factorization (fun x y => red x y+B x y) k hRow hColumn
  refine ⟨F,H,hH,fun x y => ?_⟩
  convert hF x y using 1
  congr 1
  ext j
  simp

/-- On the balanced clusters of §5.10, all needed local subdigraphs exist
under uniform dense-pair bounds. -/
theorem exists_dense_cluster_factorization (s : Equiv.Perm I)
    (red : (E ⊕ (I × W)) → (E ⊕ (I × W)) → ℕ) (D : I → Digraph W) (k e L : ℕ) (b : ℝ)
    (hOut : ∀ x, ∑ y,red x y ≤ k) (hIn : ∀ y, ∑ x,red x y ≤ k)
    (hExOut : ∀ z : E, (∑ y,red (.inl z) y) = k)
    (hExIn : ∀ z : E, (∑ x,red x (.inl z)) = k)
    (hBal : ∀ i : I, (∑ v : W,∑ y,red (.inr (i,v)) y) =
      ∑ w : W,∑ x,red x (.inr (s i,w)))
    (hRedOut : ∀ i : I, ∀ v : W, (∑ y,red (.inr (i,v)) y) ≤ k-L)
    (hRedIn : ∀ i : I, ∀ w : W, (∑ x,red x (.inr (i,w))) ≤ k-L)
    (hLk : L ≤ k) (hb : 0 ≤ b) (hTwo : k ≤ 2*L)
    (hL : 2*b*(Fintype.card W:ℝ) ≤ 3*(L:ℝ))
    (hU : (k:ℝ) ≤ b*(Fintype.card W:ℝ))
    (hSlack : b*(Fintype.card W:ℝ)-(L:ℝ) ≤ 2*(b*(Fintype.card W:ℝ)-(k:ℝ)))
    (hPairOut : ∀ i v, k+2*e ≤ outDegree (D i) v)
    (hPairIn : ∀ i v, k+2*e ≤ inDegree (D i) v)
    (hRect : ∀ i, ∀ S Y : Finset W, e ≤ S.card → e ≤ Y.card →
      b*(S.card:ℝ)*(Y.card:ℝ) ≤ (incidences (D i) S Y:ℝ)) :
    ∃ F : Fin k → Equiv.Perm (E ⊕ (I × W)), ∃ H : I → Digraph W,
      (∀ i, H i ≤ D i) ∧ ∀ x y,
      ((univ : Finset (Fin k)).filter (fun j => F j x = y)).card = red x y + successorPairArcs s H x y := by
  apply exists_cluster_factorization s red D k hOut hIn hExOut hExIn
  intro i
  let p := fun v : W => ∑ y,red (.inr (i,v)) y
  let q := fun w : W => ∑ x,red x (.inr (s i,w))
  apply exists_demands_of_dense_pair (D i) e L k b (fun v => k-p v) (fun w => k-q w)
    hb hTwo hL hU hSlack (hPairOut i) (hPairIn i) (hRect i)
  · intro v
    have h : p v ≤ k-L := hRedOut i v
    omega
  · intro w
    have h : q w ≤ k-L := hRedIn (s i) w
    omega
  · exact balanced_cluster_deficits p q k (fun v => hOut (.inr (i,v)))
      (fun w => hIn (.inr (s i,w))) (hBal i)

end OverfullWork.DirectedMultigraphFactors
