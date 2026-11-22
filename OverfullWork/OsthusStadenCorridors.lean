module

public import OverfullWork.FactorMergeBatch

@[expose] public section


/-! The black intervals and the bridges across consecutive red
clusters in Osthus–Staden §5.11. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Iterating the matchings of a corridor maps the first cell onto its last cell. -/
theorem iterate_image_of_cluster_matchings (σ : Equiv.Perm V) (A : ℕ → Finset V) (n : ℕ)
    (h : ∀ j < n, (A j).image σ = A (j+1)) :
    (A 0).image ((σ : V → V)^[n]) = A n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ',←image_image,ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    exact h n (Nat.lt_succ_self n)

theorem orbit_hits_of_cluster_interval (σ : Equiv.Perm V) (A : ℕ → Finset V) (n j q : ℕ)
    (hj : j ≤ n) (hq : q ≤ n) (h : ∀ t < n, (A t).image σ = A (t+1))
    {v : V} (hv : v ∈ A j) : touchesCut σ (A q) v := by
  have hReach (i : ℕ) (hi : i ≤ n) :
      (A 0).image ((σ : V → V)^[i]) = A i :=
    iterate_image_of_cluster_matchings σ A i (fun t ht => h t (ht.trans_le hi))
  rw [←hReach j hj] at hv
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
  let z := (σ : V → V)^[q] x
  have hz : z ∈ A q := hReach q hq ▸ mem_image.mpr ⟨x,hx,rfl⟩
  exact ⟨z,hz,by rw [←Equiv.Perm.coe_pow,show z = (σ^q) x by simp [z,Equiv.Perm.coe_pow]]
                 rw [Equiv.Perm.sameCycle_pow_left,Equiv.Perm.sameCycle_pow_right]⟩

/-- Each factor orbit reaches a cut if it hits a black interval
and one source cell is selected in every interval. -/
theorem cover_of_selected_black_intervals {I : Type*} (σ : Equiv.Perm V)
    (A : I → ℕ → Finset V) (n q : I → ℕ) (hq : ∀ i, q i ≤ n i)
    (hBlack : ∀ i t, t < n i → (A i t).image σ = A i (t+1))
    (hHit : ∀ v, ∃ w, σ.SameCycle v w ∧ ∃ i t, t ≤ n i ∧ w ∈ A i t) :
    ∀ v, ∃ i, touchesCut σ (A i (q i)) v := by
  intro v
  obtain ⟨w,hvw,i,t,ht,hw⟩ := hHit v
  exact ⟨i,(touchesCut_congr hvw).mpr
    (orbit_hits_of_cluster_interval σ (A i) (n i) t (q i) ht (hq i) (hBlack i) hw)⟩

omit [Fintype V] in
/-- A proper subset of outgoing-red vertices leaves an old matching edge
from the outgoing-red cluster to its successor cluster. -/
theorem exists_unmarked_transition (σ : Equiv.Perm V) (A B red : Finset V)
    (hSize : red.card < A.card)
    (hNext : ∀ x ∈ A, x ∉ red → σ x ∈ B) :
    ∃ x ∈ A, σ x ∈ B := by
  by_contra! h
  have hSub : A ⊆ red := fun x hx => by
    by_contra hr
    exact h x hx (hNext x hx hr)
  exact (not_le_of_gt hSize) (card_le_card hSub)

/-- A winding corridor has one red transition with an available original
arc. All other transitions are perfect matchings. -/
theorem bridge_chain_of_winding_corridor {I : Type*} (σ : Equiv.Perm V)
    (S : I → Finset V) (A : ℕ → Finset V) (n p : ℕ) (hp : p < n)
    (hBlack : ∀ j < n, j ≠ p → (A j).image σ = A (j+1))
    (hRed : ∃ x ∈ A p, σ x ∈ A (p+1))
    (hOff : ∀ j < n, ∀ x ∈ A j, ∀ i, x ∉ S i) :
    ∃ x ∈ A 0, ∃ y ∈ A n, ∃ L : List V,
      L.head? = some x ∧ L.getLast? = some y ∧ x ∈ L ∧ y ∈ L ∧
      L.IsChain (fun a b => (∀ i, a ∉ S i) ∧ σ a = b) := by
  obtain ⟨w,hw,hw'⟩ := hRed
  have hReach := iterate_image_of_cluster_matchings σ A p
    (fun j hj => hBlack j (hj.trans hp) (ne_of_lt hj))
  rw [←hReach] at hw
  obtain ⟨x,hx,hxw⟩ := mem_image.mp hw
  let f : V → V := σ
  have hAlong (j : ℕ) (hj : j ≤ n) : f^[j] x ∈ A j := by
    induction j with
    | zero => exact hx
    | succ j ih =>
      rw [iterate_succ_apply']
      by_cases h : j = p
      · subst j
        rw [show f^[p] x = w from hxw]
        exact hw'
      · rw [←hBlack j (by omega) h]
        exact mem_image.mpr ⟨_,ih (Nat.le_of_succ_le hj),rfl⟩
  let L := List.ofFn (fun j : Fin (n+1) => f^[j.val] x)
  have hLen : L.length = n+1 := List.length_ofFn
  have hAt (j : ℕ) (hj : j < L.length) : L[j] = f^[j] x := by simp only [L,List.getElem_ofFn]
  let y := f^[n] x
  refine ⟨x,hx,y,hAlong n le_rfl,L,?_,?_,?_,?_,?_⟩
  · rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega : 0 < L.length),hAt]
    rfl
  · rw [List.getLast?_eq_getElem?]
    have he : L.length-1 = n := by omega
    rw [List.getElem?_eq_getElem (by omega : L.length-1 < L.length),hAt,he]
  · exact List.mem_ofFn.mpr ⟨0,rfl⟩
  · exact List.mem_ofFn.mpr ⟨Fin.last n,rfl⟩
  · apply List.isChain_iff_getElem.mpr
    intro j hj
    rw [hAt,hAt]
    exact ⟨hOff j (by omega) _ (hAlong j (by omega)),(iterate_succ_apply' f j x).symm⟩

omit [Fintype V] in
/-- The red classes and exceptional vertices reach a black vertex
along an arc of their factor, possibly after one extra step. -/
theorem every_orbit_hits_black (σ : Equiv.Perm V) (black redIn redOut : Set V)
    (hIn : ∀ v ∈ redIn, σ v ∈ black)
    (hOut : ∀ v ∈ redOut, σ.symm v ∈ black)
    (hExceptional : ∀ v, v ∉ black → v ∉ redIn → v ∉ redOut →
      σ v ∈ black ∨ σ v ∈ redIn ∨ σ v ∈ redOut) :
    ∀ v, ∃ w ∈ black, σ.SameCycle v w := by
  have hCore (v : V) (h : v ∈ black ∨ v ∈ redIn ∨ v ∈ redOut) :
      ∃ w ∈ black, σ.SameCycle v w := by
    rcases h with h | h | h
    · exact ⟨v,h,Equiv.Perm.SameCycle.refl σ v⟩
    · exact ⟨σ v,hIn v h,(Equiv.Perm.SameCycle.refl σ v).apply_right⟩
    · exact ⟨σ.symm v,hOut v h,(Equiv.Perm.SameCycle.refl σ v).symm_apply_right⟩
  intro v
  by_cases h : v ∈ black ∨ v ∈ redIn ∨ v ∈ redOut
  · exact hCore v h
  · obtain ⟨w,hw,hs⟩ := hCore (σ v) (hExceptional v (fun h' => h (Or.inl h'))
      (fun h' => h (Or.inr (Or.inl h'))) (fun h' => h (Or.inr (Or.inr h'))))
    exact ⟨w,hw,hs.of_apply_left⟩

/-- The bridge starts in the target cell of one cut and finishes in
the source cell of the next. Its old arcs avoid the selected cuts. -/
theorem bridge_between_selected_pairs {I : Type*} (σ : Equiv.Perm V)
    (S : I → Finset V) (i j : I) (A : ℕ → Finset V) (n p : ℕ) (hp : p < n)
    (hStart : A 0 = (S i).image σ) (hEnd : A n = S j)
    (hBlack : ∀ l < n, l ≠ p → (A l).image σ = A (l+1))
    (hRed : ∃ x ∈ A p, σ x ∈ A (p+1))
    (hOff : ∀ l < n, ∀ x ∈ A l, ∀ i, x ∉ S i) :
    ∃ x y, touchesCut σ (S i) x ∧ touchesCut σ (S j) y ∧
      ∃ L : List V, x ∈ L ∧ y ∈ L ∧ L.IsChain (fun a b => (∀ c, a ∉ S c) ∧ σ a = b) := by
  obtain ⟨x,hx,y,hy,L,_,_,hxL,hyL,hCh⟩ :=
    bridge_chain_of_winding_corridor σ S A n p hp hBlack hRed hOff
  rw [hStart] at hx
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  rw [hEnd] at hy
  exact ⟨σ u,y,(touchesCut_congr ((Equiv.Perm.SameCycle.refl σ u).apply_right)).mp
    (touchesCut_of_mem σ hu),touchesCut_of_mem σ hy,L,hxL,hyL,hCh⟩

omit [Fintype V] in
/-- A common old orbit, for example through an exceptional vertex,
connects the two selected pairs without changing any bridge arc. -/
theorem bridge_of_exceptional_vertex {I : Type*} (σ : Equiv.Perm V) (S : I → Finset V)
    (i j : I) (x : V) (hPred : touchesCut σ (S i) (σ.symm x))
    (hNext : touchesCut σ (S j) (σ x)) :
    ∃ a b, touchesCut σ (S i) a ∧ touchesCut σ (S j) b ∧
      ∃ L : List V, a ∈ L ∧ b ∈ L ∧ L.IsChain (fun a b => (∀ c, a ∉ S c) ∧ σ a = b) := by
  have h := Equiv.Perm.SameCycle.refl σ x
  exact ⟨x,x,(touchesCut_congr h.symm_apply_left).mp hPred,(touchesCut_congr h.apply_right).mpr hNext,
    [x],by simp,by simp,.singleton _⟩

end OverfullWork.DirectedRobustExpansion
