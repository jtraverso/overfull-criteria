module

public import OverfullWork.KuhnOsthusPhysicalChordBalance
public import OverfullWork.KuhnOsthusChordMatchingLoads

@[expose] public section


/-! Realize one chord round and read its load in coarse cluster
coordinates. Only the physical walk arcs are allocated in this step. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V I J : Type*} [Fintype V]

/-- The footprint of a union is the union of the footprints.
The cluster predicate can be the coarse or the fine label. -/
theorem chord_footprint_sup (D C : Digraph V) (p : V → Prop) :
    finiteSatisfying (fun v => p v ∧ IncidentTo (D ⊔ C) v) =
      finiteSatisfying (fun v => p v ∧ IncidentTo D v) ∪
        finiteSatisfying (fun v => p v ∧ IncidentTo C v) := by
  ext v
  simp only [mem_finiteSatisfying,mem_union,IncidentTo,Digraph.sup_adj,exists_or]
  tauto

/-- Count vertices touched by a path system through its two endpoint
lists, allowing a vertex to occur in both lists. -/
theorem chord_footprint_le_endpoint_counts (D : Digraph V) (p : V → Prop) :
    (finiteSatisfying (fun v => p v ∧ IncidentTo D v)).card ≤
      (∑ e : Arc D, if p e.val.1 then (1:ℕ) else 0) +
      (∑ e : Arc D, if p e.val.2 then (1:ℕ) else 0) := by
  let S := finiteSatisfying (fun e : Arc D => p e.val.1)
  let T := finiteSatisfying (fun e : Arc D => p e.val.2)
  let A := S.image (fun e => e.val.1)
  let B := T.image (fun e => e.val.2)
  have hSub : finiteSatisfying (fun v => p v ∧ IncidentTo D v) ⊆ A ∪ B := by
    intro v hv
    obtain ⟨hp,⟨w,he⟩ | ⟨w,he⟩⟩ := (mem_finiteSatisfying (p := fun v => p v ∧ IncidentTo D v)).mp hv
    · exact mem_union_left _ (mem_image.mpr ⟨⟨(v,w),he⟩,mem_finiteSatisfying.mpr hp,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨⟨(w,v),he⟩,mem_finiteSatisfying.mpr hp,rfl⟩)
  calc
    _ ≤ (A ∪ B).card := card_le_card hSub
    _ ≤ A.card+B.card := card_union_le _ _
    _ ≤ S.card+T.card := Nat.add_le_add card_image_le card_image_le
    _ = _ := by simp only [S,T,finiteSatisfying,card_filter]

private theorem sum_coarse_load_le [Fintype J] (p : J → Prop) (load : J → ℕ) (cap : ℕ)
    (h : ∀ j, load j ≤ cap) :
    (∑ j, if p j then load j else 0) ≤ (finiteSatisfying p).card*cap := by
  change (∑ j, if p j then load j else 0) ≤ ((univ : Finset J).filter p).card*cap
  rw [←sum_filter]
  exact (sum_le_sum (fun j _ => h j)).trans_eq (by simp)

/-- Realize the rounded loads of a chord round. The ordinary
matchings and the contracted exceptional paths are already paired.
The output verifies the balance and footprint used in Claim 5. -/
theorem kuhn_osthus_chord_round_of_matching_loads {n b k m : ℕ} (scale ell : ℕ)
    (rank : V → Fin (n+2)) (quarter : V → Fin 4) (parent : Fin (n+2) → I)
    (s : Equiv.Perm I)
    (H C : Fin b × Fin 10 → Digraph V)
    (Q : Fin (n+2) × Fin 4 → Finset V)
    (M : ∀ j : Fin (n+2) × Fin 4, Fin k → Q j ≃ Q (finRotate (n+2) j.1,j.2))
    (w : Fin (n+2) → Fin b × Fin 10 → ℕ)
    (hM : 0 < k*m) (hQ : 110 < 10*b) (hWidth : 3*scale*(10*b) ≤ k*m)
    (hRoom : 3*(130*scale) ≤ m) (hSize : ∀ j, (Q j).card = m)
    (hCell : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hApart : ∀ j p q, p ≠ q → ∀ x, M j p x ≠ M j q x)
    (hLo : ∀ j p, 11*scale ≤ w j p) (hHi : ∀ j p, w j p ≤ 13*scale)
    (hTotal : ∀ j, (∑ a : Fin b,∑ i : Fin 10, w j (a,i)) = 4*(k*m))
    (hFibre : ∀ x, (finiteSatisfying (fun j => parent j = x)).card = ell)
    (hCluster : ∀ x, (finiteSatisfying (fun v => parent (rank v) = x)).card =
      (finiteSatisfying (fun v => parent (rank v) = s x)).card)
    (hPath : ∀ p, IsDirectedPathSystem (H p ⊔ C p))
    (hHC : ∀ p x y, (H p).Adj x y → ¬ (C p).Adj x y)
    (hDis : ∀ a i j, i ≠ j → Disjoint
      (finiteSatisfying (IncidentTo (H (a,i) ⊔ C (a,i))))
      (finiteSatisfying (IncidentTo (H (a,j) ⊔ C (a,j)))))
    (hTouch : ∀ p x, (finiteSatisfying (fun v => parent (rank v) = x ∧
      IncidentTo (H p ⊔ C p) v)).card ≤ scale)
    (hBalance : ∀ p x,
      (∑ j, if parent j = x then w j p else 0) +
        (∑ e : Arc (H p), if parent (rank e.val.1) = x then (1:ℕ) else 0) =
      (∑ j, if parent (finRotate (n+2) j) = s x then w j p else 0) +
        (∑ e : Arc (H p), if parent (rank e.val.2) = s x then (1:ℕ) else 0))
    (hBalanceC : ∀ p x, (∑ e : Arc (C p), if parent (rank e.val.1) = x then (1:ℕ) else 0) =
      ∑ e : Arc (C p), if parent (rank e.val.2) = s x then (1:ℕ) else 0) :
    let next := finRotate (n+2)
    let U := successorCellMatchingUnion Q (next.prodCongr (Equiv.refl (Fin 4))) M
    let cluster := parent ∘ rank
    ∃ D : Fin b × Fin 10 → Digraph V,
      (∀ x y, U.Adj x y ↔ ∃! p, (D p).Adj x y) ∧ (∀ p, D p ≤ U) ∧
      (∀ p x, IncidentTo (D p) x → ¬ IncidentTo (H p ⊔ C p) x) ∧
      ∀ p, let W := D p ⊔ (H p ⊔ C p)
        IsDirectedPathSystem W ∧
        (∀ x, (freeOut W cluster x).card = (freeIn W cluster (s x)).card) ∧
        ∀ x, (finiteSatisfying (fun v => cluster v = x ∧ IncidentTo W v)).card ≤
          scale+2*(ell*(13*scale)) := by
  intro next U cluster
  let P (a : Fin b) (i : Fin 10) := finiteSatisfying (IncidentTo (H (a,i) ⊔ C (a,i)))
  have hFine (j : Fin (n+2)) (a : Fin b) (i : Fin 10) :
      (P a i ∩ finiteSatisfying (fun v => rank v = j)).card ≤ scale := by
    refine (card_le_card (t := finiteSatisfying (fun v => parent (rank v) = parent j ∧
      IncidentTo (H (a,i) ⊔ C (a,i)) v)) ?_).trans (hTouch _ _)
    intro v hv
    obtain ⟨hp,hj⟩ := mem_inter.mp hv
    exact mem_finiteSatisfying.mpr ⟨congrArg parent
      ((mem_finiteSatisfying (p := fun v => rank v = j)).mp hj),
      (mem_finiteSatisfying (p := IncidentTo (H (a,i) ⊔ C (a,i)))).mp hp⟩
  obtain ⟨D,hPart,hLe,hStep,hD,hAvoid,hCount⟩ :=
    realize_physical_walk_bank scale rank quarter Q M (fun j a i => w j (a,i)) P hM hQ hWidth
      hRoom hSize hCell hApart (fun j a i => hLo j (a,i)) (fun j a i => hHi j (a,i)) hTotal hDis
      (fun j a i => (Nat.add_le_add (hFine j a i) (hFine (next j) a i)).trans (by omega))
  have hAway (p : Fin b × Fin 10) (x : V) (hx : IncidentTo (D p) x) :
      ¬ IncidentTo (H p ⊔ C p) x := fun he =>
    hAvoid p.1 p.2 x hx (mem_finiteSatisfying.mpr he)
  refine ⟨D,hPart,hLe,hAway,?_⟩
  intro p W
  have hW : IsDirectedPathSystem W :=
    (hD p.1 p.2).sup_of_disjoint_vertices (hPath p) (hAway p)
  refine ⟨hW,?_,?_⟩
  · exact free_successor_pairs_after_realized_chords (D p) (H p) (C p) rank next parent s (fun j => w j p)
      (hStep p) (fun j => hCount j p.1 p.2)
      (fun x y hd hc => hAway p x (Or.inl ⟨y,hd⟩) (Or.inl ⟨y,hc⟩))
      (hHC p) hW hCluster (hBalance p) (hBalanceC p)
  · intro x
    have hOut (v : Fin (n+2) → ℕ) (hv : ∀ j, v j ≤ 13*scale) :
        (∑ j, if parent j = x then v j else 0) ≤ ell*(13*scale) := by
      have hle := sum_coarse_load_le (fun j => parent j = x) v (13*scale) hv
      rw [hFibre x] at hle
      exact hle
    have hIncoming : (∑ j, if parent (next j) = x then w j p else 0) ≤ ell*(13*scale) := by
      have he := Equiv.sum_comp next (fun j => if parent j = x then w (next.symm j) p else 0)
      simp only [Equiv.symm_apply_apply] at he
      rw [he]
      exact hOut _ (fun j => hHi (next.symm j) p)
    obtain ⟨hout,hin⟩ := arc_loads_from_walk_realization (D p) rank next parent
      (fun j => w j p) (hStep p) (fun j => hCount j p.1 p.2)
    have hWalk : (finiteSatisfying (fun v => cluster v = x ∧ IncidentTo (D p) v)).card ≤
        2*(ell*(13*scale)) := by
      refine (chord_footprint_le_endpoint_counts (D p) (fun v => parent (rank v) = x)).trans ?_
      rw [hout,hin,two_mul]
      exact Nat.add_le_add (hOut _ (fun j => hHi j p)) hIncoming
    change (finiteSatisfying (fun v => cluster v = x ∧ IncidentTo (D p ⊔ (H p ⊔ C p)) v)).card ≤ _
    rw [chord_footprint_sup]
    exact (card_union_le _ _).trans ((Nat.add_le_add hWalk (hTouch p x)).trans_eq (Nat.add_comm _ _))

end OverfullWork.DirectedRobustExpansion
