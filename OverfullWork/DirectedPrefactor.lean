module

public import OverfullWork.DirectedRobustCycleFactor

@[expose] public section


/-! Prefactor extensions in Lo–Patel §5. Close the missing arc
formally with a permutation, but require adjacency only off that arc. -/
namespace OverfullWork.DirectedPrefactor

variable {V : Type*}

/-- The successor permutation with the missing arc entering the fixed origin. -/
structure Prefactor (D : Digraph V) (origin : V) where
  successor : Equiv.Perm V
  adj : ∀ v, successor v ≠ origin → D.Adj v (successor v)

variable {D : Digraph V} {x : V}

def terminus (F : Prefactor D x) : V := F.successor.symm x

def ofFactor (σ : Equiv.Perm V) (hσ : ∀ v,D.Adj v (σ v)) (x : V) :
    Prefactor D x := ⟨σ,fun v _ => hσ v⟩

/-- Add the arc from the old terminus to z, removing the old arc into z.
Swapping the two targets also moves the formal missing arc. -/
noncomputable def extend (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (h : D.Adj (terminus F) z) : Prefactor D x := by
  classical
  refine ⟨F.successor.trans (Equiv.swap x z),?_⟩
  intro v hv
  change Equiv.swap x z (F.successor v) ≠ x at hv
  change D.Adj v (Equiv.swap x z (F.successor v))
  by_cases hx : F.successor v=x
  · have he : v=terminus F := F.successor.symm_apply_eq.mpr hx.symm |>.symm
    rw [hx,Equiv.swap_apply_left,he]
    exact h
  · by_cases hzv : F.successor v=z
    · exact False.elim (hv (by simp [hzv]))
    · rw [Equiv.swap_apply_of_ne_of_ne hx hzv]
      exact F.adj v hx

theorem terminus_extend (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (h : D.Adj (terminus F) z) : terminus (extend F z hz h)=F.successor.symm z := by
  classical
  change F.successor.symm ((Equiv.swap x z).symm x)=_
  simp

theorem predecessor_extend_same (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (h : D.Adj (terminus F) z) (w : V) (hwx : w ≠ x) (hwz : w ≠ z) :
    (extend F z hz h).successor.symm w=F.successor.symm w := by
  classical
  change F.successor.symm ((Equiv.swap x z).symm w)=_
  rw [Equiv.symm_swap,Equiv.swap_apply_of_ne_of_ne hwx hwz]

theorem predecessor_extend_at (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (h : D.Adj (terminus F) z) :
    (extend F z hz h).successor.symm z=terminus F := by
  classical
  change F.successor.symm ((Equiv.swap x z).symm z)=_
  simp [terminus]

theorem close_factor (F : Prefactor D x) (h : D.Adj (terminus F) x) :
    ∀ v,D.Adj v (F.successor v) := by
  intro v
  by_cases hx : F.successor v=x
  · have he : terminus F=v := F.successor.symm_apply_eq.mpr hx.symm
    simpa [he,hx] using h
  · exact F.adj v hx

end OverfullWork.DirectedPrefactor
