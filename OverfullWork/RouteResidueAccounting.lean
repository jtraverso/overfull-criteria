module

public import OverfullWork.ColourCertificateExchange

@[expose] public section


/-! # Missing pairs and exact internal residue after route recoloring

Each legal route exchange removes exactly its two missing endpoints.
Good removed copies preserve the residue degree cap and protected rows.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 20000000

theorem goodMatching_internal (L R : MultiGraph V) (A : Finset V) (h : ℕ)
    (x y : V) (hCross : ¬(x ∈ A ↔ y ∈ A)) : (L.goodMatching R A h).mult s(x,y)=0 := by
  change (L.internalPart A).mult s(x,y)-_=0
  rw [internalPart_mult,if_neg hCross]
  exact Nat.zero_sub _

theorem goodMatching_residue_room (L R : MultiGraph V) (A : Finset V) (h : ℕ) (v : V)
    (hPos : 0 < (L.goodMatching R A h).degree v) : R.degree v < h := by
  by_contra hn
  have hv : v ∈ R.highVertices h := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hz := subtract_incidentOn_degree_zero (L.internalPart A) (R.highVertices h) v hv
  change (L.goodMatching R A h).degree v=0 at hz
  omega

namespace PartialColouring.RouteInput
variable {M : MultiGraph V} {k : ℕ} {P : M.PartialColouring k} {i : Fin k} {a b : V}

theorem missingSet_exact (s : RouteInput P i a b) :
    s.result.colouring.missingSet univ i=((P.colouring.missingSet univ i).erase a).erase b := by
  ext v
  simp only [EdgeColoring.missingSet,mem_filter,mem_univ,true_and,mem_erase]
  rw [s.selected_degree_change v]
  by_cases hva : v=a
  · subst v;simp [s.first_missing]
  by_cases hvb : v=b
  · subst v;simp [s.last_missing]
  · simp [hva,hvb]

theorem missingPalette_change (s : RouteInput P i a b) (v : V) :
    (s.result.colouring.missingPalette v).card+(if v=a then 1 else 0)+(if v=b then 1 else 0)=
      (P.colouring.missingPalette v).card := by
  have hP := P.colouring.missingPalette_card_add_degree v
  have hQ := s.result.colouring.missingPalette_card_add_degree v
  have hd := s.degree_change v
  omega

theorem total_missing_drop (s : RouteInput P i a b) :
    (∑ v, (P.colouring.missingPalette v).card)=(∑ v, (s.result.colouring.missingPalette v).card)+2 := by
  have hP := sum_congr (s₁ := (univ : Finset V)) rfl
    (fun v _ => P.colouring.missingPalette_card_add_degree v)
  have hQ := sum_congr (s₁ := (univ : Finset V)) rfl
    (fun v _ => s.result.colouring.missingPalette_card_add_degree v)
  simp only [sum_add_distrib,P.graph.sum_degrees_eq_twice_edgeCount,
    s.result.graph.sum_degrees_eq_twice_edgeCount] at hP hQ
  have hSize := s.size_change
  omega

theorem internal_residue (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) :
    (s.result.available.internalPart A)=(P.available.internalPart A).addCopies s.removed := by
  change ((M.subtractCopies ((P.graph.subtractCopies s.removed).addCopies s.added)).internalPart A)=_
  exact remainder_internal_exchange M P.graph s.removed s.added A P.le
    (fun e => (s.removed_le e).trans (P.colouring.col_le_mult e i)) hR hAdd

theorem internal_residue_size (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) :
    (s.result.available.internalPart A).edgeCount=(P.available.internalPart A).edgeCount+s.rounds+1 := by
  rw [s.internal_residue A hR hAdd,edgeCount_addCopies,s.removed_count]
  omega

theorem internal_residue_cap (s : RouteInput P i a b) (A : Finset V) (h : ℕ)
    (hGood : ∀ e, s.removed.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h) :
    ∀ v, (s.result.available.internalPart A).degree v ≤ h := by
  have hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0 := by
    intro x y hxy
    have hh := hGood s(x,y)
    rw [goodMatching_internal _ _ _ _ x y hxy] at hh
    omega
  intro v
  rw [s.internal_residue A hR hAdd,degree_addCopies]
  have hOne := s.removed_matching v
  by_cases hPos : 0 < s.removed.degree v
  · have hLe := ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).degree_le_of_mult_le
      s.removed hGood v
    have hRoom := goodMatching_residue_room (P.colouring.colourGraph i) (P.available.internalPart A) A h v
      (lt_of_lt_of_le hPos hLe)
    omega
  · have hh := hCap v
    omega

theorem internal_residue_protected (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0)
    (v : V) (hv : s.removed.degree v=0) :
    (s.result.available.internalPart A).degree v=(P.available.internalPart A).degree v := by
  rw [s.internal_residue A hR hAdd,degree_addCopies,hv,Nat.add_zero]

end PartialColouring.RouteInput
end SimpleGraph.MultiGraph
