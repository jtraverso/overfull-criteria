module

public import OverfullWork.GeneralCopies
public import OverfullWork.MultigraphColouring

@[expose] public section


/-! # Recover a proper coloring of labelled copies from weighted counts

This is the reverse of GeneralCopies.edgeColoring. Each bundle uses a
finite equivalence between its copy indices and its occupied colors.
Thus the existing edge-family Kempe API can work on the actual copies.
-/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 6000000

theorem bundle_colour_le_one (C : M.EdgeColoring k) (e : Sym2 V) (i : Fin k) : C.col e i ≤ 1 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hh := single_le_sum (s := univ.filter fun e : Sym2 V => a ∈ e)
      (f := fun e => C.col e i) (fun _ _ => Nat.zero_le _)
      (mem_filter.mpr ⟨mem_univ _,by simp⟩ : s(a,b) ∈ univ.filter fun e : Sym2 V => a ∈ e)
    exact hh.trans (C.proper a i)

def occupiedColours (C : M.EdgeColoring k) (e : Sym2 V) : Finset (Fin k) :=
  univ.filter (fun i => C.col e i=1)

theorem occupiedColours_card (C : M.EdgeColoring k) (e : Sym2 V) :
    (C.occupiedColours e).card = M.mult e := by
  rw [occupiedColours,card_eq_sum_ones,sum_filter]
  calc
    _ = ∑ i, C.col e i := by
      apply sum_congr rfl
      intro i _
      have hh := C.bundle_colour_le_one e i
      split_ifs <;> omega
    _ = _ := C.sum_col e

theorem exists_labelled_copy_colouring (C : M.EdgeColoring k) :
    ∃ c : GeneralCopies.Copies M → Fin k,
      ShannonColouring.IsProperEdgeColouring (GeneralCopies.ends M) c ∧
      ∀ p, C.col p.1 (c p)=1 := by
  let E : ∀ e : Sym2 V, Fin (M.mult e) ≃ ↥(C.occupiedColours e) := fun e =>
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,C.occupiedColours_card])
  let c : GeneralCopies.Copies M → Fin k := fun p => (E p.1 p.2).val
  have hc : ∀ p, C.col p.1 (c p)=1 := by
    intro p
    exact (mem_filter.mp (E p.1 p.2).property).2
  refine ⟨c,?_,hc⟩
  intro p q hpq hInc hcol
  obtain ⟨v,hp,hq⟩ := hInc
  have hpv := (GeneralCopies.incident_iff M p v).mp hp
  have hqv := (GeneralCopies.incident_iff M q v).mp hq
  have hpp : 0 < C.col p.1 (c p) := by rw [hc p];omega
  have hqp : 0 < C.col q.1 (c p) := by rw [hcol,hc q];omega
  have heq := C.eq_of_incident_positive hpv hqv hpp hqp
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  change e=f at heq
  subst f
  have hE : E e i=E e j := Subtype.ext hcol
  have hij := (E e).injective hE
  subst j
  exact hpq rfl

end SimpleGraph.MultiGraph.EdgeColoring

namespace SimpleGraph.MultiGraph.GeneralCopies
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
set_option maxHeartbeats 6000000

theorem colourable_of_labelled_family (M : MultiGraph V) (ends : I → V × V) (k : ℕ)
    (hFibre : ∀ e, (univ.filter (fun i => s((ends i).1,(ends i).2)=e)).card = M.mult e)
    (c : I → Fin k) (hc : ShannonColouring.IsProperEdgeColouring ends c) :
    Nonempty (M.EdgeColoring k) := by
  let w := fun (e : Sym2 V) (j : Fin k) =>
    ((univ.filter (fun i => c i=j)).filter (fun i => s((ends i).1,(ends i).2)=e)).card
  refine ⟨{
    col := w
    sum_col := ?_
    proper := ?_
  }⟩
  · intro e
    have hf : ∀ j, w e j =
        ((univ.filter (fun i => s((ends i).1,(ends i).2)=e)).filter (fun i => c i=j)).card := by
      intro j
      apply congrArg Finset.card
      ext i
      simp [and_comm,w]
    simp_rw [hf]
    rw [sum_card_fiberwise_eq_card_filter]
    simp only [mem_univ,filter_true]
    exact hFibre e
  · intro v j
    dsimp only [w]
    rw [sum_card_fiberwise_eq_card_filter]
    apply card_le_one.mpr
    intro e he f hf
    simp only [mem_filter,mem_univ,true_and] at he hf
    by_contra hne
    apply hc e f hne
      ⟨v,by simpa only [ShannonColouring.Incident,Sym2.mem_iff,eq_comm] using he.2,
        by simpa only [ShannonColouring.Incident,Sym2.mem_iff,eq_comm] using hf.2⟩
    exact he.1.trans hf.1.symm

end SimpleGraph.MultiGraph.GeneralCopies
