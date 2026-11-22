module

public import OverfullWork.ProtectedResidueBundles
public import OverfullWork.GeneralCopies

@[expose] public section


/-! # Select actual residue copies and preserve the protected part

Stage I uses an actual bounded submultigraph on one side. The protected
incident residue at the end of the good run is exactly the initial one.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem exists_subcopies_with_edgeCount (M : MultiGraph V) (q : ℕ) (hq : q ≤ M.edgeCount) :
    ∃ J : MultiGraph V, (∀ e, J.mult e ≤ M.mult e) ∧ J.edgeCount=q := by
  obtain ⟨f,hf,hSum⟩ := bounded_allocation M.mult q hq
  let J : MultiGraph V := {
    mult := f,
    loopless := fun e he => by have hh := hf e;rw [M.loopless e he] at hh;omega
  }
  exact ⟨J,hf,hSum⟩

theorem edgeCount_subtract_add (M J : MultiGraph V) (hJ : ∀ e, J.mult e ≤ M.mult e) :
    (M.subtractCopies J).edgeCount+J.edgeCount=M.edgeCount := by
  change (∑ e, (M.mult e - J.mult e))+(∑ e, J.mult e)=(∑ e, M.mult e)
  rw [←sum_add_distrib]
  exact sum_congr rfl (fun e _ => Nat.sub_add_cancel (hJ e))

theorem exists_balanced_stage_one_selection (L R : MultiGraph V) (E : Finset V)
    (hEqual : L.edgeCount=R.edgeCount) :
    ∃ J : MultiGraph V, (∀ e, J.mult e ≤ L.mult e) ∧
      J.edgeCount=(R.incidentOn E).edgeCount ∧
      (L.subtractCopies J).edgeCount=(R.subtractCopies (R.incidentOn E)).edgeCount ∧
      ∀ v ∈ E, (R.subtractCopies (R.incidentOn E)).degree v=0 := by
  have hBound : (R.incidentOn E).edgeCount ≤ R.edgeCount :=
    sum_le_sum (fun e _ => R.incidentOn_le E e)
  obtain ⟨J,hJ,hCount⟩ := L.exists_subcopies_with_edgeCount (R.incidentOn E).edgeCount (by omega)
  have hLeft := edgeCount_subtract_add L J hJ
  have hRight := edgeCount_subtract_add R (R.incidentOn E) (R.incidentOn_le E)
  exact ⟨J,hJ,hCount,by omega,fun v hv => subtract_incidentOn_degree_zero R E v hv⟩

namespace PartialColouring.GoodRouteRun
variable {M : MultiGraph V} {k : ℕ} {A E : Finset V} {h ell : ℕ}
variable {P Q : M.PartialColouring k} {n t : ℕ}

theorem protected_incident_residue (run : GoodRouteRun A E h ell P Q n t) :
    (Q.available.internalPart A).incidentOn E=(P.available.internalPart A).incidentOn E := by
  apply ext_mult
  intro e
  change (if ∃ v ∈ E, v ∈ e then _ else 0)=(if ∃ v ∈ E, v ∈ e then _ else 0)
  split_ifs with he
  · obtain ⟨v,hv,hve⟩ := he
    induction e using Sym2.inductionOn with
    | hf x y =>
      rcases Sym2.mem_iff.mp hve with hx|hy
      · subst x
        exact run.protected_internal_bundle v hv y
      · subst y
        rw [Sym2.eq_swap]
        exact run.protected_internal_bundle v hv x
  · rfl

theorem protected_right_incident_bound (run : GoodRouteRun A E h ell P Q n t) :
    ((Q.available.restrict Aᶜ).incidentOn E).edgeCount ≤ (P.available.internalPart A).edgeCount := by
  have hLe : ∀ e, ((Q.available.restrict Aᶜ).incidentOn E).mult e ≤
      ((Q.available.internalPart A).incidentOn E).mult e := by
    intro e
    change (if ∃ v ∈ E, v ∈ e then (if e.toFinset ⊆ Aᶜ then Q.available.mult e else 0) else 0) ≤ _
    change _ ≤ (if ∃ v ∈ E, v ∈ e then (if e.toFinset ⊆ A ∨ e.toFinset ⊆ Aᶜ then Q.available.mult e else 0) else 0)
    split_ifs <;> simp_all
  have hCount := sum_le_sum (s := (univ : Finset (Sym2 V))) (fun e _ => hLe e)
  change ((Q.available.restrict Aᶜ).incidentOn E).edgeCount ≤
    ((Q.available.internalPart A).incidentOn E).edgeCount at hCount
  rw [run.protected_incident_residue] at hCount
  exact hCount.trans (sum_le_sum (fun e _ => (P.available.internalPart A).incidentOn_le E e))

end PartialColouring.GoodRouteRun
end SimpleGraph.MultiGraph
