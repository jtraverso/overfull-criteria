module

public import OverfullWork.PartialColouring
public import OverfullWork.MultigraphCopyCritical
public import OverfullWork.AddColourMatching
public import OverfullWork.EquitableMissingCounts

@[expose] public section


/-! # Saturate a designated centre by actual copy exchanges

Each step fills one missing centre color using an available incident
copy. At most one conflicting copy away from the centre is uncolored.
A finite run fills every centre color, with at most the initial number
of missing colors uncolored, and never lowers the total colored size.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 12000000

def incidentCopies (M : MultiGraph V) (u : V) : MultiGraph V where
  mult e := if u ∈ e then M.mult e else 0
  loopless e he := by rw [M.loopless e he];simp

theorem incidentCopies_le (M : MultiGraph V) (u : V) (e : Sym2 V) :
    (M.incidentCopies u).mult e ≤ M.mult e := by
  dsimp only [incidentCopies]
  split_ifs <;> omega

theorem incidentCopies_edgeCount (M : MultiGraph V) (u : V) :
    (M.incidentCopies u).edgeCount=M.degree u := by
  simp only [edgeCount,incidentCopies,degree,sum_filter]

theorem subtract_incident_degree_zero (M : MultiGraph V) (u : V) :
    (M.subtractCopies (M.incidentCopies u)).degree u=0 := by
  apply sum_eq_zero
  intro e he
  change M.mult e-(if u ∈ e then M.mult e else 0)=0
  rw [if_pos (mem_filter.mp he).2,Nat.sub_self]

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

structure CentreStep (P Q : M.PartialColouring k) (a : V) where
  color : Fin k
  neighbour : V
  distinct : a ≠ neighbour
  removed : MultiGraph V
  removed_le : ∀ e, removed.mult e ≤ P.colouring.col e color
  available : ∀ e, (unitEdge a neighbour distinct).mult e ≤ P.available.mult e
  proper : ∀ v, ((P.colouring.colourGraph color).subtractCopies removed).degree v+
    (unitEdge a neighbour distinct).degree v ≤ 1
  updated : Q=P.exchange color removed (unitEdge a neighbour distinct) removed_le available proper
  erased_le_one : removed.edgeCount ≤ 1
  centre_free : removed.degree a=0
  centre_gain : Q.graph.degree a=P.graph.degree a+1

theorem exists_centre_step (P : M.PartialColouring k) (a : V) (hk : k ≤ M.degree a)
    (hpos : 0 < (P.colouring.missingPalette a).card) : ∃ Q, Nonempty (CentreStep P Q a) := by
  obtain ⟨i,hi⟩ := card_pos.mp hpos
  have hia : (P.colouring.colourGraph i).degree a=0 := (mem_filter.mp hi).2
  have hmissing := P.colouring.missingPalette_card_add_degree a
  have hav := P.available_degree a
  have hapos : 0 < P.available.degree a := by omega
  have hex : ∃ u, 0 < P.available.mult s(a,u) := by
    by_contra! h
    have hz : P.available.degree a=0 := by
      rw [degree_eq_sum_mult]
      exact sum_eq_zero (fun u _ => Nat.eq_zero_of_le_zero (h u))
    omega
  obtain ⟨u,hu⟩ := hex
  have hau : a ≠ u := by
    intro he
    subst u
    have hz := P.available.loopless s(a,a) (by simp)
    omega
  let R := (P.colouring.colourGraph i).incidentCopies u
  let A := unitEdge a u hau
  have hR : ∀ e, R.mult e ≤ P.colouring.col e i := fun e =>
    (P.colouring.colourGraph i).incidentCopies_le u e
  have hA : ∀ e, A.mult e ≤ P.available.mult e := by
    intro e
    change (if e=s(a,u) then 1 else 0) ≤ _
    by_cases he : e=s(a,u)
    · subst e;rw [if_pos rfl];exact hu
    · rw [if_neg he];exact Nat.zero_le _
  have hRa : R.degree a=0 := by
    have hh := (P.colouring.colourGraph i).degree_le_of_mult_le R hR a
    omega
  have hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v ≤ 1 := by
    intro v
    have hs := degree_subtract_add (P.colouring.colourGraph i) R hR v
    have hc := P.colouring.colourGraph_degree_le_one i v
    dsimp only [A]
    rw [degree_unitEdge]
    by_cases hva : v=a
    · subst v;rw [if_pos (Or.inl rfl)];omega
    by_cases hvu : v=u
    · subst v
      rw [if_pos (Or.inr rfl)]
      have hz : ((P.colouring.colourGraph i).subtractCopies R).degree u=0 :=
        subtract_incident_degree_zero _ _
      omega
    · rw [if_neg (by simp [hva,hvu])];omega
  let Q := P.exchange i R A hR hA hp
  have hGain : Q.graph.degree a=P.graph.degree a+1 := by
    have hh := P.exchange_degree_identity i R A hR hA hp a
    have hAd : A.degree a=1 := by simp [A,degree_unitEdge]
    change Q.graph.degree a+R.degree a=P.graph.degree a+A.degree a at hh
    omega
  refine ⟨Q,⟨{
    color := i, neighbour := u, distinct := hau, removed := R,
    removed_le := hR, available := hA, proper := hp, updated := rfl,
    erased_le_one := ?_, centre_free := hRa, centre_gain := hGain
  }⟩⟩
  exact ((P.colouring.colourGraph i).incidentCopies_edgeCount u).le.trans
    (P.colouring.colourGraph_degree_le_one i u)

theorem CentreStep.edgeCount_mono {P Q : M.PartialColouring k} {a : V} (h : CentreStep P Q a) :
    P.graph.edgeCount ≤ Q.graph.edgeCount := by
  have hh := P.exchange_edgeCount_identity h.color h.removed
    (unitEdge a h.neighbour h.distinct) h.removed_le h.available h.proper
  rw [←h.updated,edgeCount_unitEdge] at hh
  have he := h.erased_le_one
  omega

theorem CentreStep.missingSet_mono {P Q : M.PartialColouring k} {a : V} (h : CentreStep P Q a)
    (i : Fin k) : (Q.colouring.missingSet univ i).card ≤ (P.colouring.missingSet univ i).card := by
  by_cases hi : i=h.color
  · subst i
    have heq := P.exchange_colour_selected h.color h.removed (unitEdge a h.neighbour h.distinct)
      h.removed_le h.available h.proper
    rw [←h.updated] at heq
    have hd : ((P.colouring.colourGraph h.color).subtractCopies h.removed).edgeCount+
        h.removed.edgeCount=(P.colouring.colourGraph h.color).edgeCount := by
      change (∑ e, (P.colouring.col e h.color-h.removed.mult e))+(∑ e, h.removed.mult e)=_
      rw [←sum_add_distrib]
      exact sum_congr rfl (fun e _ => Nat.sub_add_cancel (h.removed_le e))
    have hc : P.colouring.colourMass h.color ≤ Q.colouring.colourMass h.color := by
      change (P.colouring.colourGraph h.color).edgeCount ≤ (Q.colouring.colourGraph h.color).edgeCount
      rw [heq,edgeCount_addCopies,edgeCount_unitEdge]
      have hr := h.erased_le_one
      omega
    have hp := P.colouring.missing_card_add_twice_mass h.color
    have hq := Q.colouring.missing_card_add_twice_mass h.color
    omega
  · have heq := P.exchange_colour_other h.color h.removed (unitEdge a h.neighbour h.distinct)
      h.removed_le h.available h.proper i hi
    rw [←h.updated] at heq
    have hh : Q.colouring.missingSet univ i=P.colouring.missingSet univ i := by
      dsimp only [EdgeColoring.missingSet]
      rw [heq]
    rw [hh]

theorem CentreStep.degree_loss_le {P Q : M.PartialColouring k} {a : V} (h : CentreStep P Q a) (v : V) :
    P.graph.degree v ≤ Q.graph.degree v+h.removed.edgeCount := by
  have hh := P.exchange_degree_identity h.color h.removed (unitEdge a h.neighbour h.distinct)
    h.removed_le h.available h.proper v
  rw [←h.updated] at hh
  have hd : h.removed.degree v ≤ h.removed.edgeCount :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  omega

inductive CentreRun (a : V) : M.PartialColouring k → M.PartialColouring k → ℕ → ℕ → Prop
  | refl (P) : CentreRun a P P 0 0
  | step {P Q R n t} (h : CentreStep P Q a) (tail : CentreRun a Q R n t) :
      CentreRun a P R (n+1) (h.removed.edgeCount+t)

theorem CentreRun.missingSet_mono {a : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : CentreRun a P Q n t) (i : Fin k) :
    (Q.colouring.missingSet univ i).card ≤ (P.colouring.missingSet univ i).card := by
  induction h with
  | refl P => exact le_refl _
  | step h _ ih => exact ih.trans (h.missingSet_mono i)

theorem CentreRun.degree_loss_le {a : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : CentreRun a P Q n t) (v : V) : P.graph.degree v ≤ Q.graph.degree v+t := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.degree_loss_le v;omega

theorem CentreRun.missingPalette_growth_le {a : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : CentreRun a P Q n t) (v : V) :
    (Q.colouring.missingPalette v).card ≤ (P.colouring.missingPalette v).card+t := by
  have hp := P.colouring.missingPalette_card_add_degree v
  have hq := Q.colouring.missingPalette_card_add_degree v
  have hl := h.degree_loss_le v
  omega

theorem exists_centre_saturated_run (a : V) (hk : k ≤ M.degree a) (P : M.PartialColouring k) :
    ∃ Q t, CentreRun a P Q (P.colouring.missingPalette a).card t ∧
      t ≤ (P.colouring.missingPalette a).card ∧
      (∀ i : Fin k, (Q.colouring.colourGraph i).degree a=1) ∧
      P.graph.edgeCount ≤ Q.graph.edgeCount := by
  suffices ∀ n : ℕ, ∀ P : M.PartialColouring k, (P.colouring.missingPalette a).card=n →
      ∃ Q t, CentreRun a P Q n t ∧ t ≤ n ∧
        (∀ i : Fin k, (Q.colouring.colourGraph i).degree a=1) ∧
        P.graph.edgeCount ≤ Q.graph.edgeCount from this _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hcount
    by_cases hn : n=0
    · refine ⟨P,0,?_,Nat.zero_le _,?_,le_refl _⟩
      · rw [hn]
        exact CentreRun.refl P
      · intro i
        have hc := P.colouring.colourGraph_degree_le_one i a
        by_contra hne
        have hz : (P.colouring.colourGraph i).degree a=0 := by omega
        have hi : i ∈ P.colouring.missingPalette a := mem_filter.mpr ⟨mem_univ _,hz⟩
        have hp := card_pos.mpr ⟨i,hi⟩
        omega
    obtain ⟨Q,⟨hStep⟩⟩ := exists_centre_step P a hk (by omega)
    have hP := P.colouring.missingPalette_card_add_degree a
    have hQ := Q.colouring.missingPalette_card_add_degree a
    have hGain := hStep.centre_gain
    have hless : (Q.colouring.missingPalette a).card < n := by omega
    obtain ⟨R,t,hRun,ht,hSat,hSize⟩ := ih _ hless Q rfl
    have hnEq : (Q.colouring.missingPalette a).card+1=n := by omega
    refine ⟨R,hStep.removed.edgeCount+t,?_,?_,hSat,hStep.edgeCount_mono.trans hSize⟩
    · rw [←hnEq]
      exact CentreRun.step hStep hRun
    · have hh := hStep.erased_le_one
      omega

end PartialColouring
end SimpleGraph.MultiGraph
