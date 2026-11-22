module

public import OverfullWork.ProtectedColourTools

@[expose] public section


/-! # CMS protected centre step: ordinary and exceptional recolorings

In the exceptional case the conflicting protected copy is transferred
from i to an unused triangle color alpha. Only alpha copies incident
with the two protected vertices are discarded, at most two in total.
The protected bundle itself is restored by the explicit second exchange.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 16000000

structure ProtectedStep (P Q : M.PartialColouring k) (a b w : V) where
  neighbour : V
  distinct : a ≠ neighbour
  removed : MultiGraph V
  removed_le : ∀ e, removed.mult e ≤ P.graph.mult e
  removed_count : removed.edgeCount ≤ 2
  centre_zero : removed.degree a=0
  triangle_zero : ∀ e, e.toFinset ⊆ ({a,b,w}:Finset V) → removed.mult e=0
  balance : ∀ e, Q.graph.mult e+removed.mult e=P.graph.mult e+(unitEdge a neighbour distinct).mult e
  mass_loss : ∀ i, P.colouring.colourMass i ≤ Q.colouring.colourMass i+1

theorem unit_available_of_positive (P : M.PartialColouring k) (a u : V) (hau : a ≠ u)
    (hu : 0 < P.available.mult s(a,u)) : ∀ e, (unitEdge a u hau).mult e ≤ P.available.mult e := by
  intro e
  change (if e=s(a,u) then 1 else 0) ≤ _
  by_cases he : e=s(a,u)
  · subst e;rw [if_pos rfl];exact hu
  · rw [if_neg he];exact Nat.zero_le _

theorem exists_ordinary_protected_step (P : M.PartialColouring k) (a b w u : V) (hau : a ≠ u)
    (i : Fin k) (hia : (P.colouring.colourGraph i).degree a=0)
    (hu : 0 < P.available.mult s(a,u)) (hSafe : u ∉ s(b,w) ∨ P.colouring.col s(b,w) i=0) :
    ∃ Q, Nonempty (ProtectedStep P Q a b w) := by
  let L := P.colouring.colourGraph i
  let R := L.incidentOn {u}
  let A := unitEdge a u hau
  have hR : ∀ e, R.mult e ≤ P.colouring.col e i := L.incidentOn_le {u}
  have hA : ∀ e, A.mult e ≤ P.available.mult e := unit_available_of_positive P a u hau hu
  have hp : ∀ v, (L.subtractCopies R).degree v+A.degree v ≤ 1 :=
    matching_after_incidentOn_clear L {u} (P.colouring.colourGraph_degree_le_one i) a u hau
      (Or.inl hia) (Or.inr (mem_singleton_self u))
  let Q := P.exchange i R A hR hA hp
  have hRa : R.degree a=0 := by
    have hh := L.degree_le_of_mult_le R hR a
    change R.degree a ≤ (P.colouring.colourGraph i).degree a at hh
    omega
  have hRf : R.mult s(b,w)=0 := by
    change (if ∃ v ∈ ({u}:Finset V), v ∈ s(b,w) then P.colouring.col s(b,w) i else 0)=0
    rcases hSafe with hSafe|hSafe
    · simp only [mem_singleton,exists_eq_left,if_neg hSafe]
    · simp only [hSafe,ite_self]
  have hCount : R.edgeCount ≤ 1 := by
    have hh := L.incidentOn_edgeCount_le {u}
    simp only [sum_singleton] at hh
    exact hh.trans (P.colouring.colourGraph_degree_le_one i u)
  refine ⟨Q,⟨{
    neighbour := u, distinct := hau, removed := R,
    removed_le := fun e => (hR e).trans (P.colouring.col_le_mult e i)
    removed_count := by omega
    centre_zero := hRa
    triangle_zero := triangle_zero_of_centre_and_pair R a b w hRa hRf
    balance := P.exchange_bundle_balance i R A hR hA hp
    mass_loss := ?_
  }⟩⟩
  intro j
  by_cases hj : j=i
  · subst j
    have hh := P.exchange_mass_identity i R A hR hA hp
    have hAc : A.edgeCount=1 := edgeCount_unitEdge a u hau
    change Q.colouring.colourMass i+R.edgeCount=P.colouring.colourMass i+A.edgeCount at hh
    omega
  · have heq := P.exchange_colour_other i R A hR hA hp j hj
    change Q.colouring.colourGraph j=P.colouring.colourGraph j at heq
    have hm := congrArg MultiGraph.edgeCount heq
    change Q.colouring.colourMass j=P.colouring.colourMass j at hm
    omega

theorem exists_exceptional_protected_step (P : M.PartialColouring k) (a b w u : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (hau : a ≠ u) (huPair : u ∈ s(b,w))
    (i α : Fin k) (hia : (P.colouring.colourGraph i).degree a=0)
    (hu : 0 < P.available.mult s(a,u)) (hiF : P.colouring.col s(b,w) i=1)
    (hα : α ∉ P.colouring.usedOn {a,b,w}) : ∃ Q, Nonempty (ProtectedStep P Q a b w) := by
  let F := unitEdge b w hbw
  let E := unitEdge a u hau
  have haF : a ∉ s(b,w) := by simp only [Sym2.mem_iff];tauto
  have hEf : E.mult s(b,w)=0 := unitEdge_zero_of_not_mem a u hau _ haF
  have hF : ∀ e, F.mult e ≤ P.colouring.col e i := by
    intro e
    change (if e=s(b,w) then 1 else 0) ≤ _
    by_cases he : e=s(b,w)
    · subst e;rw [if_pos rfl,hiF]
    · rw [if_neg he];exact Nat.zero_le _
  have hE : ∀ e, E.mult e ≤ P.available.mult e := unit_available_of_positive P a u hau hu
  have hαzero : ∀ e, e.toFinset ⊆ ({a,b,w}:Finset V) → P.colouring.col e α=0 :=
    P.colouring.unusedOn_copies_zero {a,b,w} α hα
  have hαf : P.colouring.col s(b,w) α=0 := hαzero _ (by simp [Sym2.toFinset_mk_eq])
  have hiα : i ≠ α := by intro hh;subst α;omega
  have hFdu : F.degree u=1 := by
    rw [degree_unitEdge]
    exact if_pos (by simpa only [Sym2.mem_iff] using huPair)
  have hp₁ : ∀ v, ((P.colouring.colourGraph i).subtractCopies F).degree v+E.degree v ≤ 1 := by
    intro v
    have hs := degree_subtract_add (P.colouring.colourGraph i) F hF v
    have hd := P.colouring.colourGraph_degree_le_one i v
    rw [show E.degree v=if v=a ∨ v=u then 1 else 0 from degree_unitEdge a u hau v]
    by_cases hva : v=a
    · subst v;rw [if_pos (Or.inl rfl)];omega
    by_cases hvu : v=u
    · subst v;rw [if_pos (Or.inr rfl)];omega
    · rw [if_neg (by simp [hva,hvu])];omega
  let Q₁ := P.exchange i F E hF hE hp₁
  have hOther : Q₁.colouring.colourGraph α=P.colouring.colourGraph α :=
    P.exchange_colour_other i F E hF hE hp₁ α hiα.symm
  let L := Q₁.colouring.colourGraph α
  let R := L.incidentOn {b,w}
  have hR : ∀ e, R.mult e ≤ Q₁.colouring.col e α := L.incidentOn_le {b,w}
  have hRestore : ∀ e, F.mult e ≤ Q₁.available.mult e := by
    intro e
    by_cases he : e=s(b,w)
    · subst e
      have hbalance := P.exchange_bundle_balance i F E hF hE hp₁ s(b,w)
      have hPf : 1 ≤ P.graph.mult s(b,w) := by
        have hh := P.colouring.col_le_mult s(b,w) i
        omega
      have hcap := P.le s(b,w)
      have hFc : F.mult s(b,w)=1 := if_pos rfl
      change Q₁.graph.mult s(b,w)+F.mult s(b,w)=P.graph.mult s(b,w)+E.mult s(b,w) at hbalance
      change F.mult s(b,w) ≤ M.mult s(b,w)-Q₁.graph.mult s(b,w)
      omega
    · change (if e=s(b,w) then 1 else 0) ≤ _
      rw [if_neg he];exact Nat.zero_le _
  have hp₂ : ∀ v, (L.subtractCopies R).degree v+F.degree v ≤ 1 :=
    matching_after_incidentOn_clear L {b,w} (Q₁.colouring.colourGraph_degree_le_one α) b w hbw
      (Or.inr (by simp)) (Or.inr (by simp))
  let Q := Q₁.exchange α R F hR hRestore hp₂
  have hRtri : ∀ e, e.toFinset ⊆ ({a,b,w}:Finset V) → R.mult e=0 := by
    intro e he
    have hh := hR e
    have hz : Q₁.colouring.col e α=0 := by
      change (Q₁.colouring.colourGraph α).mult e=0
      rw [hOther]
      exact hαzero e he
    omega
  have hRa : R.degree a=0 := by
    apply incidentOn_degree_zero_away L {b,w} a (by simp [hab,haw])
    intro v hv
    change (Q₁.colouring.colourGraph α).mult s(a,v)=0
    rw [hOther]
    apply hαzero
    rcases (show v=b ∨ v=w by simpa only [mem_insert,mem_singleton] using hv) with hv|hv <;> subst v <;> simp [Sym2.toFinset_mk_eq]
  have hCount : R.edgeCount ≤ 2 := by
    have hh := L.incidentOn_edgeCount_le {b,w}
    rw [sum_pair hbw] at hh
    change R.edgeCount ≤ (Q₁.colouring.colourGraph α).degree b+(Q₁.colouring.colourGraph α).degree w at hh
    have hb := Q₁.colouring.colourGraph_degree_le_one α b
    have hw := Q₁.colouring.colourGraph_degree_le_one α w
    omega
  have hRoriginal : ∀ e, R.mult e ≤ P.graph.mult e := by
    intro e
    have hh := hR e
    have hc : Q₁.colouring.col e α=P.colouring.col e α := congrArg (fun N : MultiGraph V => N.mult e) hOther
    rw [hc] at hh
    exact hh.trans (P.colouring.col_le_mult e α)
  refine ⟨Q,⟨{
    neighbour := u, distinct := hau, removed := R, removed_le := hRoriginal,
    removed_count := hCount, centre_zero := hRa, triangle_zero := hRtri,
    balance := ?_, mass_loss := ?_
  }⟩⟩
  · intro e
    have h1 := P.exchange_bundle_balance i F E hF hE hp₁ e
    have h2 := Q₁.exchange_bundle_balance α R F hR hRestore hp₂ e
    change Q₁.graph.mult e+F.mult e=P.graph.mult e+E.mult e at h1
    change Q.graph.mult e+R.mult e=Q₁.graph.mult e+F.mult e at h2
    change Q.graph.mult e+R.mult e=P.graph.mult e+E.mult e
    omega
  · intro j
    have hFi : F.edgeCount=1 := edgeCount_unitEdge b w hbw
    have hEi : E.edgeCount=1 := edgeCount_unitEdge a u hau
    by_cases hjα : j=α
    · subst j
      have hm1 := congrArg MultiGraph.edgeCount hOther
      have hm2 := Q₁.exchange_mass_identity α R F hR hRestore hp₂
      change Q₁.colouring.colourMass α=P.colouring.colourMass α at hm1
      change Q.colouring.colourMass α+R.edgeCount=Q₁.colouring.colourMass α+F.edgeCount at hm2
      omega
    have hQj := Q₁.exchange_colour_other α R F hR hRestore hp₂ j hjα
    have hmQ := congrArg MultiGraph.edgeCount hQj
    change Q.colouring.colourMass j=Q₁.colouring.colourMass j at hmQ
    by_cases hji : j=i
    · subst j
      have hm1 := P.exchange_mass_identity i F E hF hE hp₁
      change Q₁.colouring.colourMass i+F.edgeCount=P.colouring.colourMass i+E.edgeCount at hm1
      omega
    · have hm1 := congrArg MultiGraph.edgeCount (P.exchange_colour_other i F E hF hE hp₁ j hji)
      change Q₁.colouring.colourMass j=P.colouring.colourMass j at hm1
      omega

end SimpleGraph.MultiGraph.PartialColouring
