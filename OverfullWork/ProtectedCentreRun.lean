module

public import OverfullWork.ProtectedCentreStep

@[expose] public section


/-! # Finite protected first-centre stage

Iterate the ordinary and exceptional CMS recolorings, maintaining the
current triangle bound. The protected bundle is preserved exactly.
The estimates here allow two discarded copies per step; no assertion
about the later second-centre stage is included.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 16000000

theorem ProtectedStep.degree_balance {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (v : V) :
    Q.graph.degree v+h.removed.degree v=P.graph.degree v+
      (unitEdge a h.neighbour h.distinct).degree v := by
  simp only [MultiGraph.degree,←sum_add_distrib]
  exact sum_congr rfl (fun e _ => h.balance e)

theorem ProtectedStep.centre_gain {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) : Q.graph.degree a=P.graph.degree a+1 := by
  have hh := h.degree_balance a
  rw [h.centre_zero,degree_unitEdge,if_pos (Or.inl rfl)] at hh
  omega

theorem ProtectedStep.triangle_gain {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) :
    Q.graph.edgesWithin {a,b,w}=P.graph.edgesWithin {a,b,w}+
      (unitEdge a h.neighbour h.distinct).edgesWithin {a,b,w} := by
  unfold edgesWithin edgeCount
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  change (if e.toFinset ⊆ ({a,b,w}:Finset V) then Q.graph.mult e else 0)=
    (if e.toFinset ⊆ ({a,b,w}:Finset V) then P.graph.mult e else 0)+
    (if e.toFinset ⊆ ({a,b,w}:Finset V) then (unitEdge a h.neighbour h.distinct).mult e else 0)
  split_ifs with he
  · have hh := h.balance e
    rw [h.triangle_zero e he] at hh
    omega
  · rfl

theorem ProtectedStep.triangle_bound {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w)
    (hTri : P.graph.edgesWithin {a,b,w} ≤ P.graph.degree a) :
    Q.graph.edgesWithin {a,b,w} ≤ Q.graph.degree a := by
  have hh := h.triangle_gain
  have hd := h.centre_gain
  rw [edgesWithin_unitEdge] at hh
  split_ifs at hh <;> omega

theorem ProtectedStep.protected_bundle {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (hab : a ≠ b) (haw : a ≠ w) :
    Q.graph.mult s(b,w)=P.graph.mult s(b,w) := by
  have hh := h.balance s(b,w)
  have hz := h.triangle_zero s(b,w) (by simp [Sym2.toFinset_mk_eq])
  have ha : a ∉ s(b,w) := by simp only [Sym2.mem_iff];tauto
  rw [hz,unitEdge_zero_of_not_mem _ _ _ _ ha] at hh
  omega

theorem ProtectedStep.centre_bundle_mono {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (v : V) :
    P.graph.mult s(a,v) ≤ Q.graph.mult s(a,v) := by
  have hz := h.removed.mult_eq_zero_of_degree_zero a v h.centre_zero
  have hh := h.balance s(a,v)
  omega

theorem ProtectedStep.away_bundle_le {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (e : Sym2 V) (ha : a ∉ e) :
    Q.graph.mult e ≤ P.graph.mult e := by
  have hh := h.balance e
  rw [unitEdge_zero_of_not_mem _ _ _ _ ha] at hh
  omega

theorem ProtectedStep.edgeCount_balance {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) :
    Q.graph.edgeCount+h.removed.edgeCount=P.graph.edgeCount+1 := by
  have hh := congrArg (fun f : Sym2 V → ℕ => ∑ e, f e) (funext h.balance)
  simp only [sum_add_distrib] at hh
  change Q.graph.edgeCount+h.removed.edgeCount=P.graph.edgeCount+
    (unitEdge a h.neighbour h.distinct).edgeCount at hh
  simpa only [edgeCount_unitEdge] using hh

theorem ProtectedStep.degree_loss_le {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (v : V) :
    P.graph.degree v ≤ Q.graph.degree v+h.removed.edgeCount := by
  have hh := h.degree_balance v
  have hd : h.removed.degree v ≤ h.removed.edgeCount :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  omega

theorem ProtectedStep.missingSet_growth_le {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) (i : Fin k) :
    (Q.colouring.missingSet univ i).card ≤ (P.colouring.missingSet univ i).card+2 := by
  have hp := P.colouring.missing_card_add_twice_mass i
  have hq := Q.colouring.missing_card_add_twice_mass i
  have hm := h.mass_loss i
  omega

theorem exists_protected_step (P : M.PartialColouring k) (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (hk : k ≤ M.degree a)
    (hTri : P.graph.edgesWithin {a,b,w} ≤ P.graph.degree a)
    (hpos : 0 < (P.colouring.missingPalette a).card) :
    ∃ Q, Nonempty (ProtectedStep P Q a b w) := by
  obtain ⟨i,hi⟩ := card_pos.mp hpos
  have hia : (P.colouring.colourGraph i).degree a=0 := (mem_filter.mp hi).2
  have hm := P.colouring.missingPalette_card_add_degree a
  have ha := P.available_degree a
  have hav : 0 < P.available.degree a := by omega
  have hex : ∃ u, 0 < P.available.mult s(a,u) := by
    by_contra! hn
    have hz : P.available.degree a=0 := by
      rw [degree_eq_sum_mult]
      exact sum_eq_zero (fun u _ => Nat.eq_zero_of_le_zero (hn u))
    omega
  obtain ⟨u,hu⟩ := hex
  have hau : a ≠ u := by
    intro he;subst u
    have hz := P.available.loopless s(a,a) (by simp)
    omega
  by_cases hSafe : u ∉ s(b,w) ∨ P.colouring.col s(b,w) i=0
  · exact exists_ordinary_protected_step P a b w u hau i hia hu hSafe
  · have huPair : u ∈ s(b,w) := by tauto
    have hposF : 0 < P.colouring.col s(b,w) i := by omega
    have hle : P.colouring.col s(b,w) i ≤ 1 := by
      have he : P.colouring.col s(b,w) i ≤ (P.colouring.colourGraph i).degree b := by
        rw [degree_eq_sum_mult]
        exact single_le_sum (f := fun v => (P.colouring.colourGraph i).mult s(b,v))
          (fun _ _ => Nat.zero_le _) (mem_univ w)
      exact he.trans (P.colouring.colourGraph_degree_le_one i b)
    have hiF : P.colouring.col s(b,w) i=1 := by omega
    obtain ⟨α,hα⟩ := exists_unused_triangle_colour P a b w hTri hpos
    exact exists_exceptional_protected_step P a b w u hab haw hbw hau huPair i α hia hu hiF hα

inductive ProtectedRun (a b w : V) : M.PartialColouring k → M.PartialColouring k → ℕ → ℕ → Prop
  | refl (P) : ProtectedRun a b w P P 0 0
  | step {P Q R n t} (h : ProtectedStep P Q a b w) (tail : ProtectedRun a b w Q R n t) :
      ProtectedRun a b w P R (n+1) (h.removed.edgeCount+t)

theorem ProtectedRun.removed_bound {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) : t ≤ 2*n := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.removed_count;omega

theorem ProtectedRun.protected_bundle {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (hab : a ≠ b) (haw : a ≠ w) :
    Q.graph.mult s(b,w)=P.graph.mult s(b,w) := by
  induction h with
  | refl P => rfl
  | step h _ ih => exact ih.trans (h.protected_bundle hab haw)

theorem ProtectedRun.centre_bundle_mono {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (v : V) :
    P.graph.mult s(a,v) ≤ Q.graph.mult s(a,v) := by
  induction h with
  | refl P => exact le_refl _
  | step h _ ih => exact (h.centre_bundle_mono v).trans ih

theorem ProtectedRun.away_bundle_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (e : Sym2 V) (ha : a ∉ e) :
    Q.graph.mult e ≤ P.graph.mult e := by
  induction h with
  | refl P => exact le_refl _
  | step h _ ih => exact ih.trans (h.away_bundle_le e ha)

theorem ProtectedRun.degree_loss_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (v : V) : P.graph.degree v ≤ Q.graph.degree v+t := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.degree_loss_le v;omega

theorem ProtectedRun.missingPalette_growth_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (v : V) :
    (Q.colouring.missingPalette v).card ≤ (P.colouring.missingPalette v).card+t := by
  have hp := P.colouring.missingPalette_card_add_degree v
  have hq := Q.colouring.missingPalette_card_add_degree v
  have hh := h.degree_loss_le v
  omega

theorem ProtectedRun.missingSet_growth_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) (i : Fin k) :
    (Q.colouring.missingSet univ i).card ≤ (P.colouring.missingSet univ i).card+2*n := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.missingSet_growth_le i;omega

theorem ProtectedRun.edgeCount_balance {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) : Q.graph.edgeCount+t=P.graph.edgeCount+n := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.edgeCount_balance;omega

theorem ProtectedRun.total_missing_growth_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) :
    (∑ v, (Q.colouring.missingPalette v).card) ≤
      (∑ v, (P.colouring.missingPalette v).card)+2*n := by
  have hP := sum_congr (s₁ := (univ : Finset V)) rfl
    (fun v _ => P.colouring.missingPalette_card_add_degree v)
  have hQ := sum_congr (s₁ := (univ : Finset V)) rfl
    (fun v _ => Q.colouring.missingPalette_card_add_degree v)
  simp only [sum_add_distrib,P.graph.sum_degrees_eq_twice_edgeCount,
    Q.graph.sum_degrees_eq_twice_edgeCount] at hP hQ
  have hh := h.edgeCount_balance
  have ht := h.removed_bound
  omega

theorem exists_protected_centre_saturated_run (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (hk : k ≤ M.degree a)
    (P : M.PartialColouring k) (hTri : P.graph.edgesWithin {a,b,w} ≤ P.graph.degree a) :
    ∃ Q t, ProtectedRun a b w P Q (P.colouring.missingPalette a).card t ∧
      t ≤ 2*(P.colouring.missingPalette a).card ∧
      (∀ i : Fin k, (Q.colouring.colourGraph i).degree a=1) ∧
      Q.graph.mult s(b,w)=P.graph.mult s(b,w) ∧
      Q.graph.edgesWithin {a,b,w} ≤ Q.graph.degree a := by
  suffices ∀ n : ℕ, ∀ P : M.PartialColouring k, (P.colouring.missingPalette a).card=n →
      P.graph.edgesWithin {a,b,w} ≤ P.graph.degree a →
      ∃ Q t, ProtectedRun a b w P Q n t ∧ t ≤ 2*n ∧
        (∀ i : Fin k, (Q.colouring.colourGraph i).degree a=1) ∧
        Q.graph.mult s(b,w)=P.graph.mult s(b,w) ∧
        Q.graph.edgesWithin {a,b,w} ≤ Q.graph.degree a from this _ P rfl hTri
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hcount hTriangle
    by_cases hn : n=0
    · refine ⟨P,0,?_,by omega,?_,rfl,hTriangle⟩
      · rw [hn];exact ProtectedRun.refl P
      · intro i
        have hc := P.colouring.colourGraph_degree_le_one i a
        by_contra hne
        have hz : (P.colouring.colourGraph i).degree a=0 := by omega
        have hi : i ∈ P.colouring.missingPalette a := mem_filter.mpr ⟨mem_univ _,hz⟩
        have hh := card_pos.mpr ⟨i,hi⟩
        omega
    obtain ⟨Q,⟨hStep⟩⟩ := exists_protected_step P a b w hab haw hbw hk hTriangle (by omega)
    have hP := P.colouring.missingPalette_card_add_degree a
    have hQ := Q.colouring.missingPalette_card_add_degree a
    have hGain := hStep.centre_gain
    have hless : (Q.colouring.missingPalette a).card < n := by omega
    obtain ⟨R,t,hRun,ht,hSat,hBundle,hBound⟩ := ih _ hless Q rfl (hStep.triangle_bound hTriangle)
    have hnEq : (Q.colouring.missingPalette a).card+1=n := by omega
    refine ⟨R,hStep.removed.edgeCount+t,?_,?_,hSat,?_,hBound⟩
    · rw [←hnEq];exact ProtectedRun.step hStep hRun
    · have hh := hStep.removed_count;omega
    · exact hBundle.trans (hStep.protected_bundle hab haw)

end SimpleGraph.MultiGraph.PartialColouring
