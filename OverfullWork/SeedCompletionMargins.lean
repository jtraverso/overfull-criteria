module

public import OverfullWork.ActualLayerExchange

@[expose] public section


/-! # A finite initial-state criterion for completing the seed colors

All premises concern the initial coloring, ambient support or explicit
scalar margins. No premise supplies paths, later colorings or factors.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes OverfullWork.BipartiteRobustMargin
open OverfullWork.PrunedCore OverfullWork.RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 32000000

structure SeedCompletionMargins (P : M.PartialColouring k) (A E : Finset V) (h ell : ℕ)
    (m Δ r cutoff B g q Wbar : ℕ) (loss ξ : ℝ) (a₀ b₀ : V) : Prop where
  card_part : A.card=m
  card_compl : Aᶜ.card=m
  robust : IsBipartiteRobustAt M.supportGraph A r cutoff
  residue_cap : ∀ v, (P.available.internalPart A).degree v ≤ h
  ordinary_deleted : ∀ v, v ≠ a₀ → v ≠ b₀ → (P.graph.crossingSupport A).degree v ≤ 2
  first_exception : a₀ ∈ E
  second_exception : b₀ ∈ E
  missing : ∀ v, (P.colouring.missingPalette v).card ≤ B
  anchors : ∀ i, (P.colouring.colourGraph i).degree a₀ ≠ 0 ∧ (P.colouring.colourGraph i).degree b₀ ≠ 0
  ordinary_support : ∀ v, v ≠ a₀ → v ≠ b₀ → (Δ:ℝ)/2-loss ≤ M.supportGraph.degree v
  discrepancy : ∀ v, |(neighboursIn M.supportGraph A v:ℝ)-(neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ
  delta : m ≤ Δ
  loss_margin : loss+ξ ≤ (m:ℝ)/16
  forbidden_margin : (Wbar:ℝ) ≤ (m:ℝ)/32
  deletion_margin : (2+B+h:ℕ) ≤ (m:ℝ)/32
  seed_window : (cutoff:ℝ) ≤ (m:ℝ)/8
  window : 2*cutoff ≤ m
  positive_cap : 0 < h
  positive_gain : 0 < g
  gain : Wbar+g ≤ r
  rounds : m/g+3 ≤ ell
  reserve : 4+2*ell < q
  predecessors : q ≤ r-(2+B+h)
  forbidden_initial : ∀ i,
    h*(2*(P.colouring.colourGraph i).cutSize A+(ell+1)*(P.colouring.missingSet univ i).card+2*E.card)+
      4*((P.available.internalPart A).edgeCount+ell*((∑ v, (P.colouring.missingPalette v).card)/2)) ≤ h*Wbar

/-- Use a single bootstrap inequality when the minimum degree is
only a fixed positive fraction of the host order. -/
structure RelativeSeedCompletionMargins (P : M.PartialColouring k) (A E : Finset V) (h ell : ℕ)
    (m Δ r cutoff B g q Wbar : ℕ) (loss ξ : ℝ) (a₀ b₀ : V) : Prop where
  card_part : A.card=m
  card_compl : Aᶜ.card=m
  robust : IsBipartiteRobustAt M.supportGraph A r cutoff
  residue_cap : ∀ v, (P.available.internalPart A).degree v ≤ h
  ordinary_deleted : ∀ v, v ≠ a₀ → v ≠ b₀ → (P.graph.crossingSupport A).degree v ≤ 2
  first_exception : a₀ ∈ E
  second_exception : b₀ ∈ E
  missing : ∀ v, (P.colouring.missingPalette v).card ≤ B
  anchors : ∀ i, (P.colouring.colourGraph i).degree a₀ ≠ 0 ∧ (P.colouring.colourGraph i).degree b₀ ≠ 0
  ordinary_support : ∀ v, v ≠ a₀ → v ≠ b₀ → (Δ:ℝ)/2-loss ≤ M.supportGraph.degree v
  discrepancy : ∀ v, |(neighboursIn M.supportGraph A v:ℝ)-(neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ
  bootstrap_margin : (cutoff:ℝ)+(loss+ξ)/2+(Wbar:ℝ)+((2+B+h:ℕ):ℝ) ≤ (Δ:ℝ)/4
  window : 2*cutoff ≤ m
  positive_cap : 0 < h
  positive_gain : 0 < g
  gain : Wbar+g ≤ r
  rounds : m/g+3 ≤ ell
  reserve : 4+2*ell < q
  predecessors : q ≤ r-(2+B+h)
  forbidden_initial : ∀ i,
    h*(2*(P.colouring.colourGraph i).cutSize A+(ell+1)*(P.colouring.missingSet univ i).card+2*E.card)+
      4*((P.available.internalPart A).edgeCount+ell*((∑ v, (P.colouring.missingPalette v).card)/2)) ≤ h*Wbar

theorem SeedCompletionMargins.toRelative
    {P : M.PartialColouring k} {A E : Finset V} {h ell m Δ r cutoff B g q Wbar : ℕ}
    {loss ξ : ℝ} {a₀ b₀ : V}
    (pay : SeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀) :
    RelativeSeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀ := by
  refine {
    card_part := pay.card_part
    card_compl := pay.card_compl
    robust := pay.robust
    residue_cap := pay.residue_cap
    ordinary_deleted := pay.ordinary_deleted
    first_exception := pay.first_exception
    second_exception := pay.second_exception
    missing := pay.missing
    anchors := pay.anchors
    ordinary_support := pay.ordinary_support
    discrepancy := pay.discrepancy
    bootstrap_margin := ?_
    window := pay.window
    positive_cap := pay.positive_cap
    positive_gain := pay.positive_gain
    gain := pay.gain
    rounds := pay.rounds
    reserve := pay.reserve
    predecessors := pay.predecessors
    forbidden_initial := pay.forbidden_initial
  }
  have hDelta : (m:ℝ) ≤ Δ := by exact_mod_cast pay.delta
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith only [pay.seed_window,pay.loss_margin,pay.forbidden_margin,pay.deletion_margin,hDelta,hm]

namespace GoodRouteRun
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem exists_exchange_from_relative_margins (run : GoodRouteRun A E h ell P Q n t)
    {m Δ r cutoff B g q Wbar : ℕ} {loss ξ : ℝ} {a₀ b₀ : V}
    (pay : RelativeSeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀)
    (i : Fin k) (a b : V) (hab : a ≠ b)
    (ha : a ∈ Q.colouring.missingSet univ i) (hb : b ∈ Q.colouring.missingSet univ i) :
    ∃ s : RouteInput Q i a b,
      (∀ e, s.removed.mult e ≤ ((Q.colouring.colourGraph i).goodMatching (Q.available.internalPart A) A h).mult e) ∧
      (∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) ∧
      (∀ x ∈ E, s.removed.degree x=0) ∧ s.removed.edgeCount ≤ ell := by
  let W := (Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
    (Q.available.internalPart A) A E h
  have hW : W.card ≤ Wbar := by
    have hh := (run.forbidden_weighted_bound i).trans (pay.forbidden_initial i)
    change h*W.card ≤ h*Wbar at hh
    nlinarith [pay.positive_cap]
  have hOrdinary : ∀ v, v ∉ E → (P.graph.crossingSupport A).degree v ≤ 2 := by
    intro v hv
    exact pay.ordinary_deleted v (by intro he;exact hv (he ▸ pay.first_exception))
      (by intro he;exact hv (he ▸ pay.second_exception))
  have hSeed : ∀ v ∈ Q.colouring.missingSet univ i, cutoff < (Q.bootstrapSet A W v).card := by
    intro v hv
    let D := if v ∈ A then Aᶜ else A
    have hSide : (v ∈ A ∧ D=Aᶜ) ∨ (v ∉ A ∧ D=A) := by
      by_cases hh : v ∈ A <;> simp [D,hh]
    have hv₀ := run.missing_endpoint_ne_saturated i a₀ v (pay.anchors i).1 hv
    have hv₁ := run.missing_endpoint_ne_saturated i b₀ v (pay.anchors i).2 hv
    have hd := run.missing_endpoint_deleted_bound a₀ b₀ i B (pay.anchors i).1 (pay.anchors i).2
      pay.ordinary_deleted pay.missing pay.residue_cap v hv
    have hdR : ((Q.graph.crossingSupport A).degree v:ℝ) ≤ (2+B+h:ℕ) := by exact_mod_cast hd
    have hWR : (W.card:ℝ) ≤ Wbar := by exact_mod_cast hW
    have hBoot := Q.bootstrap_from_support_discrepancy A W v D hSide ((Δ:ℝ)/2-loss) ξ
      (pay.ordinary_support v hv₀ hv₁) (pay.discrepancy v)
    have hLower : (cutoff:ℝ) < (Q.bootstrapSet A W v).card := by
      linarith only [hBoot,pay.bootstrap_margin,hWR,hdR]
    exact_mod_cast hLower
  exact run.exists_exchange_from_bootstrap m r cutoff B g q pay.card_part pay.card_compl pay.robust
    pay.residue_cap hOrdinary pay.missing i (by change W.card+g ≤ r;exact (Nat.add_le_add_right hW g).trans pay.gain)
    pay.predecessors pay.positive_gain pay.window pay.rounds pay.reserve a b hab
    (mem_filter.mp ha).2 (mem_filter.mp hb).2 (hSeed a ha) (hSeed b hb)

theorem exists_exchange_from_initial_margins (run : GoodRouteRun A E h ell P Q n t)
    {m Δ r cutoff B g q Wbar : ℕ} {loss ξ : ℝ} {a₀ b₀ : V}
    (pay : SeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀)
    (i : Fin k) (a b : V) (hab : a ≠ b)
    (ha : a ∈ Q.colouring.missingSet univ i) (hb : b ∈ Q.colouring.missingSet univ i) :
    ∃ s : RouteInput Q i a b,
      (∀ e, s.removed.mult e ≤ ((Q.colouring.colourGraph i).goodMatching (Q.available.internalPart A) A h).mult e) ∧
      (∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) ∧
      (∀ x ∈ E, s.removed.degree x=0) ∧ s.removed.edgeCount ≤ ell :=
  run.exists_exchange_from_relative_margins pay.toRelative i a b hab ha hb

end GoodRouteRun
end SimpleGraph.MultiGraph.PartialColouring
