module

public import OverfullWork.SeedCompletionMargins
public import OverfullWork.EquitableMissingCounts

@[expose] public section


/-! # Complete every seed color by actual bounded good exchanges

Parity supplies two distinct missing endpoints. The finite initial-state
margins construct their exchange at every stage. Strong induction on
the total missing incidences constructs a completed run, with no
factorization or path-existence premise.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 32000000

theorem GoodRouteRun.trans {A E : Finset V} {h ell : ℕ} {P Q R : M.PartialColouring k}
    {n₁ t₁ n₂ t₂ : ℕ} (first : GoodRouteRun A E h ell P Q n₁ t₁)
    (last : GoodRouteRun A E h ell Q R n₂ t₂) :
    GoodRouteRun A E h ell P R (n₁+n₂) (t₁+t₂) := by
  induction first with
  | refl P => simpa using last
  | step s hGood hCross hProtected hLen tail ih =>
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      GoodRouteRun.step s hGood hCross hProtected hLen (ih last)

theorem exists_completed_good_run_of_relative_margins (P : M.PartialColouring k) (A E : Finset V) (h ell : ℕ)
    {m Δ r cutoff B g q Wbar : ℕ} {loss ξ : ℝ} {a₀ b₀ : V}
    (pay : RelativeSeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀) :
    ∃ Q : M.PartialColouring k, ∃ n t : ℕ, GoodRouteRun A E h ell P Q n t ∧
      ∀ i v, (Q.colouring.colourGraph i).degree v=1 := by
  have hEven : Even (Fintype.card V) := by
    refine ⟨m,?_⟩
    have hh := card_add_card_compl A
    rw [pay.card_part,pay.card_compl] at hh
    omega
  suffices ∀ N : ℕ, ∀ Q : M.PartialColouring k, ∀ n t,
      GoodRouteRun A E h ell P Q n t → (∑ v, (Q.colouring.missingPalette v).card)=N →
      ∃ R : M.PartialColouring k, ∃ n' t' : ℕ, GoodRouteRun A E h ell P R n' t' ∧
        ∀ i v, (R.colouring.colourGraph i).degree v=1 by
    exact this _ P 0 0 (GoodRouteRun.refl P) rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro Q n t run hN
    by_cases hDone : ∀ i : Fin k, Q.colouring.missingSet univ i=∅
    · refine ⟨Q,n,t,run,?_⟩
      intro i v
      have hZero : (Q.colouring.colourGraph i).degree v ≠ 0 := by
        intro hv
        have hm : v ∈ Q.colouring.missingSet univ i := mem_filter.mpr ⟨mem_univ _,hv⟩
        rw [hDone i] at hm
        simpa using hm
      have hOne := Q.colouring.colourGraph_degree_le_one i v
      omega
    · push Not at hDone
      obtain ⟨i,hi⟩ := hDone
      have hPos : 0 < (Q.colouring.missingSet univ i).card := card_pos.mpr hi
      obtain ⟨u,hu⟩ := Q.colouring.missing_card_even hEven i
      have hTwo : 1 < (Q.colouring.missingSet univ i).card := by omega
      obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hTwo
      obtain ⟨s,hGood,hCross,hProtected,hLen⟩ := run.exists_exchange_from_relative_margins pay i a b hab ha hb
      have oneStep := GoodRouteRun.step s hGood hCross hProtected hLen (GoodRouteRun.refl s.result)
      have extended := run.trans oneStep
      have hDrop := s.total_missing_drop
      have hLess : (∑ v, (s.result.colouring.missingPalette v).card) < N := by omega
      exact ih _ hLess s.result _ _ extended rfl

theorem exists_completed_good_run (P : M.PartialColouring k) (A E : Finset V) (h ell : ℕ)
    {m Δ r cutoff B g q Wbar : ℕ} {loss ξ : ℝ} {a₀ b₀ : V}
    (pay : SeedCompletionMargins P A E h ell m Δ r cutoff B g q Wbar loss ξ a₀ b₀) :
    ∃ Q : M.PartialColouring k, ∃ n t : ℕ, GoodRouteRun A E h ell P Q n t ∧
      ∀ i v, (Q.colouring.colourGraph i).degree v=1 :=
  exists_completed_good_run_of_relative_margins P A E h ell pay.toRelative

end SimpleGraph.MultiGraph.PartialColouring
