module

public import OverfullWork.DirectedBatchPrefix
public import OverfullWork.DirectedProfilePerturbation

@[expose] public section


/-! Execute a finite batch from a round construction valid throughout
explicit semidegree budgets. The state is the actual used graph. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage DirectedReserveStitching InducedDigraphSampling
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]

private theorem sum_prefix_le (S : Finset J) (f : J → ℕ) :
    (∑ i : S, f i.val) ≤ ∑ i, f i := by
  rw [← sum_subtype S (fun _ => Iff.rfl) f]
  exact sum_le_sum_of_subset (subset_univ _)

theorem visits_prefix_le (S : Finset J) (A : J → Finset V) (v : V) :
    visits (fun i : S => A i.val) v ≤ visits A v := by
  simp only [visits,card_filter]
  exact sum_prefix_le S (fun i => if v ∈ A i then 1 else 0)

private theorem removed_reserve_eq (Γ U : Digraph V) : Γ \ (Γ \ U) = U ⊓ Γ := by
  ext x y
  simp only [Digraph.sdiff_adj,Digraph.inf_adj]
  tauto

private theorem induced_mixed_mono {D D' Γ Γ' : Digraph V} (A : Finset V)
    (hD : D' ≤ D) (hΓ : Γ' ≤ Γ) :
    mixed D' (induced Γ' A) ⟨Subtype.val,Subtype.val_injective⟩ ≤
      mixed D (induced Γ A) ⟨Subtype.val,Subtype.val_injective⟩ := by
  intro x y h
  rcases h with ⟨p,q,hpq,hp,hq⟩ | ⟨hn,he⟩
  · exact Or.inl ⟨p,q,hΓ hpq,hp,hq⟩
  · exact Or.inr ⟨hn,hD he⟩

/-- Greedy execution of an entire batch (GGKLO 7.3(i)). The supplied
round theorem may depend on the actual remaining graphs and the actual
saturated set. It need only cover the displayed uniform degree budgets. -/
theorem exists_batch_of_rounds (D Γ : Digraph V) (hDΓ : Disjoint D Γ)
    (L : J → Layout V I) (long : J → I) (A : J → Finset V) (b a cap q z : ℕ)
    (hcap : 0 < cap) (hZ : Fintype.card J*q ≤ cap*z)
    (hEndpoint : ∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b)
    (hBlock : ∀ v, visits A v ≤ a)
    (hRound : ∀ (i : J) (D' Γ' : Digraph V) (Z : Finset V),
      D' ≤ D → Γ' ≤ Γ → Disjoint (L i).boundary Z → Z.card ≤ z →
      (∀ v, inDegree (D \ D') v ≤ Fintype.card J+b ∧
        outDegree (D \ D') v ≤ Fintype.card J+b) →
      (∀ v, inDegree (Γ \ Γ') v ≤ b+2*cap+2*a ∧
        outDegree (Γ \ Γ') v ≤ b+2*cap+2*a) →
      ∃ R : Realization (D' ⊔ Γ') (L i), (R.shortVertices (long i)).card ≤ q ∧
        Disjoint (R.shortVertices (long i)) Z ∧
        wordGraph (R.word (long i)) ≤ mixed D' (induced Γ' (A i)) ⟨Subtype.val,Subtype.val_injective⟩) :
    Nonempty (BatchPrefix D Γ L long A (univ : Finset J) cap q) := by
  have hEp (S : Finset J) (v : V) :
      (∑ i : S, ((L i.val).endpointLoad true v+(L i.val).endpointLoad false v)) ≤ b :=
    (sum_prefix_le S _).trans (hEndpoint v)
  suffices h : ∀ S : Finset J, Nonempty (BatchPrefix D Γ L long A S cap q) from h _
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨BatchPrefix.empty D Γ L long A cap q⟩
  | @insert i S hi ih =>
    obtain ⟨P⟩ := ih
    let U := P.toPackingPrefix.used
    let D' := D \ U
    let Γ' := Γ \ U
    let Z := P.saturated \ (L i).boundary
    have hZDis : Disjoint (L i).boundary Z := disjoint_left.mpr fun _ h hz => (mem_sdiff.mp hz).2 h
    have hV := (Nat.mul_le_mul_right q (card_le_univ S)).trans hZ
    have hSat := P.saturated_cost.trans hV
    have hSatLe : P.saturated.card ≤ z :=
      (mul_le_mul_iff_right₀ hcap).mp (by simpa only [Nat.mul_comm cap] using hSat)
    have hZSize : Z.card ≤ z := (card_le_card sdiff_subset).trans hSatLe
    have hDLoss (v : V) :
        inDegree (D \ D') v ≤ Fintype.card J+b ∧
          outDegree (D \ D') v ≤ Fintype.card J+b := by
      have hLoads (s : Bool) : (∑ j : S, (L j.val).endpointLoad s v) ≤ b := by
        apply le_trans _ (hEp S v)
        apply sum_le_sum
        intro j _
        cases s <;> omega
      have h := semidegrees_batch_used (D ⊔ Γ) (fun j : S => L j.val) P.round P.disjoint v
        (visits (fun j : S => (L j.val).boundary) v) b le_rfl hLoads
      have hl := semidegrees_deleted_le D U v
      change _ ≤ inDegree U v ∧ _ ≤ outDegree U v at hl
      change _ ≤ inDegree U v+_ ∧ inDegree U v ≤ _ ∧
        _ ≤ outDegree U v+_ ∧ outDegree U v ≤ _ at h
      have hCard : Fintype.card S ≤ Fintype.card J := by
        simpa only [Fintype.card_coe] using card_le_univ S
      exact ⟨hl.1.trans (h.2.1.trans (Nat.add_le_add_right hCard _)),
        hl.2.trans (h.2.2.2.trans (Nat.add_le_add_right hCard _))⟩
    have hΓLoss (v : V) :
        inDegree (Γ \ Γ') v ≤ b+2*cap+2*a ∧ outDegree (Γ \ Γ') v ≤ b+2*cap+2*a := by
      have hh := P.reserve_use hDΓ b a (hEp S) (fun v =>
        (visits_prefix_le S A v).trans (hBlock v)) v
      change inDegree (Γ \ (Γ \ U)) v ≤ _ ∧ outDegree (Γ \ (Γ \ U)) v ≤ _
      rw [removed_reserve_eq]
      exact ⟨(Nat.le_add_right _ _).trans hh,(Nat.le_add_left _ _).trans hh⟩
    obtain ⟨R,hSize,hZA,hLong⟩ :=
      hRound i D' Γ' Z sdiff_le sdiff_le hZDis hZSize hDLoss hΓLoss
    have hAvoid : Disjoint (R.shortVertices (long i)) P.saturated := by
      apply disjoint_left.mpr
      intro v hv hs
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hv
      have hOut := R.outside j v (List.mem_toFinset.mp hj)
      exact disjoint_left.mp hZA hv (mem_sdiff.mpr ⟨hs,hOut⟩)
    have he : D' ⊔ Γ' = (D ⊔ Γ) \ U := sup_sdiff.symm
    let Q := R.rehost (le_of_eq he)
    have hLong' := hLong.trans (induced_mixed_mono (A i) (show D' ≤ D from sdiff_le)
      (show Γ' ≤ Γ from sdiff_le))
    exact ⟨P.insert hi Q hLong' hSize hAvoid⟩

end OverfullWork.DirectedSpanningConfiguration
