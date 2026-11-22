module

public import OverfullWork.DirectedPackingPrefix
public import OverfullWork.DirectedRoundReserveCost

@[expose] public section


/-! The induction invariant (A)–(C) of GGKLO Lemma 7.3(i) on actual
prefixes. A vertex with no short-interior capacity is excluded before
the next layout is routed. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage DirectedReserveStitching InducedDigraphSampling
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype I]

/-- A prefix with bounds on short interiors and the provenance of the long path. -/
structure BatchPrefix (D Γ : Digraph V) (L : J → Layout V I) (long : J → I)
    (A : J → Finset V) (S : Finset J) (cap q : ℕ) extends PackingPrefix (D ⊔ Γ) L S where
  long_from_block : ∀ i : S, wordGraph ((round i).word (long i.val)) ≤
    mixed D (induced Γ (A i.val)) ⟨Subtype.val,Subtype.val_injective⟩
  short_size : ∀ i : S, ((round i).shortVertices (long i.val)).card ≤ q
  short_cap : ∀ v, visits (fun i : S => (round i).shortVertices (long i.val)) v ≤ cap

namespace BatchPrefix

variable {D Γ : Digraph V} {L : J → Layout V I} {long : J → I} {A : J → Finset V}
  {S : Finset J} {cap q : ℕ}

/-- The set of vertices which have already met the short-interior cap. -/
noncomputable def saturated (P : BatchPrefix D Γ L long A S cap q) : Finset V :=
  univ.filter (fun v => cap ≤ visits (fun i : S => (P.round i).shortVertices (long i.val)) v)

theorem saturated_cost (P : BatchPrefix D Γ L long A S cap q) :
    cap*P.saturated.card ≤ S.card*q := by
  have h := saturated_vertices_cost (fun i : S => (P.round i).shortVertices (long i.val)) cap
  apply h.trans
  calc
    _ ≤ ∑ _i : S, q := sum_le_sum (fun i _ => P.short_size i)
    _ = S.card*q := by simp [nsmul_eq_mul]

def empty (D Γ : Digraph V) (L : J → Layout V I) (long : J → I) (A : J → Finset V) (cap q : ℕ) :
    BatchPrefix D Γ L long A ∅ cap q where
  toPackingPrefix := PackingPrefix.empty _ _
  long_from_block i := (notMem_empty i.val i.prop).elim
  short_size i := (notMem_empty i.val i.prop).elim
  short_cap := by intro v; simp [visits]

private theorem visits_insert {i : J} (hi : i ∉ S) (F : ↥(insert i S : Finset J) → Finset V)
    (v : V) :
    visits F v = (if v ∈ F ⟨i,mem_insert_self _ _⟩ then 1 else 0)+
      visits (fun j : S => F ⟨j.val,mem_insert_of_mem j.prop⟩) v := by
  let e := (subtypeInsertEquivOption hi).symm
  rw [visits,card_filter,← e.sum_comp (fun j => if v ∈ F j then (1:ℕ) else 0),
    Fintype.sum_option,visits,card_filter]
  rfl

/-- The short-interior cap is preserved by avoiding vertices that have
already reached it. The two realizations use disjoint host arcs. -/
noncomputable def insert (P : BatchPrefix D Γ L long A S cap q)
    {i : J} (hi : i ∉ S) (R : Realization ((D ⊔ Γ) \ P.toPackingPrefix.used) (L i))
    (hLong : wordGraph (R.word (long i)) ≤
      mixed D (induced Γ (A i)) ⟨Subtype.val,Subtype.val_injective⟩)
    (hSize : (R.shortVertices (long i)).card ≤ q)
    (hAvoid : Disjoint (R.shortVertices (long i)) P.saturated) :
    BatchPrefix D Γ L long A (insert i S) cap q where
  toPackingPrefix := P.toPackingPrefix.insert hi R
  long_from_block := by
    intro j
    by_cases hj : j.val = i
    · have he : j = ⟨i,mem_insert_self _ _⟩ := Subtype.ext hj
      subst j
      rw [P.toPackingPrefix.insert_round_new hi R]
      exact hLong
    · have hm := (mem_insert.mp j.prop).resolve_left hj
      have he : j = ⟨j.val,mem_insert_of_mem hm⟩ := Subtype.ext rfl
      conv => lhs; rw [he,P.toPackingPrefix.insert_round_old hi R ⟨j.val,hm⟩]
      exact P.long_from_block ⟨j.val,hm⟩
  short_size := by
    intro j
    by_cases hj : j.val = i
    · have he : j = ⟨i,mem_insert_self _ _⟩ := Subtype.ext hj
      subst j
      rw [P.toPackingPrefix.insert_round_new hi R]
      exact hSize
    · have hm := (mem_insert.mp j.prop).resolve_left hj
      have he : j = ⟨j.val,mem_insert_of_mem hm⟩ := Subtype.ext rfl
      conv => lhs; rw [he,P.toPackingPrefix.insert_round_old hi R ⟨j.val,hm⟩]
      exact P.short_size ⟨j.val,hm⟩
  short_cap := by
    intro v
    rw [visits_insert hi,P.toPackingPrefix.insert_round_new hi R]
    simp_rw [P.toPackingPrefix.insert_round_old hi R]
    have hOld := P.short_cap v
    by_cases hv : v ∈ R.shortVertices (long i)
    · have hNot := disjoint_left.mp hAvoid hv
      have hLess : visits (fun i : S => (P.round i).shortVertices (long i.val)) v < cap := by
        apply lt_of_not_ge
        exact fun h => hNot (mem_filter.mpr ⟨mem_univ _,h⟩)
      have hR : v ∈ (R.rehost sdiff_le).shortVertices (long i) := hv
      rw [if_pos hR]
      omega
    · have hR : v ∉ (R.rehost sdiff_le).shortVertices (long i) := hv
      rw [if_neg hR,Nat.zero_add]
      exact hOld

/-- The unused reserve has lost at most the endpoint, block, and capped
short-interior budgets of the processed prefix. -/
theorem reserve_use (P : BatchPrefix D Γ L long A S cap q) (hDΓ : Disjoint D Γ) (b a : ℕ)
    (hEndpoint : ∀ v, (∑ i : S, ((L i.val).endpointLoad true v+
      (L i.val).endpointLoad false v)) ≤ b)
    (hBlock : ∀ v, visits (fun i : S => A i.val) v ≤ a) (v : V) :
    inDegree (P.toPackingPrefix.used ⊓ Γ) v+outDegree (P.toPackingPrefix.used ⊓ Γ) v ≤
      b+2*cap+2*a :=
  reserve_loss_of_rounds (fun i : S => L i.val) P.round (fun i => long i.val)
    (fun i => A i.val) hDΓ P.long_from_block b cap a hEndpoint P.short_cap hBlock v

end BatchPrefix
end OverfullWork.DirectedSpanningConfiguration
