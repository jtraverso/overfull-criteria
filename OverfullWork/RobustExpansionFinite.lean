module

public import OverfullWork.MaximumTwoCore

@[expose] public section


/-! # Finite robust expansion from an explicit minimum-degree margin

All thresholds are integers. These are structural counting statements;
no criticality, edge-colouring, or factorization theorem is assumed.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices having at least `r` neighbours in `S`. -/
def neighbourhood (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (S : Finset V) : Finset V :=
  univ.filter fun v => r≤neighboursIn G S v

/-- An integer form of robust `(r,t)` vertex expansion. -/
def IsRobustAt (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℕ) : Prop :=
  ∀ S : Finset V,t≤S.card → S.card+t≤Fintype.card V →
    S.card+r≤(neighbourhood G r S).card

theorem neighboursIn_eq_filter_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : neighboursIn G S v=(S.filter fun x => G.Adj v x).card := by
  unfold neighboursIn
  congr 1
  ext x
  simp only [mem_filter,mem_neighborFinset]
  tauto

theorem neighboursIn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : neighboursIn G S v≤S.card := by
  rw [neighboursIn_eq_filter_card]
  exact card_le_card (filter_subset _ _)

theorem degree_add_card_le_neighboursIn_add_order (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : G.degree v+S.card≤neighboursIn G S v+Fintype.card V := by
  have hsplit:=card_filter_add_card_filter_not (s:=G.neighborFinset v) (fun x => x∈S)
  have hsub : (G.neighborFinset v).filter (fun x => x∉S)⊆Sᶜ := by
    intro x hx
    exact mem_compl.mpr (mem_filter.mp hx).2
  have hcard:=card_le_card hsub
  have htotal:=card_add_card_compl S
  rw [card_neighborFinset_eq_degree] at hsplit
  change neighboursIn G S v+_ = G.degree v at hsplit
  omega

/-- Double counting adjacency between `S` and all ambient vertices. -/
theorem sum_neighboursIn_eq_sum_degrees (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : (∑v : V,neighboursIn G S v)=∑x∈S,G.degree x := by
  calc
    _ = ∑v : V,∑x∈S,if G.Adj v x then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      rw [neighboursIn_eq_filter_card,card_filter]
    _ = ∑x∈S,∑v : V,if G.Adj v x then 1 else 0 := sum_comm
    _ = ∑x∈S,G.degree x := by
      apply sum_congr rfl
      intro x _
      simp only [G.adj_comm]
      rw [←card_filter]
      have he : univ.filter (fun v => G.Adj x v)=G.neighborFinset x := by
        ext v
        simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
      rw [he,card_neighborFinset_eq_degree]

theorem minDegree_mul_card_le_sum_neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : G.minDegree*S.card≤∑v : V,neighboursIn G S v := by
  rw [sum_neighboursIn_eq_sum_degrees]
  calc
    _ = ∑_x∈S,G.minDegree := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum fun x _ => G.minDegree_le_degree x

/-- Split the incidence count into robust neighbours and all remaining vertices. -/
theorem sum_neighboursIn_le_threshold_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (S : Finset V) :
    (∑v : V,neighboursIn G S v)≤
      (neighbourhood G r S).card*S.card+
        (Fintype.card V-(neighbourhood G r S).card)*(r-1) := by
  let N:=neighbourhood G r S
  have hfirst : (∑v∈N,neighboursIn G S v)≤N.card*S.card := by
    calc
      _ ≤ ∑_v∈N,S.card := sum_le_sum fun v _ => neighboursIn_le_card G S v
      _ = _ := by simp [Nat.mul_comm]
  have hsecond : (∑v∈Nᶜ,neighboursIn G S v)≤Nᶜ.card*(r-1) := by
    calc
      _ ≤ ∑_v∈Nᶜ,(r-1) := by
        apply sum_le_sum
        intro v hv
        have hn : ¬r≤neighboursIn G S v := by
          intro hh
          exact (mem_compl.mp hv) (mem_filter.mpr ⟨mem_univ v,hh⟩)
        omega
      _ = _ := by simp [Nat.mul_comm]
  change (∑v : V,neighboursIn G S v)≤N.card*S.card+(Fintype.card V-N.card)*(r-1)
  calc
    _ = (∑v∈N,neighboursIn G S v)+(∑v∈Nᶜ,neighboursIn G S v) :=
      (sum_add_sum_compl N (fun v => neighboursIn G S v)).symm
    _ ≤ N.card*S.card+Nᶜ.card*(r-1) := Nat.add_le_add hfirst hsecond
    _ = _ := by rw [card_compl]

/-- A minimum-degree margin above one half forces robust expansion
at explicit integer scales. -/
theorem isRobustAt_of_minDegree_margin (G : SimpleGraph V) [DecidableRel G.Adj]
    (m r t : ℕ)
    (hmargin : Fintype.card V+2*m≤2*G.minDegree)
    (hr : 0<r) (hrt : r≤t) (hrm : r≤m)
    (hscale : 4*r*Fintype.card V≤m*t) : IsRobustAt G r t := by
  intro S ht hsize
  have hScard:=card_le_univ S
  by_cases hsmall : 2*S.card≤Fintype.card V+m
  · by_contra hbad
    have hk : (neighbourhood G r S).card<S.card+r := by omega
    have hspos : 0<S.card := by omega
    have hsumlo:=minDegree_mul_card_le_sum_neighboursIn G S
    have hsumhi:=sum_neighboursIn_le_threshold_split G r S
    have hkmul : (neighbourhood G r S).card*S.card<(S.card+r)*S.card :=
      Nat.mul_lt_mul_of_pos_right hk hspos
    have hrem : (Fintype.card V-(neighbourhood G r S).card)*(r-1)≤Fintype.card V*r :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have hrsize : r*S.card≤r*Fintype.card V:=Nat.mul_le_mul_left r hScard
    have hstrict : (∑v : V,neighboursIn G S v)<S.card*S.card+2*r*Fintype.card V := by
      nlinarith only [hsumhi,hkmul,hrem,hrsize]
    have hdm : 2*S.card+m≤2*G.minDegree := by omega
    have hmul:=Nat.mul_le_mul_right S.card hdm
    have hmt : m*t≤m*S.card:=Nat.mul_le_mul_left m ht
    nlinarith only [hstrict,hsumlo,hmul,hmt,hscale]
  · have hlarge : Fintype.card V+r≤G.minDegree+S.card := by omega
    have hall : neighbourhood G r S=univ := by
      apply eq_univ_of_forall
      intro v
      apply mem_filter.mpr
      refine ⟨mem_univ v,?_⟩
      have hd:=degree_add_card_le_neighboursIn_add_order G S v
      have hm:=G.minDegree_le_degree v
      omega
    rw [hall,card_univ]
    omega

end OverfullWork.RobustExpansion
