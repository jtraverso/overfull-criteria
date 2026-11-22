module

public import OverfullWork.RegularPairNeighbourhood

@[expose] public section


/-! # Bipartite robust expansion with a bounded exceptional set

This above-half degree criterion is proved by finite incidence counting.
All thresholds and exceptional losses are explicit. It is a sufficient
criterion for the actual crossing graph, not a factorization theorem.
-/
namespace OverfullWork.BipartiteRobustMargin
open SimpleGraph Finset PrunedCore RobustExpansion RegularPairNeighbourhood
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 6000000

def neighbours (B : Finset V) (r : ℕ) (S : Finset V) : Finset V :=
  B.filter fun v=>r≤neighboursIn G S v

def ExpandsTo (A B : Finset V) (r t : ℕ) : Prop :=
  ∀S : Finset V,S⊆A → t≤S.card → S.card+t≤A.card →
    S.card+r≤(neighbours G B r S).card

def IsBipartiteRobustAt (A : Finset V) (r t : ℕ) : Prop :=
  ExpandsTo G A Aᶜ r t ∧ ExpandsTo G Aᶜ A r t

theorem interedges_eq_row_sum (S B : Finset V) :
    (G.interedges S B).card=∑x∈S,neighboursIn G B x := by
  letI : Std.Symm G.Adj:=⟨fun _ _ h=>h.symm⟩
  have hh:=Rel.card_interedges_comm (r:=G.Adj) S B
  change (G.interedges S B).card=(G.interedges B S).card at hh
  exact hh.trans (interedges_eq_sum_neighbours G B S)

theorem subset_neighbour_bound (A S : Finset V) (hSA : S⊆A) (v : V) :
    neighboursIn G A v+S.card≤neighboursIn G S v+A.card := by
  let N:=A.filter fun x=>G.Adj v x
  have hsub:N∪S⊆A:=union_subset (filter_subset _ _) hSA
  have hInter:N∩S=S.filter (G.Adj v):=by
    ext x
    simp only [N,mem_inter,mem_filter]
    constructor
    · rintro ⟨⟨_,ha⟩,hx⟩;exact ⟨hx,ha⟩
    · rintro ⟨hx,ha⟩;exact ⟨⟨hSA hx,ha⟩,hx⟩
  have hh:=card_union_add_card_inter N S
  rw [hInter] at hh
  have hu:=card_le_card hsub
  rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card]
  change N.card+S.card≤(S.filter (G.Adj v)).card+A.card
  omega

theorem threshold_count (B S : Finset V) (r : ℕ) :
    (G.interedges S B).card≤(neighbours G B r S).card*S.card+B.card*r := by
  rw [interedges_eq_sum_neighbours]
  let R:=neighbours G B r S
  have hsub:R⊆B:=filter_subset _ _
  have hsplit:(∑v∈R,neighboursIn G S v)+(∑v∈B\R,neighboursIn G S v)=
      ∑v∈B,neighboursIn G S v:=by
    have hh:=sum_sdiff (f:=fun v=>neighboursIn G S v) hsub
    omega
  have h₁:(∑v∈R,neighboursIn G S v)≤R.card*S.card:=by
    calc
      _ ≤ ∑_v∈R,S.card :=sum_le_sum (fun v _=>neighboursIn_le_card G S v)
      _ = _ :=by simp [Nat.mul_comm]
  have h₂:(∑v∈B\R,neighboursIn G S v)≤B.card*r:=by
    have hpoint:∀v∈B\R,neighboursIn G S v≤r:=by
      intro v hv
      obtain ⟨hvB,hvR⟩:=mem_sdiff.mp hv
      have hn:¬r≤neighboursIn G S v:=by
        intro hr
        exact hvR (mem_filter.mpr ⟨hvB,hr⟩)
      omega
    calc
      _ ≤ ∑_v∈B\R,r :=sum_le_sum hpoint
      _ = (B\R).card*r :=by simp [Nat.mul_comm]
      _ ≤ _ :=Nat.mul_le_mul_right r (card_le_card sdiff_subset)
  change _≤R.card*S.card+B.card*r
  omega

theorem row_lower_with_exceptions (A B E S : Finset V) (δ a : ℕ)
    (hSA : S⊆A) (hE : E.card≤a)
    (hDegree : ∀v∈A,v∉E → δ≤neighboursIn G B v) :
    δ*S.card≤(G.interedges S B).card+δ*a := by
  have h₁:δ*(S\E).card≤(G.interedges S B).card:=by
    rw [interedges_eq_row_sum]
    calc
      _ = ∑_v∈S\E,δ :=by simp [Nat.mul_comm]
      _ ≤ ∑v∈S\E,neighboursIn G B v :=by
        apply sum_le_sum
        intro v hv
        exact hDegree v (hSA (mem_sdiff.mp hv).1) (mem_sdiff.mp hv).2
      _ ≤ _ :=sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _=>Nat.zero_le _)
  have h₂:(S∩E).card≤a:=(card_le_card inter_subset_right).trans hE
  have hsplit:=card_sdiff_add_card_inter S E
  have hh:=Nat.mul_le_mul_left δ h₂
  have he:δ*S.card=δ*(S\E).card+δ*(S∩E).card:=by rw [←hsplit,Nat.mul_add]
  omega

/-- Each side has m vertices. Except for at most a vertices, every
crossing degree is at least delta. The displayed scale inequality pays
for both threshold loss and exceptional rows. -/
theorem expands_of_margin (A B E : Finset V) (m δ q r t a : ℕ)
    (hA : A.card=m) (hB : B.card=m) (hE : E.card≤a)
    (hAB : ∀v∈A,v∉E → δ≤neighboursIn G B v)
    (hBA : ∀v∈B,v∉E → δ≤neighboursIn G A v)
    (hδ : δ≤m) (hMargin : m+2*q≤2*δ) (hr : 0<r)
    (hrq : r≤q) (hrt : r+a≤t) (hScale : 4*r*m+2*m*a≤q*t) :
    ExpandsTo G A B r t := by
  intro S hSA ht hSize
  have hSm:S.card≤m:=by rw [←hA];exact card_le_card hSA
  by_cases hSmall:2*S.card≤m+q
  · by_contra hBad
    have hRN:(neighbours G B r S).card<S.card+r:=by omega
    have hSpos:0<S.card:=by omega
    have hUpper:=threshold_count G B S r
    rw [hB] at hUpper
    have hLower:=row_lower_with_exceptions G A B E S δ a hSA hE hAB
    have hStrict: (neighbours G B r S).card*S.card<(S.card+r)*S.card:=
      Nat.mul_lt_mul_of_pos_right hRN hSpos
    have hrSm:=Nat.mul_le_mul_left r hSm
    have hδa:=Nat.mul_le_mul_right a hδ
    have hCount:(G.interedges S B).card<S.card*S.card+2*r*m:=by
      nlinarith only [hUpper,hStrict,hrSm]
    have hRoom:2*S.card+q≤2*δ:=by omega
    have hMul:=Nat.mul_le_mul_right S.card hRoom
    have hQT:=Nat.mul_le_mul_left q ht
    nlinarith only [hLower,hδa,hCount,hMul,hScale,hQT]
  · have hRoom:m+r≤δ+S.card:=by omega
    have hSub:B\E⊆neighbours G B r S:=by
      intro v hv
      obtain ⟨hvB,hvE⟩:=mem_sdiff.mp hv
      have hD:=hBA v hvB hvE
      have hN:=subset_neighbour_bound G A S hSA v
      rw [hA] at hN
      exact mem_filter.mpr ⟨hvB,by omega⟩
    have hRN:=card_le_card hSub
    have hSplit:=card_sdiff_add_card_inter B E
    have hBE:(B∩E).card≤a:=(card_le_card inter_subset_right).trans hE
    rw [hB] at hSplit
    rw [hA] at hSize
    omega

theorem bipartite_robust_of_margin (A E : Finset V) (m δ q r t a : ℕ)
    (hA : A.card=m) (hB : Aᶜ.card=m) (hE : E.card≤a)
    (hAB : ∀v∈A,v∉E → δ≤neighboursIn G Aᶜ v)
    (hBA : ∀v∈Aᶜ,v∉E → δ≤neighboursIn G A v)
    (hδ : δ≤m) (hMargin : m+2*q≤2*δ) (hr : 0<r)
    (hrq : r≤q) (hrt : r+a≤t) (hScale : 4*r*m+2*m*a≤q*t) :
    IsBipartiteRobustAt G A r t := by
  exact ⟨expands_of_margin G A Aᶜ E m δ q r t a hA hB hE hAB hBA hδ hMargin hr hrq hrt hScale,
    expands_of_margin G Aᶜ A E m δ q r t a hB hA hE hBA hAB hδ hMargin hr hrq hrt hScale⟩

end OverfullWork.BipartiteRobustMargin
