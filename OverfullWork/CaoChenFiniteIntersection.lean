module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Finset.Max

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # The finite double-counting core of Cao--Chen Lemma 9

Counting pairs consisting of a family index and an r-subset constructs
the common intersection; no intersection hypothesis is postulated.
-/
namespace OverfullWork.CaoChenFiniteIntersection
open Finset
open scoped Classical
variable {α β : Type*} [DecidableEq β]

/-- A strict binomial incidence bound forces k distinct family indices
whose sets contain the same r-subset.  Indices are represented by a
finset of cardinality k, so repeated family sets cause no difficulty. -/
theorem exists_common_subset_of_choose_bound
    (I : Finset α) (U : Finset β) (A : α → Finset β) (k a r : ℕ)
    (hsub : ∀ i∈I,A i⊆U) (hcard : ∀ i∈I,a≤(A i).card)
    (hcount : (k-1)*Nat.choose U.card r<I.card*Nat.choose a r) :
    ∃ J : Finset α,J⊆I ∧ J.card=k ∧
      ∃ S : Finset β,S⊆U ∧ S.card=r ∧ ∀ i∈J,S⊆A i := by
  let C := U.powersetCard r
  let rel : α → Finset β → Prop := fun i S => S⊆A i
  have hrow (i : α) (hi : i∈I) :
      Nat.choose a r≤(C.bipartiteAbove rel i).card := by
    have heq : C.bipartiteAbove rel i=(A i).powersetCard r := by
      ext S
      simp only [mem_bipartiteAbove,mem_powersetCard,C,rel]
      constructor
      · intro h
        exact ⟨h.2,h.1.2⟩
      · intro h
        exact ⟨⟨h.1.trans (hsub i hi),h.2⟩,h.1⟩
    rw [heq,card_powersetCard]
    exact Nat.choose_le_choose r (hcard i hi)
  have hex : ∃ S∈C,k≤(I.bipartiteBelow rel S).card := by
    by_contra hno
    have hcol (S : Finset β) (hS : S∈C) :
        (I.bipartiteBelow rel S).card≤k-1 := by
      have hn : ¬k≤(I.bipartiteBelow rel S).card := fun h => hno ⟨S,hS,h⟩
      exact Nat.le_sub_one_of_lt (Nat.lt_of_not_ge hn)
    have hb := Finset.card_mul_le_card_mul rel hrow hcol
    have hb' : I.card*Nat.choose a r≤Nat.choose U.card r*(k-1) := by
      simpa only [C,card_powersetCard] using hb
    exact (Nat.not_lt_of_ge hb') (by simpa only [Nat.mul_comm] using hcount)
  obtain ⟨S,hS,hfiber⟩ := hex
  obtain ⟨J,hJ,hJcard⟩ := Finset.exists_subset_card_eq hfiber
  obtain ⟨hSU,hScard⟩ := mem_powersetCard.mp hS
  refine ⟨J,?_,hJcard,S,hSU,hScard,?_⟩
  · intro i hi
    exact (mem_filter.mp (hJ hi)).1
  · intro i hi
    exact (mem_filter.mp (hJ hi)).2

/-- Comparison of descending factorials cancels the factorial denominator
without using division or rounded real binomial coefficients. -/
theorem choose_le_pow_mul_choose_of_factor_bounds (N a Q r : ℕ)
    (hfactor : ∀ i<r,N-i≤Q*(a-i)) :
    Nat.choose N r≤Q^r*Nat.choose a r := by
  have hdesc : N.descFactorial r≤Q^r*a.descFactorial r := by
    induction r with
    | zero => simp
    | succ r ih =>
      have hi := ih (fun i hi => hfactor i (Nat.lt_succ_of_lt hi))
      have hf := hfactor r (Nat.lt_succ_self r)
      rw [Nat.descFactorial_succ,Nat.descFactorial_succ,pow_succ]
      calc
        (N-r)*N.descFactorial r≤(Q*(a-r))*(Q^r*a.descFactorial r) :=
          Nat.mul_le_mul hf hi
        _ = _ := by ring
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hh : r.factorial*Nat.choose N r≤r.factorial*(Q^r*Nat.choose a r) := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hdesc
  exact Nat.le_of_mul_le_mul_left hh (Nat.factorial_pos r)

/-- The integer reciprocal-density estimate used in Lemma 9:
if a set has at least a 1/q fraction of the universe, and the universe
has at least r*q² points, the binomial ratio is at most (q+1)^r. -/
theorem choose_le_reciprocal_density_power (N a q r : ℕ)
    (hq : 1≤q) (hN : N≤q*a) (hr : r*q*q≤N) :
    Nat.choose N r≤(q+1)^r*Nat.choose a r := by
  have hqa : r*q≤a := by
    apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
    calc
      q*(r*q)=r*q*q := by ring
      _≤N := hr
      _≤q*a := hN
  apply choose_le_pow_mul_choose_of_factor_bounds
  intro i hi
  have hiq : i*q≤a := (Nat.mul_le_mul_right q (Nat.le_of_lt hi)).trans hqa
  have hia : i≤a := by
    calc
      i=i*1 := by simp
      _≤i*q := Nat.mul_le_mul_left i hq
      _≤a := hiq
  have hs : a-i+i=a := Nat.sub_add_cancel hia
  have hm : (a-i)*q+i*q=a*q := by rw [←Nat.add_mul,hs]
  apply Nat.sub_le_iff_le_add.mpr
  nlinarith only [hN,hiq,hs,hm]

/-- A fully integer version of Cao--Chen Lemma 9, with density 1/q.
The chosen indices are distinct and the common r-subset is constructed. -/
theorem exists_common_subset_of_reciprocal_density
    (I : Finset α) (U : Finset β) (A : α → Finset β) (k a q r : ℕ)
    (hq : 1≤q) (hsub : ∀ i∈I,A i⊆U) (hcard : ∀ i∈I,a≤(A i).card)
    (hU : U.card≤q*a) (hr : r*q*q≤U.card)
    (hfamily : (k-1)*(q+1)^r<I.card) :
    ∃ J : Finset α,J⊆I ∧ J.card=k ∧
      ∃ S : Finset β,S⊆U ∧ S.card=r ∧ ∀ i∈J,S⊆A i := by
  have hqa : r*q≤a := by
    apply Nat.le_of_mul_le_mul_left (c:=q) _ (by omega)
    calc
      q*(r*q)=r*q*q := by ring
      _≤U.card := hr
      _≤q*a := hU
  have hra : r≤a := by
    exact (show r≤r*q by simpa using Nat.mul_le_mul_left r hq).trans hqa
  have hpos := Nat.choose_pos hra
  have hb := choose_le_reciprocal_density_power U.card a q r hq hU hr
  apply exists_common_subset_of_choose_bound I U A k a r hsub hcard
  calc
    (k-1)*Nat.choose U.card r≤(k-1)*((q+1)^r*Nat.choose a r) :=
      Nat.mul_le_mul_left (k-1) hb
    _ = ((k-1)*(q+1)^r)*Nat.choose a r := by ring
    _ < I.card*Nat.choose a r := Nat.mul_lt_mul_of_pos_right hfamily hpos

/-- The reciprocal-density formulation without a separately supplied
minimum cardinality.  A smallest member of the finite family supplies it. -/
theorem exists_common_subset_of_fraction_bound
    (I : Finset α) (U : Finset β) (A : α → Finset β) (k q r : ℕ)
    (hq : 1≤q) (hsub : ∀ i∈I,A i⊆U)
    (hdensity : ∀ i∈I,U.card≤q*(A i).card) (hr : r*q*q≤U.card)
    (hfamily : (k-1)*(q+1)^r<I.card) :
    ∃ J : Finset α,J⊆I ∧ J.card=k ∧
      ∃ S : Finset β,S⊆U ∧ S.card=r ∧ ∀ i∈J,S⊆A i := by
  have hI : I.Nonempty := card_pos.mp (by omega)
  obtain ⟨i,hi,hmin⟩ := I.exists_min_image (fun j => (A j).card) hI
  exact exists_common_subset_of_reciprocal_density I U A k (A i).card q r
    hq hsub hmin (hdensity i hi) hr hfamily

/-- The graph-free exceptional-set consequence used in Corollary 10.
If k members never share an r-subset, only a bounded number of members
can have reciprocal density at least 1/q.  Their complement is strictly
smaller than that density threshold. -/
theorem exists_exceptional_set_of_no_common_subset
    (I : Finset α) (U : Finset β) (A : α → Finset β) (k q r : ℕ)
    (hq : 1≤q) (hsub : ∀ i∈I,A i⊆U) (hr : r*q*q≤U.card)
    (havoid : ∀ J : Finset α,J⊆I → J.card=k →
      ∀ S : Finset β,S⊆U → S.card=r → ¬∀ i∈J,S⊆A i) :
    ∃ X : Finset α,X⊆I ∧ X.card≤(k-1)*(q+1)^r ∧
      ∀ i∈I\X,q*(A i).card<U.card := by
  let X := I.filter fun i => U.card≤q*(A i).card
  have hXI : X⊆I := filter_subset _ _
  have hbound : X.card≤(k-1)*(q+1)^r := by
    by_contra hn
    have hlarge : (k-1)*(q+1)^r<X.card := Nat.lt_of_not_ge hn
    obtain ⟨J,hJ,hJcard,S,hSU,hScard,hcommon⟩ :=
      exists_common_subset_of_fraction_bound X U A k q r hq
        (fun i hi => hsub i (hXI hi))
        (fun i hi => (mem_filter.mp hi).2) hr hlarge
    exact havoid J (hJ.trans hXI) hJcard S hSU hScard hcommon
  refine ⟨X,hXI,hbound,?_⟩
  intro i hi
  obtain ⟨hiI,hiX⟩ := mem_sdiff.mp hi
  have hn : ¬U.card≤q*(A i).card := by
    intro h
    exact hiX (mem_filter.mpr ⟨hiI,h⟩)
  exact Nat.lt_of_not_ge hn

end OverfullWork.CaoChenFiniteIntersection
