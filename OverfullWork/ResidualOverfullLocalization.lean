module

public import OverfullWork.TrimmingResidualOddGeometry
public import OverfullWork.CaoChenCriticalAverageProof

@[expose] public section


/-! # A residual overfull set has a tiny star complement

No preservation of absence of overfull sets is assumed. An actual odd
overfull set in the degree-lowered residue is localized using its cut,
the original degree deficits and criticality. The final uniform theorem
uses the proved critical deficit bound, with all choices before the graph.
-/
namespace OverfullWork.ResidualOverfullLocalization
open SimpleGraph Finset OddCutDeficit SparseDeficitCore
open TrimmingResidualOddGeometry NearTightOddSetGeometry
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- A simple overfull odd set in a D-2 residue has at least D-1 vertices. -/
theorem degree_le_overfull_card_add_one (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hD : 2≤G.maxDegree)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X) :
    G.maxDegree≤X.card+1 := by
  have hc:=internalEdges_le_card_mul_half (G\L) X hodd
  have hmul : (G.maxDegree-2)*(X.card/2)<X.card*(X.card/2):=hof.trans_le hc
  have hd : G.maxDegree-2<X.card := by
    by_contra hn
    have hh:=Nat.mul_le_mul_right (X.card/2) (Nat.le_of_not_gt hn)
    omega
  omega

/-- The complement's vertices outside the exceptional set must all spend
from the same residual cut. -/
theorem high_complement_mass_le_cut (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G)
    (hL : L.maxDegree≤2) (a : ℕ) (X : Finset V)
    (hgap : a+Xᶜ.card+a+1≤G.maxDegree) :
    a*(Xᶜ\exceptions G G.maxDegree a).card≤cutEdges (G\L) X := by
  let A:=Xᶜ\exceptions G G.maxDegree a
  have hs:=selected_degree_sum_le_cut_add G L hLG hL X A sdiff_subset
  have hd : G.maxDegree*A.card≤(∑v∈A,G.degree v)+a*A.card := by
    calc
      _ = ∑_v∈A,G.maxDegree := by simp [Nat.mul_comm]
      _ ≤ ∑v∈A,(G.degree v+a) := sum_le_sum (fun v hv =>
        degree_add_threshold_of_not_exception G G.maxDegree a v (mem_sdiff.mp hv).2)
      _ = _ := by simp [sum_add_distrib,Nat.mul_comm]
  have hm:=Nat.mul_le_mul_right A.card hgap
  nlinarith only [hs,hd,hm]

/-- Two nonexceptional complementary vertices already exceed the cut
budget. This sharper conclusion follows after the complement is small. -/
theorem high_complement_card_le_one (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G)
    (hL : L.maxDegree≤2) (hD : 2≤G.maxDegree)
    (hR : ∀v,(G\L).degree v≤G.maxDegree-2)
    (a : ℕ) (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X)
    (hsmall : 2*a+2*Xᶜ.card≤G.maxDegree) :
    (Xᶜ\exceptions G G.maxDegree a).card≤1 := by
  apply card_le_one.mpr
  intro u hu v hv
  by_contra hne
  let A:Finset V:={u,v}
  have hA : A⊆Xᶜ := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact (mem_sdiff.mp hu).1
    · have he:=mem_singleton.mp hz
      subst z
      exact (mem_sdiff.mp hv).1
  have hs:=selected_degree_sum_le_cut_add G L hLG hL X A hA
  have hcard:A.card=2:=by simp [A,hne]
  have hsum:(∑z∈A,G.degree z)=G.degree u+G.degree v:=by simp [A,hne]
  rw [hcard,hsum] at hs
  have hdu:=degree_add_threshold_of_not_exception G G.maxDegree a u (mem_sdiff.mp hu).2
  have hdv:=degree_add_threshold_of_not_exception G G.maxDegree a v (mem_sdiff.mp hv).2
  have hcut:=residual_overfull_cut_bound G L hD hR X hodd hof
  omega

/-- Finite localization at the integer scales used by the actual layer.
The complement is tiny, has at most one nonexceptional vertex, and its
original edges form a star (or the complement is empty). -/
theorem finite_localization (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj]
    (hc : Overfull.IsDeltaCritical G) (hLG : L≤G) (hL : L.maxDegree≤2)
    (hD : 2≤G.maxDegree) (hR : ∀v,(G\L).degree v≤G.maxDegree-2)
    (a k q : ℕ) (ha : 0<a) (hUk : (exceptions G G.maxDegree a).card≤k)
    (hgap : Fintype.card V+2*a+2≤2*G.maxDegree)
    (hlower : Fintype.card V≤16*q*a) (hk : 16*q≤k)
    (hscale : 2*k+1≤a) (hDscale : 8*a≤G.maxDegree)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X) :
    G.maxDegree≤X.card+1 ∧ cutEdges (G\L) X+3≤G.maxDegree ∧
      Xᶜ.card≤2*k ∧ (Xᶜ\exceptions G G.maxDegree a).card≤1 ∧
      (Xᶜ=∅ ∨ ∃v∈Xᶜ,∀u∈Xᶜ,∀w∈Xᶜ,G.Adj u w → u=v ∨ w=v) := by
  have hsize:=degree_le_overfull_card_add_one G L hD X hodd hof
  have hcut:=residual_overfull_cut_bound G L hD hR X hodd hof
  have hcard:X.card+Xᶜ.card=Fintype.card V:=by simp
  have hmass:=high_complement_mass_le_cut G L hLG hL a X (by omega)
  have hDn : G.maxDegree≤Fintype.card V :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => (G.degree_lt_card_verts v).le)
  have hhigh : (Xᶜ\exceptions G G.maxDegree a).card≤16*q := by
    have hm : a*(Xᶜ\exceptions G G.maxDegree a).card≤a*(16*q) := by
      nlinarith only [hmass,hcut,hDn,hlower]
    exact Nat.le_of_mul_le_mul_left hm ha
  have htotal : Xᶜ.card≤2*k := by
    have hh:=card_le_card_sdiff_add_card (s:=Xᶜ) (t:=exceptions G G.maxDegree a)
    omega
  have hhighone:=high_complement_card_le_one G L hLG hL hD hR a X hodd hof (by omega)
  refine ⟨hsize,hcut,htotal,hhighone,?_⟩
  rcases Xᶜ.eq_empty_or_nonempty with he|hne
  · exact Or.inl he
  · right
    apply complement_edges_have_common_vertex G L hLG hL hD hR 0 _ X hodd hof _ hne
    · intro u v huv
      have hh:=Overfull.deg_add hc huv
      omega
    · omega

universe u

/-- G1 discharges the mass hypothesis uniformly. Every actual residual
overfull odd set then has a tiny star complement, with at most one vertex
outside the same small exceptional set. No property of the residual
beyond the explicitly achieved degree drop is postulated. -/
theorem above_half_residual_overfull_localization (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let a:=Fintype.card W/(8*q)
        let k:=Fintype.card W/(4096*q^2)
        let U:=exceptions G G.maxDegree a
        U.card≤k ∧
        ∀(L : SimpleGraph W) [DecidableRel L.Adj],L≤G → L.maxDegree≤2 →
          (G\L).maxDegree=G.maxDegree-2 →
          ∀X : Finset W,Odd X.card →
            (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X →
            G.maxDegree≤X.card+1 ∧ cutEdges (G\L) X+3≤G.maxDegree ∧
              Xᶜ.card≤2*k ∧ (Xᶜ\U).card≤1 ∧
              (Xᶜ=∅ ∨ ∃v∈Xᶜ,∀u∈Xᶜ,∀w∈Xᶜ,G.Adj u w → u=v ∨ w=v) := by
  obtain ⟨q,hq⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hqNat : 2≤q := by
    have hh:=(le_max_left (2:ℝ) (1/ε)).trans_lt hq
    exact_mod_cast hh.le
  have hqe : (1:ℝ)≤(q:ℝ)*ε := by
    have hh:=(le_max_right (2:ℝ) (1/ε)).trans_lt hq
    exact ((div_lt_iff₀ hε).mp hh).le
  let η:ℝ:=1/(262144*(q:ℝ)^3)
  have hη:0<η:=by dsimp [η];positivity
  obtain ⟨D₀,hDef⟩:=CaoChenCriticalAverage.deficit_bound.{u} η hη
  refine ⟨q,hqNat,max (16*q*(4096*q^2)) (2*D₀),?_⟩
  intro W _ _ G _ hn hc hdense
  let n:=Fintype.card W
  let a:=n/(8*q)
  let k:=n/(4096*q^2)
  let U:=exceptions G G.maxDegree a
  change U.card≤k ∧ _
  have hnscale : 16*q*(4096*q^2)≤n := (le_max_left _ _).trans hn
  have hnD : 2*D₀≤n := (le_max_right _ _).trans hn
  have hnbase : 4096*q^2≤n := by
    have hh:=Nat.mul_le_mul_right (4096*q^2) (show 1≤16*q by omega)
    omega
  have hk : 16*q≤k := (Nat.le_div_iff_mul_le (by positivity)).mpr hnscale
  have hnDelta : n≤2*G.maxDegree := by
    have hh:0≤ε*(n:ℝ):=by positivity
    exact_mod_cast (show (n:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hh])
  have hD₀ : D₀≤G.maxDegree := by omega
  have hmass:=hDef G hc hD₀
  have hDn:G.maxDegree≤n:=G.maxDegree_le_of_forall_degree_le n
    (fun v => (G.degree_lt_card_verts v).le)
  have hDnR:(G.maxDegree:ℝ)≤(n:ℝ):=by exact_mod_cast hDn
  have hmassQ:(totalDeficit G G.maxDegree:ℝ)≤η*(n:ℝ)^2:=by
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDnR hη.le) (Nat.cast_nonneg n)
    nlinarith only [hmass,hh]
  have hmassInt:=RobustExpansion.integer_mass_budget_of_quadratic_bound n q
    (totalDeficit G G.maxDegree) (by omega) hmassQ
  have hUk:U.card≤k:=RobustExpansion.exception_count_le_of_mass_lt G G.maxDegree a k hmassInt
  obtain ⟨_,_,hscale,_,_⟩:=RobustExpansion.sparse_deficit_integer_scales n q hqNat hnbase
  change 2*k+1≤a at hscale
  have ha:0<a:=by omega
  have haf:8*q*a≤n:=Nat.mul_div_le n (8*q)
  have h16:16*a≤n:=(Nat.mul_le_mul_right a (show 16≤8*q by omega)).trans haf
  have hDscale:8*a≤G.maxDegree:=by omega
  have hafR:8*(q:ℝ)*(a:ℝ)≤(n:ℝ):=by exact_mod_cast haf
  have haeps:8*(a:ℝ)≤ε*(n:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right hqe
      (show 0≤8*(a:ℝ) by positivity)
    have hh2:=mul_le_mul_of_nonneg_left hafR hε.le
    nlinarith only [hh,hh2]
  have hgap:n+2*a+2≤2*G.maxDegree:=by
    have hhR:(1:ℝ)≤(a:ℝ):=by exact_mod_cast ha
    exact_mod_cast (show (n:ℝ)+2*(a:ℝ)+2≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,haeps,hhR])
  have halower:n≤16*q*a:=by
    have hh:=Nat.lt_mul_div_succ n (show 0<8*q by positivity)
    change n<8*q*(a+1) at hh
    have hm:=Nat.mul_le_mul_left (8*q) (show 1≤a by omega)
    nlinarith only [hh,hm]
  refine ⟨hUk,?_⟩
  intro L _ hLG hL hR X hodd hof
  apply finite_localization G L hc hLG hL (by omega) _ a k q ha hUk hgap
    halower hk hscale hDscale X hodd hof
  intro v
  rw [←hR]
  exact (G\L).degree_le_maxDegree v

/-- A residual overfull subgraph supplies an actual odd witness with
the localized stop geometry. Even witnesses are excluded by the degree
identity, rather than postulated away. -/
theorem above_half_residual_overfull_stop (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let a:=Fintype.card W/(8*q)
        let k:=Fintype.card W/(4096*q^2)
        let U:=exceptions G G.maxDegree a
        U.card≤k ∧
        ∀(L : SimpleGraph W) [DecidableRel L.Adj],L≤G → L.maxDegree≤2 →
          (G\L).maxDegree=G.maxDegree-2 → (G\L).HasOverfullSubgraph →
          ∃X : Finset W,Odd X.card ∧
            (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X ∧
            G.maxDegree≤X.card+1 ∧ cutEdges (G\L) X+3≤G.maxDegree ∧
              Xᶜ.card≤2*k ∧ (Xᶜ\U).card≤1 ∧
              (Xᶜ=∅ ∨ ∃v∈Xᶜ,∀u∈Xᶜ,∀w∈Xᶜ,G.Adj u w → u=v ∨ w=v) := by
  obtain ⟨q,hq,N,hN⟩:=above_half_residual_overfull_localization.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro W _ _ G _ hn hc hdense
  obtain ⟨hUk,hlocal⟩:=hN G hn hc hdense
  refine ⟨hUk,?_⟩
  intro L _ hLG hL hR hOF
  obtain ⟨X,hof⟩:=hOF
  change (G\L).maxDegree*(X.card/2)< internalEdges (G\L) X at hof
  rw [hR] at hof
  have hodd : Odd X.card := by
    by_contra hnodd
    have heven:=Nat.not_odd_iff_even.mp hnodd
    have hb:=even_internal_bound (G\L) (G.maxDegree-2)
      (fun v => by rw [←hR];exact (G\L).degree_le_maxDegree v) X heven
    omega
  exact ⟨X,hodd,hof,hlocal L hLG hL hR X hodd hof⟩

end OverfullWork.ResidualOverfullLocalization
