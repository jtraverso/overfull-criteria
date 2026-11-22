module

public import OverfullWork.CaoChenCriticalAverageProof
public import OverfullWork.MaximumMatchingPeeling
public import OverfullWork.DenseSpanningPaths

@[expose] public section


/-! # Dense critical cores survive sparse trimming

The proved critical deficit estimate supplies a small exceptional set.
After deleting any subgraph of maximum degree at most k, the remaining
induced core still satisfies the explicit degree margin used for k
prescribed disjoint spanning paths. No spanning layout or colouring is
assumed or asserted here.
-/
namespace OverfullWork.CriticalDenseCoreTrimming
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
universe u
set_option maxHeartbeats 3000000

/-- The finite cost of deleting exceptional vertices and a sparse layer. -/
theorem core_residue_degree_margin {V : Type u} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H≤G) (a k : ℕ)
    (hU : (exceptions G G.maxDegree a).card≤k) (hH : H.maxDegree≤k)
    (hbudget : Fintype.card V+2*a+10*k+2≤2*G.maxDegree)
    (hsize : 4*k+5≤Fintype.card V) :
    let U:=exceptions G G.maxDegree a
    let K:=(G\H).induce ((U : Set V)ᶜ)
    Fintype.card ↥((U : Set V)ᶜ)+6*k+2≤2*K.minDegree ∧
      3*k+5≤Fintype.card ↥((U : Set V)ᶜ) := by
  classical
  let U:=exceptions G G.maxDegree a
  let K:=(G\H).induce ((U : Set V)ᶜ)
  change Fintype.card ↥((U : Set V)ᶜ)+6*k+2≤2*K.minDegree ∧
    3*k+5≤Fintype.card ↥((U : Set V)ᶜ)
  have hcard : Fintype.card ↥((U : Set V)ᶜ)=Fintype.card V-U.card := by
    rw [Fintype.card_compl_set]
    simp
  have hUk : U.card≤k := hU
  have hcoreSize : 3*k+5≤Fintype.card ↥((U : Set V)ᶜ) := by rw [hcard];omega
  have : Nonempty ↥((U : Set V)ᶜ) := Fintype.card_pos_iff.mp (by omega)
  have hlow : G.maxDegree-a-U.card-k≤K.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    have hg:=degree_add_threshold_of_not_exception G G.maxDegree a v.val v.property
    have hs:=MaximumMatching.degree_sdiff_add_of_le G H hHG v.val
    have hh:=(H.degree_le_maxDegree v.val).trans hH
    have hd:=degree_le_induce_compl_add_card (G\H) U v
    change (G\H).degree v.val≤K.degree v+U.card at hd
    omega
  constructor
  · rw [hcard]
    omega
  · exact hcoreSize

/-- Uniform critical graphs above one half have a core with enough room
for k prescribed paths, even after an arbitrary k-sparse edge deletion.
The exceptional set and all thresholds are selected before the deletion. -/
theorem above_half_critical_sparse_trimming (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let a:=Fintype.card V/(8*q)
        let k:=Fintype.card V/(4096*q^2)
        let U:=exceptions G G.maxDegree a
        0<k ∧ U.card≤k ∧
        ∀(H : SimpleGraph V) [DecidableRel H.Adj],H≤G → H.maxDegree≤k →
          let K:=(G\H).induce ((U : Set V)ᶜ)
          Fintype.card ↥((U : Set V)ᶜ)+6*k+2≤2*K.minDegree ∧
            3*k+5≤Fintype.card ↥((U : Set V)ᶜ) := by
  obtain ⟨q,hq⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hqNat : 2≤q := by
    have hh:=(le_max_left (2:ℝ) (1/ε)).trans_lt hq
    exact_mod_cast hh.le
  have hqe : (1:ℝ)≤(q:ℝ)*ε := by
    have hh:=(le_max_right (2:ℝ) (1/ε)).trans_lt hq
    exact ((div_lt_iff₀ hε).mp hh).le
  let η : ℝ:=1/(262144*(q:ℝ)^3)
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨D₀,hD⟩:=CaoChenCriticalAverage.deficit_bound.{u} η hη
  refine ⟨q,hqNat,max (4096*q^2) (2*D₀),?_⟩
  intro V _ _ G _ hn hc hdense
  let a:=Fintype.card V/(8*q)
  let k:=Fintype.card V/(4096*q^2)
  let U:=exceptions G G.maxDegree a
  change 0<k ∧ U.card≤k ∧ ∀(H : SimpleGraph V) [DecidableRel H.Adj],
    H≤G → H.maxDegree≤k →
      Fintype.card ↥((U : Set V)ᶜ)+6*k+2≤
        2*((G\H).induce ((U : Set V)ᶜ)).minDegree ∧
      3*k+5≤Fintype.card ↥((U : Set V)ᶜ)
  have hnscale : 4096*q^2≤Fintype.card V := (le_max_left _ _).trans hn
  have hnD : 2*D₀≤Fintype.card V := (le_max_right _ _).trans hn
  have hnDelta : Fintype.card V≤2*G.maxDegree := by
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by
      have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
      nlinarith only [hdense,he])
  have hD₀ : D₀≤G.maxDegree := by omega
  have hmass:=hD G hc hD₀
  have hDelta : (G.maxDegree:ℝ)≤(Fintype.card V:ℝ) := by
    exact_mod_cast G.maxDegree_le_of_forall_degree_le
      (Fintype.card V) (fun v => (G.degree_lt_card_verts v).le)
  have hmass' : (totalDeficit G G.maxDegree:ℝ)≤η*(Fintype.card V:ℝ)^2 := by
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDelta hη.le)
      (Nat.cast_nonneg (Fintype.card V) : (0:ℝ)≤(Fintype.card V:ℝ))
    nlinarith only [hmass,hh]
  have hmassInt:=RobustExpansion.integer_mass_budget_of_quadratic_bound
    (Fintype.card V) q (totalDeficit G G.maxDegree) (by omega) hmass'
  have hUk : U.card≤k :=
    RobustExpansion.exception_count_le_of_mass_lt G G.maxDegree a k hmassInt
  obtain ⟨hka,_,hra,_,_⟩:=RobustExpansion.sparse_deficit_integer_scales
    (Fintype.card V) q hqNat hnscale
  change k≤a at hka
  change 2*k+1≤a at hra
  have hkpos : 0<k := by
    change 0<Fintype.card V/(4096*q^2)
    exact Nat.div_pos hnscale (by positivity)
  have hafloor : 8*q*a≤Fintype.card V := Nat.mul_div_le (Fintype.card V) (8*q)
  have hfour : 4*a≤Fintype.card V :=
    (Nat.mul_le_mul_right a (by omega : 4≤8*q)).trans hafloor
  have hsize : 4*k+5≤Fintype.card V := by omega
  have hcost : 2*a+10*k+2≤8*a := by omega
  have hafloorR : 8*(q:ℝ)*(a:ℝ)≤(Fintype.card V:ℝ) := by exact_mod_cast hafloor
  have haeps : 8*(a:ℝ)≤ε*(Fintype.card V:ℝ) := by
    have hfirst:=mul_le_mul_of_nonneg_right hqe (by positivity : (0:ℝ)≤8*(a:ℝ))
    have hsecond:=mul_le_mul_of_nonneg_left hafloorR hε.le
    nlinarith only [hfirst,hsecond]
  have hcostR : 2*(a:ℝ)+10*(k:ℝ)+2≤8*(a:ℝ) := by exact_mod_cast hcost
  have hbudget : Fintype.card V+2*a+10*k+2≤2*G.maxDegree := by
    exact_mod_cast (show (Fintype.card V:ℝ)+2*(a:ℝ)+10*(k:ℝ)+2≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,haeps,hcostR])
  refine ⟨hkpos,hUk,?_⟩
  intro H _ hHG hH
  exact core_residue_degree_margin G H hHG a k hUk hH hbudget hsize

/-- Actual spanning paths, with prescribed distinct ends, in the core
of an above-half critical graph after any allowed sparse trimming.
Neither Hamilton-connectivity nor a layout is supplied as an input. -/
theorem above_half_critical_core_spanning_paths (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let k:=Fintype.card V/(4096*q^2)
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        0<k ∧ U.card≤k ∧
        ∀(H : SimpleGraph V) [DecidableRel H.Adj],H≤G → H.maxDegree≤k →
          let K:=(G\H).induce ((U : Set V)ᶜ)
          ∀(t : ℕ),t+1≤k →
          ∀(a b : Fin (t+1) → ↥((U : Set V)ᶜ)),
          (∀i j,a i≠b j) → Function.Injective a → Function.Injective b →
          ∃P : ∀i,K.Walk (a i) (b i),
            (∀i,(P i).IsPath) ∧
            (∀i j,i≠j → ∀v,v∈(P i).support → v∉(P j).support) ∧
            ∀v,∃i,v∈(P i).support := by
  obtain ⟨q,hq,N,hcore⟩:=above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro V _ _ G _ hn hc hdense
  obtain ⟨hk,hU,htrim⟩:=hcore G hn hc hdense
  refine ⟨hk,hU,?_⟩
  intro H _ hHG hH
  dsimp only
  intro t ht a b hab ha hb
  obtain ⟨hdeg,hsize⟩:=htrim H hHG hH
  exact DenseHamilton.exists_paths t _ a b hab ha hb (by omega) (by omega)

end OverfullWork.CriticalDenseCoreTrimming
