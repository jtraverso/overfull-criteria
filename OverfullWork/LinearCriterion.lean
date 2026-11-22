module

public import OverfullWork.LinearFactorization
public import OverfullWork.GeometricCap

@[expose] public section


/-! # Linear growing-gap criterion from deterministic palettes in both parities -/
namespace OverfullWork.Gate8J2I
open SimpleGraph
open scoped Classical
universe u
set_option maxHeartbeats 4000000

/-- A finite numerical interface. The gap parameter s may vary with the
graph, and the coefficient C is independent of s. -/
theorem linear_gap_criterion {W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (C s : ℕ) (hC : 4000≤C)
    (hsize : 2*linearHalfBound C (s+1)≤Fintype.card W)
    (hgap : G.maxDegree-G.minDegree≤s)
    (hdense : (C+64)*(Fintype.card W+1)≤2*C*G.maxDegree) :
    (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by

  have hsb : s≤max 1 s:=le_max_right _ _
  have hbS : max 1 s≤s+1:=by omega
  obtain ⟨j,hpow,hcap,_,_,_,_,_⟩:=Gate8J2C.exists_geometric_cap s
  have hCpos : 0<C:=by omega
  have hpolypos : 0<linearHalfBound C (s+1):=by
    unfold linearHalfBound
    positivity
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  haveI : Nontrivial W:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hDup:=G.maxDegree_lt_card_verts
  rcases Nat.even_or_odd (Fintype.card W) with he|ho
  · obtain ⟨m,hmc⟩:=he
    have hm : linearHalfBound C (s+1)≤m:=by omega
    have hcard : Fintype.card W=2*m:=by omega
    have hD : G.maxDegree≤2*m:=by omega
    have hden : (C+64)*m≤C*G.maxDegree := by
      rw [hcard] at hdense
      nlinarith only [hdense,Nat.zero_le C]
    obtain ⟨x,y,hxy⟩:=exists_pair_ne W
    obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_even_bounded_completion
      G m s (by omega) hcard hno hgap
    obtain ⟨F,_⟩:=linear_centre_factorization M x y hxy C (s+1) j (max 1 s) m
      G.maxDegree hC (by omega) hpow hcap hbS hm hcard hreg
      (fun e => (hmu e).trans hpow)
      (fun v _ => (hbudget v).trans hsb) (Or.inr ((hbudget x).trans hsb)) hD hden
    apply MultiGraph.edgeColourable_of_contained M G _ F
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b => exact hcontains a b ((mem_edgeSet G).mp he)
  · obtain ⟨k,hkc⟩:=ho
    let m:=k+1
    have hm : linearHalfBound C (s+1)≤m:=by dsimp [m];omega
    have hcard : Fintype.card W+1=2*m:=by dsimp [m];omega
    have hD : G.maxDegree≤2*m:=by omega
    have hden : (C+64)*m≤C*G.maxDegree := by
      rw [hcard] at hdense
      nlinarith only [hdense]
    have hn : Odd (Fintype.card W):=⟨k,hkc⟩
    have hedge:=DegreeBudget.edge_bound_of_no_overfull G hn hno
    obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_odd_bounded_extension
      G m s (by omega) hcard hedge hgap
    have hcontrol : M.CentreControl none (max 1 s) := by
      apply Or.inl
      intro w
      cases w with
      | none => rw [M.loopless s(none,none) (by simp)];exact Nat.zero_le _
      | some v =>
        have hh:=GeneralRegularization.centre_mult_le_deficit G M G.maxDegree hreg hcontains v
        have hmin:=G.minDegree_le_degree v
        omega
    obtain ⟨y⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card W by omega)
    have hcM : Fintype.card (Option W)=2*m:=by simpa using hcard
    obtain ⟨F,_⟩:=linear_centre_factorization M none (some y) (by simp) C (s+1) j (max 1 s) m
      G.maxDegree hC (by omega) hpow hcap hbS hm hcM hreg
      (fun e => (hmu e).trans hpow) (fun v hv => (hbudget v hv).trans hsb) hcontrol hD hden
    exact MultigraphExtension.edgeColourable_of_regularized_colouring G M F hcontains


/-- The coefficient is fixed before every graph, while its actual degree
gap is allowed to grow. This is stronger than a separate threshold for
each fixed gap. -/
theorem above_half_linear_gap (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℕ,0<A ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      A*(G.maxDegree-G.minDegree+1)≤Fintype.card W →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨q,hq⟩:=exists_nat_gt ((64:ℝ)/ε)
  let C:=max 4000 q
  have hC : 4000≤C:=le_max_left _ _
  have hCpos : 0<C:=by omega
  have hqC : (q:ℝ)≤(C:ℝ):=by exact_mod_cast (le_max_right 4000 q)
  have hεC : (64:ℝ)≤ε*(C:ℝ) := by
    have hh:=(div_lt_iff₀ hε).mp hq
    nlinarith
  obtain ⟨Q,hQ⟩:=exists_nat_gt ((1+ε)/ε)
  let K:=2*(10:ℕ)^24*C^6
  have hKpos : 0<K:=by dsimp [K];positivity
  let A:=max K Q
  have hKA : K≤A:=le_max_left _ _
  have hQA : Q≤A:=le_max_right _ _
  refine ⟨A,lt_of_lt_of_le hKpos hKA,?_⟩
  intro W _ _ G _ hsize hdense
  have hpow : 1≤(G.maxDegree-G.minDegree+1):=by omega
  have hAn : A≤Fintype.card W := by
    calc
      A = A*1:=by omega
      _ ≤ A*(G.maxDegree-G.minDegree+1):=Nat.mul_le_mul_left A hpow
      _ ≤ _:=hsize
  have hQn : (Q:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast hQA.trans hAn
  have hlarge : 1+ε≤ε*(Fintype.card W:ℝ) := by
    have hh:=(div_lt_iff₀ hε).mp hQ
    nlinarith only [hh,hQn,hε]
  have hfiniteSize : 2*linearHalfBound C (G.maxDegree-G.minDegree+1)≤Fintype.card W := by
    have hmul:=(Nat.mul_le_mul_right ((G.maxDegree-G.minDegree+1)) hKA).trans hsize
    simpa only [linearHalfBound,K,Nat.mul_assoc] using hmul
  apply linear_gap_criterion G C (G.maxDegree-G.minDegree) hC hfiniteSize le_rfl
  have hh:=mul_le_mul_of_nonneg_left hdense (show (0:ℝ)≤2*(C:ℝ) by positivity)
  have he₁:=mul_le_mul_of_nonneg_right hεC (Nat.cast_nonneg (Fintype.card W) (α:=ℝ))
  have he₂:=mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg C (α:=ℝ))
  have hfinal : ((C+64:ℕ):ℝ)*(Fintype.card W+1:ℕ)≤2*(C:ℝ)*(G.maxDegree:ℝ) := by
    push_cast at *
    nlinarith only [hh,he₁,he₂,hεC]
  exact_mod_cast hfinal

end OverfullWork.Gate8J2I
