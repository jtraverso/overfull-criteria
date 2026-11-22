module

public import OverfullWork.UniformFactorization

@[expose] public section


/-! # Every fixed degree gap and every fixed positive density margin

The threshold is chosen before the vertex type and graph. It depends on
the fixed density margin; this is not the exact Delta>n/2 threshold.
-/
namespace OverfullWork.Gate8H2
open SimpleGraph
open scoped Classical
universe u

theorem eventually_parametric_fixed_gap (s c : ℕ) (hc : 1000*(2^(s+1)+max 1 s+1)≤c) :
    ∃ n₀ : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      n₀≤Fintype.card W → G.maxDegree-G.minDegree≤s →
      (c+64)*(Fintype.card W+1)≤2*c*G.maxDegree →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  have hb : 1≤max 1 s:=le_max_left _ _
  have hsb : s≤max 1 s:=le_max_right _ _
  have hpow : s+1≤2^(s+1):=(Nat.lt_two_pow_self).le
  obtain ⟨m₀,hfactor⟩:=exists_uniform_factorization_threshold.{u} (s+1) (max 1 s) c hb hc
  refine ⟨2*(max m₀ 2),?_⟩
  intro W _ _ G _ hsize hgap hdense
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hmmax : m₀≤max m₀ 2:=le_max_left _ _
  have htwo : 2≤max m₀ 2:=le_max_right _ _
  haveI : Nontrivial W:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hDup:=G.maxDegree_lt_card_verts
  rcases Nat.even_or_odd (Fintype.card W) with he|ho
  · obtain ⟨m,hmc⟩:=he
    have hm : m₀≤m:=by omega
    have hcard : Fintype.card W=2*m:=by omega
    have hD : G.maxDegree≤2*m:=by omega
    have hden : (c+64)*m≤c*G.maxDegree := by
      rw [hcard] at hdense
      nlinarith only [hdense,Nat.zero_le c]
    obtain ⟨x,y,hxy⟩:=exists_pair_ne W
    obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_even_bounded_completion
      G m s (by omega) hcard hno hgap
    obtain ⟨C,_⟩:=hfactor m hm M x y hxy G.maxDegree hcard hreg
      (fun e => (hmu e).trans hpow)
      (fun v _ => (hbudget v).trans hsb) (Or.inr ((hbudget x).trans hsb)) hD hden
    apply MultiGraph.edgeColourable_of_contained M G _ C
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b => exact hcontains a b ((mem_edgeSet G).mp he)
  · obtain ⟨k,hkc⟩:=ho
    let m:=k+1
    have hm : m₀≤m:=by dsimp [m];omega
    have hcard : Fintype.card W+1=2*m:=by dsimp [m];omega
    have hD : G.maxDegree≤2*m:=by omega
    have hden : (c+64)*m≤c*G.maxDegree := by
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
    obtain ⟨C,_⟩:=hfactor m hm M none (some y) (by simp) G.maxDegree hcM hreg
      (fun e => (hmu e).trans hpow) (fun v hv => (hbudget v hv).trans hsb) hcontrol hD hden
    exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

theorem eventually_above_half_fixed_gap_with_point (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      n₀≤Fintype.card W → G.maxDegree-G.minDegree≤s →
      ((1:ℝ)/2+ε)*(Fintype.card W+1:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨q,hq⟩:=exists_nat_gt ((32:ℝ)/ε)
  let c:=max (1000*(2^(s+1)+max 1 s+1)) q
  have hc : 1000*(2^(s+1)+max 1 s+1)≤c:=le_max_left _ _
  have hqc : (q:ℝ)≤(c:ℝ):=by exact_mod_cast (le_max_right (1000*(2^(s+1)+max 1 s+1)) q)
  have hεc : (32:ℝ)≤ε*(c:ℝ) := by
    have hh:=(div_lt_iff₀ hε).mp hq
    nlinarith
  obtain ⟨n₀,hn₀⟩:=eventually_parametric_fixed_gap.{u} s c hc
  refine ⟨n₀,?_⟩
  intro W _ _ G _ hs hg hd
  apply hn₀ G hs hg
  have hh:=mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤2*(c:ℝ) by positivity)
  have he:=mul_le_mul_of_nonneg_right hεc (Nat.cast_nonneg (Fintype.card W+1) (α:=ℝ))
  have hfinal : ((c+64:ℕ):ℝ)*(Fintype.card W+1:ℕ)≤2*(c:ℝ)*(G.maxDegree:ℝ) := by
    push_cast at *
    nlinarith only [hh,he]
  exact_mod_cast hfinal

/-- Fixed positive margins above n/2; the order threshold may depend on
epsilon, but is uniform over all vertex types and graphs. -/
theorem eventually_above_half_fixed_gap (s : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      n₀≤Fintype.card W → G.maxDegree-G.minDegree≤s →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨N,hN⟩:=eventually_above_half_fixed_gap_with_point.{u} s (ε/2) (by positivity)
  obtain ⟨Q,hQ⟩:=exists_nat_gt ((1+ε)/ε)
  refine ⟨max N Q,?_⟩
  intro W _ _ G _ hs hg hd
  have hn : N≤Fintype.card W:=(le_max_left _ _).trans hs
  have hq : (Q:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast (le_max_right N Q).trans hs
  have hlarge : 1+ε≤ε*(Fintype.card W:ℝ) := by
    have hh:=(div_lt_iff₀ hε).mp hQ
    nlinarith
  apply hN G hn hg
  push_cast
  nlinarith only [hd,hlarge]

end OverfullWork.Gate8H2
