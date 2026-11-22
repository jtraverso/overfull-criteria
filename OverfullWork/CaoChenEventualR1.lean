module

public import OverfullWork.CaoChenMediumDischarge
public import OverfullWork.CaoChenNearFullDischarge
public import OverfullWork.CaoChenSmallRootDischarge

@[expose] public section


/-! # Eventual R1 at every root degree above a fixed cutoff

One reciprocal integer serves the small-root bound and Lemmas 7--8. A
second integer controls the exceptional palette density. All parameters
and the maximum-degree threshold are chosen before the graph.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
universe u
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- Small, near-full, and large-deficit regimes exhaust the root degrees.
The palette and exceptional-family inputs have been proved, not assumed. -/
theorem R1_charge_of_palette_parameters (hcrit : IsDeltaCritical G)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hεk : 2≤ε*(k:ℝ)) (Q : ℕ) (hQ : 1≤Q) (hεQ : 32≤ε^3*(Q:ℝ))
    (hcutoff : (CaoChenUniformPaletteBudgets.cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hsize : (3*k+1)*Q*Q≤G.maxDegree) (hDQ : Q≤G.maxDegree)
    (hmass : 8*(((k+1)*(Q+1)^(3*k+1):ℕ):ℝ)+8/ε≤ε^2*(G.maxDegree:ℝ))
    (x : V) (hlarge : 2*(k+2)^4≤G.degree x) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  by_cases hxhi : (G.degree x:ℝ)<q
  · by_cases hxsmall : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2
    · exact small_root_R1_charge hcrit ε hε k hk hεk x hlarge hxsmall
    · have hxlo : ε*(G.maxDegree:ℝ)/2≤(G.degree x:ℝ):=(lt_of_not_ge hxsmall).le
      have hpos : 0<G.degree x := by
        have hp : 0<(k+2)^4 := by positivity
        omega
      obtain ⟨v,hv⟩:=(G.degree_pos_iff_exists_adj x).mp hpos
      have hne : (G.neighborFinset x).Nonempty:=⟨v,(mem_neighborFinset G x v).mpr hv⟩
      obtain ⟨y,hy,hmin⟩:=(G.neighborFinset x).exists_min_image (fun y => highCount G q y) hne
      have hxy : G.Adj x y := (mem_neighborFinset G x y).mp hy
      let s:=G.maxDegree-highCount G q y
      have hcnt:=lowCount_add_highCount G q y
      have hlpos:=lowCount_positive_of_low_neighbour G q hxy hxhi
      have hdy:=G.degree_le_maxDegree y
      have hsum : s+highCount G q y=G.maxDegree := by dsimp [s];omega
      have hs : 0<s := by dsimp [s];omega
      by_cases hsmall : (s:ℝ)≤ε^2*(G.maxDegree:ℝ)/4
      · apply charge_ge_of_near_full_half_margin G ε hε hεone s hs hsmall x hxlo hxhi
        intro z hxz
        have hh:=hmin z ((mem_neighborFinset G x z).mpr hxz)
        have hbound : G.maxDegree≤highCount G q z+s := by omega
        exact hbound
      · obtain ⟨c,hcm⟩:=exists_colMinus_of_colorable hxy
          (hcrit.2.2 s(x,y) ((mem_edgeSet G).mpr hxy))
        have hscale : 1≤ε*((k+1:ℕ):ℝ) := by push_cast;nlinarith only [hεk,hε]
        have hmass' : 8*((((k+1)*(Q+1)^(3*k+1):ℕ):ℝ)+1/ε)≤ε^2*(G.maxDegree:ℝ) := by
          convert hmass using 1
          ring
        exact charge_ge_of_large_high_count_deficit hcrit.2.1 c hcm ε hε hεone k hk hxhi
          hscale hcutoff Q hQ hsize hDQ hεQ hmass' (lt_of_not_ge hsmall)
  · exact high_charge_ge_threshold G q x (le_of_not_gt hxhi)

/-- Eventual R1 on every vertex of degree at least d. The integer d and
the maximum-degree threshold N depend only on epsilon and precede the
vertex type, graph and vertex. No structural R1 hypothesis remains. -/
theorem eventual_R1 (ε : ℝ) (hε : 0<ε) (hεone : ε<1) :
    ∃d N : ℕ,2≤d ∧
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        IsDeltaCritical G → N≤G.maxDegree → ∀x,d≤G.degree x →
          (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  obtain ⟨k,hk⟩:=exists_nat_gt (max 1 (2/ε))
  have hkNat : 1≤k := by
    have hh : (1:ℝ)<(k:ℝ):=lt_of_le_of_lt (le_max_left _ _) hk
    exact_mod_cast hh.le
  have hεk : 2≤ε*(k:ℝ) := by
    have hh : 2/ε<(k:ℝ):=lt_of_le_of_lt (le_max_right _ _) hk
    have hm:=(div_lt_iff₀ hε).mp hh
    nlinarith only [hm]
  have hεcube : 0<ε^3 := by positivity
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max 1 (32/ε^3))
  have hQNat : 1≤Q := by
    have hh : (1:ℝ)<(Q:ℝ):=lt_of_le_of_lt (le_max_left _ _) hQ
    exact_mod_cast hh.le
  have hεQ : 32≤ε^3*(Q:ℝ) := by
    have hh : 32/ε^3<(Q:ℝ):=lt_of_le_of_lt (le_max_right _ _) hQ
    have hm:=(div_lt_iff₀ hεcube).mp hh
    nlinarith only [hm]
  let E:ℕ:=(k+1)*(Q+1)^(3*k+1)
  let R:ℝ:=max ((CaoChenUniformPaletteBudgets.cutoff k:ℝ)/ε^2)
    ((8*(E:ℝ)+8/ε)/ε^2)
  obtain ⟨B,hB⟩:=exists_nat_ge R
  let N:=max B (max Q ((3*k+1)*Q*Q))
  refine ⟨2*(k+2)^4,N,?_,?_⟩
  · have hp : 0<(k+2)^4 := by positivity
    omega
  · intro W _ _ G _ hcrit hN x hx
    have hBD : B≤G.maxDegree:=(le_max_left B _).trans hN
    have hQD : Q≤G.maxDegree:=(le_max_left Q _).trans ((le_max_right B _).trans hN)
    have hsize : (3*k+1)*Q*Q≤G.maxDegree :=
      (le_max_right Q _).trans ((le_max_right B _).trans hN)
    have hBDR : (B:ℝ)≤(G.maxDegree:ℝ):=by exact_mod_cast hBD
    have heps : 0<ε^2:=sq_pos_of_pos hε
    have hmul:=mul_le_mul_of_nonneg_left hBDR heps.le
    have hcut : (CaoChenUniformPaletteBudgets.cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ) := by
      have hh : (CaoChenUniformPaletteBudgets.cutoff k:ℝ)/ε^2≤(B:ℝ):=
        (le_max_left _ _).trans hB
      have hd:=(div_le_iff₀ heps).mp hh
      nlinarith only [hd,hmul]
    have hmass : 8*(E:ℝ)+8/ε≤ε^2*(G.maxDegree:ℝ) := by
      have hh : (8*(E:ℝ)+8/ε)/ε^2≤(B:ℝ):=(le_max_right _ _).trans hB
      have hd:=(div_le_iff₀ heps).mp hh
      nlinarith only [hd,hmul]
    exact R1_charge_of_palette_parameters hcrit ε hε hεone k hkNat hεk Q hQNat hεQ
      hcut hsize hQD hmass x hx

end OverfullWork.CaoChenDischarging
