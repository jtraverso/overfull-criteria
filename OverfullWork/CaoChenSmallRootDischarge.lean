module

public import OverfullWork.CaoChenSmallChargeAssembly
public import OverfullWork.CaoChenSmallPaletteBudget

@[expose] public section


/-! # The small-root R1 discharge, with all structural inputs proved

Choose an integer reciprocal K with epsilon*K >= 2. In every critical
graph, a vertex whose degree is at least 2*(K+2)^4 and at most epsilon*Delta/2
has R1 charge at least (1-epsilon)*Delta. The proof chooses the actual
minimum-palette colouring, constructs the finite multiplicity budget,
and applies Cauchy to the real donation formula.

This closes this small-root range without asserting the unresolved
double-maximum bad-colour exclusion. The medium-root discharge and the
global average-degree bound remain separate obligations.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- A genuine small-root instance of R1. No fan, recolouring, low-neighbour
budget, charge bound, or average-degree statement is assumed. -/
theorem small_root_R1_charge (hcrit : IsDeltaCritical G)
    (ε : ℝ) (hε : 0<ε) (K : ℕ) (hK : 1≤K) (hεK : 2≤ε*(K:ℝ))
    (x : V) (hlarge : 2*(K+2)^4≤G.degree x)
    (hxsmall : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q := (1-ε)*(G.maxDegree:ℝ)
  by_cases hx : (G.degree x:ℝ)<q
  · have hd : 2≤G.degree x := by
      have hk : 0<(K+2)^4 := by positivity
      omega
    have hq : 0<q := lt_of_le_of_lt (Nat.cast_nonneg _) hx
    have hroom : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ) := by
      dsimp [q]
      have hn : (0:ℝ)≤(G.degree x:ℝ) := Nat.cast_nonneg _
      nlinarith only [hxsmall,hn]
    obtain ⟨y,c,hcm,_hp,_hmin,hsigma⟩ :=
      CaoChenMinimalPalette.exists_minimal_paletteB_uniform_sigma hcrit x q (by omega) hroom
    let T := neighboursS c q x y
    let p := (paletteB c q x y).card
    have hpartition : T.card+p+1=G.degree x :=
      neighboursS_card_add_paletteB_add_one hcrit.2.1 hcm q
    apply charge_ge_of_small_root_counts ε hε K hK hεK x T p
      (neighboursS_subset_neighbourFinset c q x y)
      (neighboursS_card_pos hcrit.2.1 hcm q) hpartition hx hxsmall hlarge
    · intro u hu
      exact neighboursS_degree_add_paletteB_ge hcrit hcm q hq hroom u hu
    · intro u hu
      have hh : highCount G q u=
          ((G.neighborFinset u).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card :=
        by
          convert CaoChenPaletteCounting.highCount_eq_excluding_low_vertex
            (G:=G) (x:=x) q hx u using 1
          congr 1
          ext z
          simp only [Finset.mem_filter]
      have hs : G.maxDegree-G.degree x+1+p≤highCount G q u := by
        calc
          _ ≤ _ := (hsigma u ((mem_neighborFinset G x u).mp hu)).1
          _ = highCount G q u := by
            rw [hh]
      have hxD := G.degree_le_maxDegree x
      have hsum : G.maxDegree≤highCount G q u+T.card := by omega
      exact hsum
    · exact CaoChenSmallPaletteBudget.sum_lowCount_neighboursS_le hcrit hcm ε hε hq hx hxsmall hd K hεK
  · exact high_charge_ge_threshold G q x (le_of_not_gt hx)

/-- The integer reciprocal and the degree cutoff are chosen before the
graph. This is the proved small-root range, not eventual R1 on all degrees. -/
theorem eventual_small_root_R1 (ε : ℝ) (hε : 0<ε) :
    ∃D₀ : ℕ,2≤D₀ ∧
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        IsDeltaCritical G → ∀x,D₀≤G.degree x →
          (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2 →
          (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 (2/ε))
  have hKnat : 1≤K := by
    have hh : (1:ℝ)<(K:ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
    exact_mod_cast hh.le
  have hepsK : 2≤ε*(K:ℝ) := by
    have hh : 2/ε<(K:ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
    have hm := (div_lt_iff₀ hε).mp hh
    nlinarith only [hm]
  refine ⟨2*(K+2)^4,?_,?_⟩
  · have hk : 0<(K+2)^4 := by positivity
    omega
  · intro W _ _ G _ hcrit x hlarge hx
    exact small_root_R1_charge hcrit ε hε K hKnat hepsK x hlarge hx

end OverfullWork.CaoChenDischarging
