module

public import OverfullWork.PrefactorOpenOrbit
public import OverfullWork.RealPrefactorReachability

@[expose] public section


/-! Lo–Patel Theorem 5.3. Short-cycle elimination using the first and
last k vertices of the open path and a finite minimization. -/
namespace OverfullWork.DirectedPrefactor
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 20000000

theorem exists_factor_with_long_cycles (D : Digraph V) (ν τ ξ : ℝ) (k : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hSmall : ξ ≤ ν^2/8) (hOrder : 128 ≤ ν^3*(Fintype.card V:ℝ))
    (hSize : 2*(k:ℝ) ≤ ξ*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,τ*(Fintype.card V:ℝ)+1 ≤ (inDegree D v:ℝ))
    (hClose : ∀ v,τ*(Fintype.card V:ℝ)+(k:ℝ) < (inDegree D v:ℝ))
    (hOut : ∀ v,(τ+ξ)*(Fintype.card V:ℝ)+2 ≤ (outDegree D v:ℝ)) :
    ∃ σ : Equiv.Perm V,(∀ v,D.Adj v (σ v)) ∧ ∀ v,k ≤ (orbit σ v).card := by
  have hn : (0:ℝ) < Fintype.card V :=
    pos_of_mul_pos_right (by linarith only [hOrder] : 0 < ν^3*(Fintype.card V:ℝ))
      (pow_nonneg hν.le _)
  obtain ⟨σ₀,hσ₀⟩ := exists_real_cycle_factor D ν τ hRobust (mul_pos hν hn) hτ hIn
    (fun v => by
      have hh := hOut v
      nlinarith only [hh,mul_nonneg hξ hn.le])
  have hStep : ∀ s ≤ k,∃ σ : Equiv.Perm V,(∀ v,D.Adj v (σ v)) ∧
      ∀ v,s ≤ (orbit σ v).card := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨σ₀,hσ₀,fun _ => Nat.zero_le _⟩
    | succ s ih =>
      intro hs
      obtain ⟨σ,hσ,hsσ⟩ := ih (by omega)
      let bad := fun π : Equiv.Perm V => univ.filter (fun v => (orbit π v).card ≤ s)
      let P := fun j : ℕ => ∃ π : Equiv.Perm V,
        (∀ v,D.Adj v (π v)) ∧ (∀ v,s ≤ (orbit π v).card) ∧ (bad π).card=j
      have hEx : ∃ j,P j := ⟨(bad σ).card,σ,hσ,hsσ,rfl⟩
      obtain ⟨π,hπ,hmin,hcard⟩ := Nat.find_spec hEx
      refine ⟨π,hπ,fun x => ?_⟩
      by_contra! hx
      have hxSize : (orbit π x).card=s := by have hh := hmin x; omega
      let F₀ := ofFactor (D:=D) π hπ x
      have hB : ∀ F : Prefactor D x,((forbiddenEnds k F).card:ℝ) ≤ ξ*(Fintype.card V:ℝ) := by
        intro F
        exact (by exact_mod_cast card_forbiddenEnds_le k F :
          ((forbiddenEnds k F).card:ℝ) ≤ 2*(k:ℝ)).trans hSize
      have hReach := real_most_termini_reachable (forbiddenEnds k) F₀ ν τ ξ
        hν hν₁ hτ hξ hSmall hOrder hB hRobust (hOut _)
      have hOriginIn : τ*(Fintype.card V:ℝ)+((orbit π x).card:ℝ) < (inDegree D x:ℝ) := by
        have hh : ((orbit π x).card:ℝ) ≤ k := by
          exact_mod_cast (show (orbit π x).card ≤ k by omega)
        linarith only [hh,hClose x]
      obtain ⟨F,hF,hEnd,hAdj⟩ := exists_reachable_closed_factor
        (forbiddenEnds k) F₀ _ _ (orbit π x) hReach hOriginIn
      have hGrow : s < (orbit F.successor x).card := hxSize ▸
        open_orbit_grows hF (show (orbit π x).card ≤ k by omega) hEnd
      have hInherited : ∀ v,(orbit F.successor v).card ≤ s →
          orbit F.successor v=orbit π v := by
        intro v hv
        have hNot : x ∉ orbit F.successor v := by
          intro h
          have hc := (orbit_mem_iff _ _ _).mp h
          have he : orbit F.successor v=orbit F.successor x := by
            ext w
            rw [orbit_mem_iff,orbit_mem_iff]
            exact ⟨fun hw => hc.symm.trans hw,fun hw => hc.trans hw⟩
          rw [he] at hv
          omega
        exact short_cycle_inherited hF v hNot (by omega)
      have hNewMin : ∀ v,s ≤ (orbit F.successor v).card := by
        intro v
        by_cases hh : (orbit F.successor v).card ≤ s
        · rw [hInherited v hh];exact hmin v
        · omega
      have hSub : bad F.successor ⊆ bad π := by
        intro v hv
        have hc := (mem_filter.mp hv).2
        exact mem_filter.mpr ⟨mem_univ _,by rw [←hInherited v hc];exact hc⟩
      have hStrict : bad F.successor ⊂ bad π := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hSub,fun he => ?_⟩
        have hxOld : x∈bad π := mem_filter.mpr ⟨mem_univ _,hxSize.le⟩
        have hxNew : x ∈ bad F.successor := he.symm ▸ hxOld
        have hxCard : (orbit F.successor x).card ≤ s := (mem_filter.mp hxNew).2
        exact (not_le_of_gt hGrow) hxCard
      have hLess := card_lt_card hStrict
      rw [hcard] at hLess
      exact (Nat.find_min hEx hLess) ⟨F.successor,hAdj,hNewMin,rfl⟩
  exact hStep k le_rfl

/-- The distinct orbits of the resulting successor permutation cover
the vertex set and their count is at most floor(n/k) when k>0. -/
theorem orbit_count_mul_le (σ : Equiv.Perm V) (k : ℕ)
    (hk : ∀ v,k ≤ (orbit σ v).card) :
    ((univ : Finset V).image (orbit σ)).card*k ≤ Fintype.card V := by
  let C := (univ : Finset V).image (orbit σ)
  have hDis : (↑C : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hNe
    obtain ⟨u,_,rfl⟩ := mem_image.mp (show A∈C from hA)
    obtain ⟨v,_,rfl⟩ := mem_image.mp (show B∈C from hB)
    apply disjoint_left.mpr
    intro w hu hv
    have he := ((orbit_mem_iff _ _ _).mp hu).trans ((orbit_mem_iff _ _ _).mp hv).symm
    apply hNe
    ext a
    rw [orbit_mem_iff,orbit_mem_iff]
    exact ⟨fun ha => he.symm.trans ha,fun ha => he.trans ha⟩
  have hCard := card_biUnion (s:=C) hDis
  calc
    C.card*k = ∑ _A∈C,k := by simp
    _ ≤ ∑ A∈C,A.card := by
      apply sum_le_sum
      intro A hA
      obtain ⟨v,_,rfl⟩ := mem_image.mp hA
      exact hk v
    _ = (C.biUnion id).card := hCard.symm
    _ ≤ Fintype.card V := card_le_univ _

/-- A spanning directed 1-factor with at most 4/ξ cycles, paying
the rounding in k = floor(ξ n / 2). -/
theorem exists_factor_with_few_cycles (D : Digraph V) (ν τ ξ : ℝ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hξ : 0 < ξ)
    (hSmall : ξ ≤ ν^2/8) (hOrder : 128 ≤ ν^3*(Fintype.card V:ℝ))
    (hRound : 4 ≤ ξ*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,(τ+ξ)*(Fintype.card V:ℝ)+1 ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,(τ+ξ)*(Fintype.card V:ℝ)+2 ≤ (outDegree D v:ℝ)) :
    ∃ σ : Equiv.Perm V,(∀ v,D.Adj v (σ v)) ∧
      (((univ : Finset V).image (orbit σ)).card:ℝ) ≤ 4/ξ := by
  let n := Fintype.card V
  let k := ⌊ξ*(n:ℝ)/2⌋₊
  have hKUpper : (k:ℝ) ≤ ξ*(n:ℝ)/2 := Nat.floor_le (by positivity)
  have hKLower : ξ*(n:ℝ)/4 ≤ (k:ℝ) := by
    have hh : ξ*(n:ℝ)/2 < (k:ℝ)+1 := Nat.lt_floor_add_one _
    linarith only [hh,hRound]
  have hN : (0:ℝ) < n :=
    pos_of_mul_pos_right (by linarith only [hRound] : 0 < ξ*(n:ℝ)) hξ.le
  have hPos : 0 ≤ ξ*(n:ℝ) := mul_nonneg hξ.le hN.le
  obtain ⟨σ,hσ,hK⟩ := exists_factor_with_long_cycles D ν τ ξ k hν hν₁ hτ hξ.le
    hSmall hOrder (by linarith only [hKUpper]) hRobust
    (fun v => by have hh := hIn v; nlinarith only [hh,hPos])
    (fun v => by have hh := hIn v; nlinarith only [hh,hPos,hKUpper]) hOut
  refine ⟨σ,hσ,(le_div_iff₀ hξ).mpr ?_⟩
  let c := ((univ : Finset V).image (orbit σ)).card
  have hprod : (c:ℝ)*(k:ℝ) ≤ n := by exact_mod_cast orbit_count_mul_le σ k hK
  have hScale := mul_le_mul_of_nonneg_left hKLower (Nat.cast_nonneg c : (0:ℝ) ≤ c)
  change (c:ℝ)*ξ ≤ 4
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith only [hprod,hScale]

end OverfullWork.DirectedPrefactor
