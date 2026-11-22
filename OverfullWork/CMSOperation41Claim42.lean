module

public import OverfullWork.CMSOperation41GlobalPacking
public import OverfullWork.CMSRegularizationDenseBase
public import OverfullWork.CMSOperation41StopExclusion

@[expose] public section


/-! Choose the integer margins used by Claim 4.2 from the robust
reserve and the size of the original exceptional set. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion DirectedSpanningConfiguration LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj SimpleGraph.fintypeEdgeSetSdiff

set_option maxHeartbeats 3000000 in
theorem cms_claim42_scalar_margins (n core exceptional D m : ℕ) (η ρ τ α : ℝ)
    (hSize : core+exceptional = n) (hMax : D ≤ n) (hDense : α*(n:ℝ) ≤ D)
    (hRounds : 3*m ≤ D) (hη : 0 ≤ η) (hSmall : η ≤ 1/64)
    (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hηα : 128*η ≤ α) (hτα : 512*τ ≤ α)
    (hRare : 8*η^2 ≤ ρ) (hLarge : 16 ≤ ρ^2*(n:ℝ)) (hτη : 4*η^2 ≤ τ)
    (hFew : (exceptional:ℝ) ≤ η^2*(n:ℝ)) (hShift : 64 ≤ η*(n:ℝ)) :
    let r := ⌈ρ*(core:ℝ)⌉₊
    let t := ⌈2*τ*(core:ℝ)⌉₊
    let a := ⌈η*(n:ℝ)⌉₊
    let b := ⌊2*(η*(n:ℝ))⌋₊-2*exceptional
    (b+2*exceptional ≤ ⌊2*(η*(n:ℝ))⌋₊) ∧
    D ≤ (r-exceptional)*(r-exceptional) ∧
    3*b+6*(t+2*exceptional+2) ≤ D-2*m ∧
    2*(a+exceptional)+2*(t+2*exceptional+2) ≤ D-2*m ∧
    ρ*(n:ℝ)/4 ≤ ((r-exceptional:ℕ):ℝ) ∧
    (1 ≤ τ*(n:ℝ) → ((t+exceptional:ℕ):ℝ) ≤ 4*τ*(n:ℝ)) := by
  intro r t a b
  let shift := η*(n:ℝ)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ shift := by linarith only [hShift]
  have hSize' : (core:ℝ)+exceptional = n := by exact_mod_cast hSize
  have hE0 : 0 ≤ (exceptional:ℝ) := Nat.cast_nonneg _
  have hCore : (core:ℝ) ≤ n := by linarith only [hSize',hE0]
  have hExceptional : (exceptional:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall hs
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hShiftLe : shift ≤ (n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith only [hSmall]) hn
    simpa only [shift,one_mul] using h
  have hHalf : (n:ℝ)/2 ≤ core := by
    linarith only [hSize',hExceptional,hShiftLe,hn]
  have hReserved : (r:ℝ) ≥ ρ*(core:ℝ) := Nat.le_ceil _
  have hRare' : 8*(exceptional:ℝ) ≤ ρ*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hRare hn
    nlinarith only [h,hFew]
  have hRhoLower : ρ*(n:ℝ)/2 ≤ (r:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hHalf hρ.le
    linarith only [h,hReserved]
  have hrE : exceptional ≤ r := by
    have hρn := mul_nonneg hρ.le hn
    exact_mod_cast (show (exceptional:ℝ) ≤ r by linarith only [hRare',hRhoLower,hρn])
  have hRadius : ρ*(n:ℝ)/4 ≤ ((r-exceptional:ℕ):ℝ) := by
    rw [Nat.cast_sub hrE]
    have hρn := mul_nonneg hρ.le hn
    linarith only [hRare',hRhoLower,hρn]
  have hRadius0 : 0 ≤ ρ*(n:ℝ)/4 := by positivity
  have hSurface : (n:ℝ) ≤ (ρ*(n:ℝ)/4)*(ρ*(n:ℝ)/4) := by
    have h := mul_le_mul_of_nonneg_right hLarge hn
    nlinarith only [h]
  have hSquare : n ≤ (r-exceptional)*(r-exceptional) := by
    have h := mul_le_mul hRadius hRadius hRadius0 (Nat.cast_nonneg _)
    exact_mod_cast hSurface.trans h
  have hEfloor : 2*exceptional ≤ ⌊2*(η*(n:ℝ))⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith only [hExceptional,hs]
  have hb : (b:ℝ) ≤ 2*shift := by
    have h : (b:ℝ) ≤ (⌊2*shift⌋₊:ℕ) := by exact_mod_cast Nat.sub_le _ _
    exact h.trans (Nat.floor_le (by positivity))
  have ha : (a:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one hs).le
  have ht : (t:ℝ) ≤ 2*τ*(n:ℝ)+1 := by
    have h := mul_le_mul_of_nonneg_left hCore (show 0 ≤ 2*τ by positivity)
    have hCeil : (t:ℝ) < 2*τ*(core:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h,hCeil]
  have hm : 2*m ≤ D := by omega
  have hRounds' : (3:ℝ)*m ≤ D := by exact_mod_cast hRounds
  have hD : α*(n:ℝ)/3 ≤ ((D-2*m:ℕ):ℝ) := by
    rw [Nat.cast_sub hm]
    push_cast
    linarith only [hDense,hRounds']
  have hbα : 128*shift ≤ α*(n:ℝ) := by
    simpa only [shift,mul_assoc] using mul_le_mul_of_nonneg_right hηα hn
  have htα : 512*τ*(n:ℝ) ≤ α*(n:ℝ) := mul_le_mul_of_nonneg_right hτα hn
  have hReserve0 : 0 ≤ α*(n:ℝ) := by linarith only [hbα,hs]
  have hReserve : 8*shift+12*τ*(n:ℝ) ≤ ((D-2*m:ℕ):ℝ) := by
    linarith only [hbα,htα,hD,hReserve0]
  refine ⟨?_,hMax.trans hSquare,?_,?_,hRadius,?_⟩
  · exact (Nat.sub_add_cancel hEfloor).le
  · exact_mod_cast (show 3*(b:ℝ)+6*((t:ℝ)+2*(exceptional:ℝ)+2) ≤ ((D-2*m:ℕ):ℝ) by
      apply le_trans _ hReserve
      linarith only [hb,ht,hExceptional,hShift])
  · exact_mod_cast (show 2*((a:ℝ)+exceptional)+2*((t:ℝ)+2*(exceptional:ℝ)+2) ≤ ((D-2*m:ℕ):ℝ) by
      have ht0 := mul_nonneg hτ hn
      apply le_trans _ hReserve
      linarith only [ha,ht,hExceptional,hShift,ht0])
  · intro hτn
    have h := mul_le_mul_of_nonneg_right hτη hn
    push_cast
    nlinarith only [ht,hFew,h,hτn]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The four properties of Claim 4.2, with integral radius and window. -/
def HasClaim42Properties (J : SimpleGraph V) [DecidableRel J.Adj] (d r t budget : ℕ) : Prop :=
  J.maxDegree = d ∧ ¬J.EdgeColorable J.maxDegree ∧ IsRobustAt J r t ∧ ¬J.HasOverfullSubgraph ∧
  ∀ u v,J.Adj u v → d ≤ J.degree u+J.degree v+budget

/-- The physical run and the final cleaned graph satisfy Claim 4.2.
The terminal record is read on that final graph. -/
def TrimmingPackingSegment.HasClaim42Realization
    {initial : Finset V} {D test cap m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap 0 m start finish)
    {atLimit : Prop} (last : TrimmingPackingTermination initial finish (D-2*m) test m cap atLimit)
    (ρ τ : ℝ) (budget terminalBudget : ℕ) : Prop :=
  let r := ⌈ρ*(initialᶜ.card:ℝ)⌉₊-initial.card
  let t := ⌈τ*(initialᶜ.card:ℝ)⌉₊+initial.card
  ∃ (R : SimpleGraph ↥(initialᶜ : Finset V)) (L : ℕ → SimpleGraph V),
    let physical (i : ℕ) := sdiff (H.states i).graph (usedTrimmingPrefix L i)
    let terminal := sdiff last.cleaned (usedTrimmingPrefix L m)
    IsRealRobust R ρ τ ∧
    (∀ i ≤ m,HasClaim42Properties (physical i) (D-2*i) r t budget) ∧
    HasClaim42Properties terminal (D-2*m) r t terminalBudget ∧
    (∀ i ≤ m,∀ v,(H.states i).record initial i v = (physical i).degree v) ∧
    (∀ v,auxiliaryPhysicalDegree last.cleaned initial finish.prescribed finish.credit m v = terminal.degree v) ∧
    (atLimit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < terminal.degree v))
      (D-2*m) test (fun v => terminal.degree v))

set_option maxHeartbeats 2500000 in
theorem TrimmingPackingSegment.realize_claim42
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial : Finset V} {test cap m : ℕ}
    {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    {atLimit : Prop}
    (last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap atLimit)
    (ρ τ : ℝ) (hρ : 0 ≤ ρ)
    (hPack : HasPackedCoreLayouts (G.induce (↑(initialᶜ : Finset V) : Set V)) H.layoutSize
      (fun i => (H.layoutWords i).endpoint) H.layoutOmitted ρ τ)
    (hRoom : 2*m ≤ G.maxDegree) (hNC : ¬G.EdgeColorable G.maxDegree)
    (hNo : ¬G.HasOverfullSubgraph) (hTest : 6*initial.card+6 ≤ test)
    (b a terminalBudget : ℕ) (hWeak : H.HasWeakDegreeSums b) (hBudget : b+2*initial.card ≤ terminalBudget)
    (hMargins : H.HasClaim42Margins ⌈ρ*(initialᶜ.card:ℝ)⌉₊ ⌈τ*(initialᶜ.card:ℝ)⌉₊ b a) :
    H.HasClaim42Realization last ρ τ b terminalBudget := by
  obtain ⟨R,L,_,hRob,hRobPrefix,hRobEnd,_,hRead,_,hEndDegree,hStop,hSum,hTrue⟩ :=
    H.realize_layouts hG last ρ τ hPack
  have hR := CanonicalRegularization.integer_robust_of_real R ρ τ hρ hRob
  rw [Fintype.card_coe] at hR
  obtain ⟨hClass,hEndClass,hAbsence⟩ := hTrue hRoom hNC
  obtain ⟨hNoPrefix,hNoEnd⟩ := hAbsence _ _ b a hR hNo hTest hMargins
  obtain ⟨hSumPrefix,hSumEnd⟩ := hSum b hWeak
  refine ⟨R,L,hRob,?_,?_,hRead,hEndDegree,hStop⟩
  · intro i hi
    exact ⟨(hClass i hi).1,(hClass i hi).2,hRobPrefix _ _ hR i hi,hNoPrefix i hi,hSumPrefix i hi⟩
  · refine ⟨hEndClass.2.2.1,hEndClass.2.2.2,hRobEnd _ _ hR,hNoEnd,?_⟩
    intro u v hEdge
    exact (hSumEnd u v hEdge).trans (Nat.add_le_add_left hBudget _)

/-- The ordinary floor survives the terminal cleanup. The extra loss
is charged to its subset of the original exceptional set. -/
theorem TrimmingPackingSegment.terminal_ordinary_floor
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial : Finset V} {test cap m a : ℕ}
    {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    {atLimit : Prop}
    (last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap atLimit)
    (hRoom : 2*m ≤ G.maxDegree)
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+a) :
    ∀ v,v ∉ initial → G.maxDegree-2*m ≤
      auxiliaryPhysicalDegree last.cleaned initial finish.prescribed finish.credit m v+
        (a+2*initial.card) := by
  let S (i : ℕ) := (H.states i).graph
  let T := H.cleanedGraph
  let P := prescribedTrimmingHistory initial T H.layoutSize H.layoutWords
  let credit := trimmingCreditHistory initial T H.layoutSize H.layoutWords H.layoutOmitted
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hRead,_,_⟩ := H.packing_inputs hG
  intro v hv
  have hBound : G.maxDegree-2*m ≤ auxiliaryPhysicalDegree (S m) initial P credit m v+a+initial.card :=
    (H.ordinary_credit_budget hG hRoom hOrd m le_rfl v hv).2.1
  have hS : S m = finish.graph := congrArg VirtualTrimmingState.graph H.finishes
  rw [hRead m le_rfl (S m),hS,H.finishes] at hBound
  let lost := (sdiff finish.graph last.cleaned).degree v
  have hBalance : last.cleaned.degree v+lost = finish.graph.degree v := by
    simpa only [lost,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,add_comm] using
      MaximumMatching.degree_sdiff_add_of_le finish.graph last.cleaned (DeletionRun.le_source last.cleanup) v
  have hLoss := independent_auxiliary_preprocessing_degree_loss last.cleanup last.cleanup_independent v
  have hCard := card_le_card last.cleanup_subset
  have hDegree := auxiliary_physical_degree_after_cleanup finish.graph last.cleaned initial finish.prescribed
    finish.credit m (DeletionRun.le_source last.cleanup) v
  change _ = _-lost at hDegree
  omega

set_option maxHeartbeats 4000000 in
/-- Operation 4.1 from the original graph through Claim 4.2 and
its physical stopping certificate. The size and scale bounds are
chosen before seeing the graph. -/
theorem cms_operation_4_1_claim_4_2 (α gap ν τ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hGap : 0 < gap) (hGapα : 6*gap ≤ α)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hHalfτ : τ ≤ 1/2) (hτGap : 32768*τ ≤ gap) :
    ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (η : ℝ) (hη : 0 ≤ η)
        (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
        (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph),
        let n := Fintype.card V
        let initial := initialExceptionalSet G η
        let shift := η*(n:ℝ)
        let cap := ⌊shift⌋₊
        let long := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
        let short := ⌊(G.maxDegree:ℝ)/3-2*shift⌋₊
        let test := 6*initial.card+6
        2*N ≤ n → 64 ≤ shift → 6 ≤ η^2*(n:ℝ) → (initial.card:ℝ) ≤ η^2*(n:ℝ) →
        128*η ≤ α → 6*η ≤ γ → 8*η^2 ≤ ν → 4*η^2 ≤ τ →
        8*η^2 ≤ ρ → 16 ≤ ρ^2*(n:ℝ) →
        α*(n:ℝ) ≤ (G.maxDegree:ℝ) → IsRealRobust G ν τ →
        ∃ m ≤ long,∃ start finish : VirtualTrimmingState V,
          start.graph = G ∧
          ∃ K : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish,
          ∃ last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
            (m = long ∨ short ≤ m),
          last.HasProfile ⌊6*shift⌋₊ ∧
          K.HasClaim42Realization last ρ (2*τ) (⌊2*shift⌋₊-2*initial.card) ⌊2*shift⌋₊ ∧
          (∀ v,v ∉ initial → G.maxDegree-2*m ≤
            auxiliaryPhysicalDegree last.cleaned initial finish.prescribed finish.credit m v+
              (⌈shift⌉₊+2*initial.card)) ∧
          α*(n:ℝ)/3 ≤ ((G.maxDegree-2*m:ℕ):ℝ) ∧
          ρ*(n:ℝ)/4 ≤ ((⌈ρ*(initialᶜ.card:ℝ)⌉₊-initial.card:ℕ):ℝ) ∧
          (1 ≤ τ*(n:ℝ) → ((⌈2*τ*(initialᶜ.card:ℝ)⌉₊+initial.card:ℕ):ℝ) ≤ 4*τ*(n:ℝ)) := by
  obtain ⟨γ,ρ,hγ,hρ,N,hChoose⟩ :=
    cms_operation_4_1_packed_layouts α gap ν τ hα hα₁ hGap hGapα hν hντ hHalfτ hτGap
  refine ⟨γ,ρ,hγ,hρ,N,?_⟩
  intro V _ _ G dG
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro η hη hVAL hNC hNo n initial shift cap long short test hn hShift hSize hFew
    hηα hγη hνη hτη hRare hLarge hDense hRob
  have hSmall : η ≤ 1/64 := by linarith only [hηα,hα₁]
  have hηα' : 24*η ≤ α := by linarith only [hη,hηα]
  have hτα : 512*τ ≤ α := by linarith only [hτGap,hGapα,hν,hντ]
  have ht : 1 ≤ test := by dsimp only [test]; omega
  obtain ⟨m,hm,start,finish,hG,hRoom,K,hWeak,last,hProfile,hPack⟩ :=
    hChoose G η hη hSmall hVAL test ht hn hShift hSize hFew hηα' hγη hνη hτη hDense hRob
  change m ≤ long at hm
  have hn0 : 0 < n := by
    by_contra! h
    have h0 : n = 0 := Nat.eq_zero_of_le_zero h
    simp only [shift,h0,Nat.cast_zero,mul_zero] at hShift
    norm_num at hShift
  letI : Nonempty V := Fintype.card_pos_iff.mp hn0
  have hMax : G.maxDegree ≤ n := G.maxDegree_lt_card_verts.le
  have hDenseShift : 24*shift ≤ (G.maxDegree:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hηα' (Nat.cast_nonneg (α := ℝ) n)
    simpa only [shift,mul_assoc] using h.trans hDense
  have hRound : 3*m ≤ G.maxDegree := by
    have hm' : (m:ℝ) ≤ long := by exact_mod_cast hm
    have hLong : (long:ℝ) ≤ (G.maxDegree:ℝ)/3-shift :=
      Nat.floor_le (by linarith only [hShift,hDenseShift])
    exact_mod_cast (show (3:ℝ)*m ≤ G.maxDegree by linarith only [hm',hLong,hShift])
  have hCard : initialᶜ.card+initial.card = n := by rw [Nat.add_comm]; exact card_add_card_compl initial
  obtain ⟨hBudget,hSquare,hB,hA,hRadius,hWindow⟩ :=
    cms_claim42_scalar_margins n initialᶜ.card initial.card G.maxDegree m η ρ τ α
      hCard hMax hDense hRound hη hSmall (hν.le.trans hντ) hρ hηα hτα hRare hLarge hτη hFew hShift
  let a := ⌈shift⌉₊
  let b := ⌊2*shift⌋₊-2*initial.card
  let r := ⌈ρ*(initialᶜ.card:ℝ)⌉₊
  let t := ⌈2*τ*(initialᶜ.card:ℝ)⌉₊
  have hOrd (v : V) (hv : v ∉ initial) : G.maxDegree ≤ G.degree v+a := by
    have hNear : (G.maxDegree:ℝ)-G.degree v ≤ shift := by
      by_contra! h
      exact hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hCeil : shift ≤ (a:ℝ) := Nat.le_ceil _
    exact_mod_cast (show (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+a by linarith only [hNear,hCeil])
  change TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish at K
  change K.HasWeakDegreeSums b at hWeak
  change TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
    (m = long ∨ short ≤ m) at last
  have hMargins := TrimmingPackingSegment.claim42_margins (G := G) K hG r t b a hRoom
    hWeak hOrd hSquare hB hA
  have hFloor : α*(n:ℝ)/3 ≤ ((G.maxDegree-2*m:ℕ):ℝ) := by
    have hmR : (3:ℝ)*m ≤ G.maxDegree := by exact_mod_cast hRound
    rw [Nat.cast_sub hRoom]
    push_cast
    linarith only [hmR,hDense]
  exact ⟨m,hm,start,finish,hG,K,last,hProfile,
    TrimmingPackingSegment.realize_claim42 (G := G) K hG last ρ (2*τ) hρ.le hPack hRoom
      hNC hNo le_rfl b (a+initial.card) _ hWeak hBudget hMargins,
    K.terminal_ordinary_floor hG last hRoom hOrd,hFloor,hRadius,hWindow⟩

set_option maxHeartbeats 3000000 in
/-- The sizes and degree deficits from the physical record satisfy
the input margins of the almost-overfull exclusion. -/
theorem cms_no_almost_stop_from_record_scales (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (U : Finset V),
          let n := Fintype.card V
          let shift := η*(n:ℝ)
          let d := J.maxDegree
          2*(N+4) ≤ n → 64 ≤ shift → 6 ≤ η^2*(n:ℝ) → (U.card:ℝ) ≤ η^2*(n:ℝ) →
          α*(n:ℝ) ≤ (d:ℝ) → ¬J.EdgeColorable d → ¬J.HasOverfullSubgraph →
          IsRealRobust J (8*ν) (σ/4) →
          (∀ u v,J.Adj u v → d ≤ J.degree u+J.degree v+⌊2*shift⌋₊) →
          (∀ v,v ∉ U → d ≤ J.degree v+⌈shift⌉₊+2*U.card) →
          ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < J.degree v)) d (6*U.card+6)
            (fun v => J.degree v) := by
  obtain ⟨σ,hσ,hUse⟩ := cms_no_almost_overfull_record_after_trimming α hα hα₁
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν hνσ
  let ηMax := min (η₀/16) (min (α/64) (1/64))
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  have hParam : 16*η ≤ η₀ := by
    have h := hηMax.trans (min_le_left _ _)
    linarith only [h]
  have hSmall : η ≤ 1/64 := (hηMax.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hηα : 64*η ≤ α := by
    have h := (hηMax.trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith only [h]
  obtain ⟨N,hUse⟩ := hUse (16*η) (by positivity) hParam
  refine ⟨N,?_⟩
  intro V _ _ J _ U n shift d hn hShift hSize hFew hD hNC hNo hRob hWeak hOrd
  let K := U.card+1
  let a := ⌈shift⌉₊+2*U.card
  let b := 6*U.card+6
  let A := ⌊2*shift⌋₊
  let active := univ.filter (fun v : V => 0 < J.degree v)
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ shift := by linarith only [hShift]
  have hFew' : (U.card:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall hs
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hShiftLe : shift ≤ (n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith only [hSmall]) hn0
    simpa only [shift,one_mul] using h
  have hHalf : 2*(K+1) ≤ n := by
    dsimp only [K]
    exact_mod_cast (show (2:ℝ)*((U.card:ℝ)+1+1) ≤ n by
      linarith only [hFew',hShift,hShiftLe])
  have hKN : K+1 ≤ n := by omega
  have hCompare : (n:ℝ)/2 ≤ ((n-K-1:ℕ):ℝ) := by
    rw [Nat.sub_sub,Nat.cast_sub hKN]
    have h : (2:ℝ)*((K:ℝ)+1) ≤ n := by exact_mod_cast hHalf
    push_cast
    linarith only [h]
  have hEnough : N+3+K ≤ n := by omega
  have hB : ((b+2*(A+K)+4:ℕ):ℝ) ≤ (16*η)*((n-K-1:ℕ):ℝ) := by
    have hA : (A:ℝ) ≤ 2*shift := Nat.floor_le (by positivity)
    have hLower := mul_le_mul_of_nonneg_left hCompare (show 0 ≤ 16*η by positivity)
    dsimp only [b,K]
    push_cast
    dsimp only [shift] at hA hFew'
    linarith only [hA,hFew',hShift,hLower]
  have hK : ((K+1:ℕ):ℝ) ≤ 2*(16*η)^2*((n-K-1:ℕ):ℝ) := by
    have hCoef : 0 ≤ 2*(16*η)^2 := by positivity
    have hFloor := mul_le_mul_of_nonneg_left hCompare hCoef
    have hηn := mul_nonneg (sq_nonneg η) hn0
    dsimp only [K]
    push_cast
    nlinarith only [hFloor,hFew,hSize,hηn]
  have hRoom : 2*a+b+1 ≤ d := by
    have hCeil : (⌈shift⌉₊:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one hs).le
    have hLarge : 64*shift ≤ (d:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hηα hn0
      simpa only [shift,mul_assoc] using h.trans hD
    dsimp only [a,b]
    exact_mod_cast (show (2:ℝ)*((⌈shift⌉₊:ℕ)+2*(U.card:ℝ))+
        (6*(U.card:ℝ)+6)+1 ≤ (d:ℝ) by linarith only [hCeil,hFew',hShift,hLarge])
  exact hUse J active U (fun v => J.degree v) a b A hEnough hD hNC hNo hRob hWeak hB hK
    (fun v hv => mem_filter.mpr ⟨mem_univ _,hv⟩) (fun _ _ => rfl)
    (fun v hv => by simpa only [a,Nat.add_assoc] using hOrd v hv) hRoom

set_option maxHeartbeats 5500000 in
/-- Uniformly choose the scales before the input graph and rule out
an almost-overfull stopping record. The realized run reaches one of
the round limits. -/
theorem cms_operation_4_1_round_limit (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τMax : ℝ,0 < τMax ∧ ∀ τ : ℝ,0 < τ → τ ≤ τMax →
      ∀ ν : ℝ,0 < ν → ν ≤ τ →
        ∃ ρ ηMax : ℝ,0 < ρ ∧ 0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
          ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
            let n := Fintype.card V
            let initial := initialExceptionalSet G η
            let shift := η*(n:ℝ)
            let cap := ⌊shift⌋₊
            let long := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
            let short := ⌊(G.maxDegree:ℝ)/3-2*shift⌋₊
            let test := 6*initial.card+6
            N ≤ n → α*(n:ℝ) ≤ (G.maxDegree:ℝ) → (initial.card:ℝ) ≤ η^2*(n:ℝ) →
            IsRealRobust G ν τ →
            (∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
            ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
            ∃ m ≤ long,∃ start finish : VirtualTrimmingState V,
              start.graph = G ∧
              ∃ K : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish,
              ∃ last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
                (m = long ∨ short ≤ m),
              (m = long ∨ short ≤ m) ∧
              K.HasClaim42Realization last ρ (2*τ) (⌊2*shift⌋₊-2*initial.card) ⌊2*shift⌋₊ ∧
              ∃ L : ℕ → SimpleGraph V,
                let J := sdiff last.cleaned (usedTrimmingPrefix L m)
                HasClaim42Properties J (G.maxDegree-2*m)
                  (⌈ρ*(initialᶜ.card:ℝ)⌉₊-initial.card)
                  (⌈2*τ*(initialᶜ.card:ℝ)⌉₊+initial.card) ⌊2*shift⌋₊ ∧
                IsRealRobust J (ρ/4) (4*τ) ∧
                (∀ v,auxiliaryPhysicalDegree last.cleaned initial finish.prescribed finish.credit m v =
                  J.degree v) ∧
                (∀ v,v ∉ initial → J.maxDegree ≤ J.degree v+⌈shift⌉₊+2*initial.card) ∧
                ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < J.degree v))
                  J.maxDegree test (fun v => J.degree v) ∧
                α*(n:ℝ)/3 ≤ (J.maxDegree:ℝ) ∧
                HasDenseRoundLimitRecord (fun v => J.degree v) J.maxDegree ⌊6*shift⌋₊ := by
  obtain ⟨σ,hσ,hExclude⟩ := cms_no_almost_stop_from_record_scales (α/3) (by positivity) (by linarith)
  let gap := α/12
  let τMax := min (gap/32768) (σ/16)
  refine ⟨τMax,by dsimp only [τMax,gap]; positivity,?_⟩
  intro τ hτ hτMax ν hν hντ
  have hτGap : 32768*τ ≤ gap := by
    have h := hτMax.trans (min_le_left _ _)
    linarith only [h]
  have hτHalf : τ ≤ 1/2 := by dsimp only [gap] at hτGap; linarith only [hτGap,hα₁]
  have hτσ : 4*τ ≤ σ/4 := by
    have h := hτMax.trans (min_le_right _ _)
    linarith only [h]
  obtain ⟨γ,ρ,hγ,hρ,Npack,hPack⟩ :=
    cms_operation_4_1_claim_4_2 α gap ν τ hα hα₁ (by dsimp only [gap]; positivity)
      (by dsimp only [gap]; linarith only [hα]) hν hντ hτHalf hτGap
  let ν₀ := min (ρ/32) σ
  have hν₀ : 0 < ν₀ := by dsimp only [ν₀]; positivity
  have hν₀σ : ν₀ ≤ σ := min_le_right _ _
  have hν₀ρ : 8*ν₀ ≤ ρ/4 := by
    have h : ν₀ ≤ ρ/32 := min_le_left _ _
    linarith only [h]
  obtain ⟨η₀,hη₀,hExclude⟩ := hExclude ν₀ hν₀ hν₀σ
  let ηMax := min η₀ (min (α/128) (min (γ/6) (min (ν/8) (min (τ/4) (ρ/8)))))
  refine ⟨ρ,ηMax,hρ,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  have hη₀' : η ≤ η₀ := hηMax.trans (min_le_left _ _)
  have hMore := hηMax.trans (min_le_right _ _)
  have hηα : 128*η ≤ α := by
    have h := hMore.trans (min_le_left _ _)
    linarith only [h]
  have hMore := hMore.trans (min_le_right _ _)
  have hηγ : 6*η ≤ γ := by
    have h := hMore.trans (min_le_left _ _)
    linarith only [h]
  have hη1 : η ≤ 1 := by linarith only [hηα,hα₁]
  have hη2 : η^2 ≤ η := by nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
  have hMore := hMore.trans (min_le_right _ _)
  have hην : 8*η^2 ≤ ν := by
    have h := (hη2.trans hMore).trans (min_le_left _ _)
    linarith only [h]
  have hMore := hMore.trans (min_le_right _ _)
  have hητ : 4*η^2 ≤ τ := by
    have h := (hη2.trans hMore).trans (min_le_left _ _)
    linarith only [h]
  have hηρ : 8*η^2 ≤ ρ := by
    have h := (hη2.trans hMore).trans (min_le_right _ _)
    linarith only [h]
  obtain ⟨Nnear,hExclude⟩ := hExclude η hη hη₀'
  let N := max (2*Npack) (max (2*(Nnear+4))
    (max ⌈64/η⌉₊ (max ⌈6/η^2⌉₊ (max ⌈16/ρ^2⌉₊ ⌈1/τ⌉₊))))
  refine ⟨N,?_⟩
  intro V _ _ G dG
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro n initial shift cap long short test hn hDense hFew hRob hVAL hNC hNo
  have hPackSize : 2*Npack ≤ n := (le_max_left _ _).trans hn
  have hNearSize : 2*(Nnear+4) ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hNum : max ⌈64/η⌉₊ (max ⌈6/η^2⌉₊ (max ⌈16/ρ^2⌉₊ ⌈1/τ⌉₊)) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have scale (c q : ℝ) (hq : 0 < q) (h : ⌈c/q⌉₊ ≤ n) : c ≤ q*(n:ℝ) := by
    have hCast : (⌈c/q⌉₊:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    have hc := (Nat.le_ceil (c/q)).trans hCast
    simpa only [mul_comm q] using (div_le_iff₀ hq).mp hc
  have hShift : 64 ≤ shift := scale 64 η hη ((le_max_left _ _).trans hNum)
  have hNum' := (le_max_right _ _).trans hNum
  have hSize : 6 ≤ η^2*(n:ℝ) := scale 6 (η^2) (by positivity) ((le_max_left _ _).trans hNum')
  have hNum'' := (le_max_right _ _).trans hNum'
  have hLarge : 16 ≤ ρ^2*(n:ℝ) := scale 16 (ρ^2) (by positivity) ((le_max_left _ _).trans hNum'')
  have hτn : 1 ≤ τ*(n:ℝ) := scale 1 τ hτ ((le_max_right _ _).trans hNum'')
  obtain ⟨m,hm,start,finish,hG,K,last,hProfile,hRealize,hOrd,hD,hRadius,hWindow⟩ :=
    hPack G η hη.le hVAL hNC hNo hPackSize hShift hSize hFew hηα hηγ hην hητ hηρ hLarge hDense hRob
  have hSave := hRealize
  obtain ⟨R,L,_,_,hEnd,_,hDegree,_⟩ := hRealize
  let J := sdiff last.cleaned (usedTrimmingPrefix L m)
  have hProps := hEnd
  obtain ⟨hJ,hJNC,hJRob,hJNo,hWeak⟩ := hEnd
  have hCoreReal : IsRealRobust J (ρ/4) (4*τ) :=
    isRealRobust_of_integer J _ _ _ _ hJRob
      (by simpa only [div_mul_eq_mul_div] using hRadius) (hWindow hτn)
  have hJReal : IsRealRobust J (8*ν₀) (σ/4) := by
    apply isRealRobust_of_integer J _ _ _ _ hJRob
    · exact (mul_le_mul_of_nonneg_right hν₀ρ (Nat.cast_nonneg _)).trans (by
        simpa only [div_mul_eq_mul_div] using hRadius)
    · exact (hWindow hτn).trans (mul_le_mul_of_nonneg_right hτσ (Nat.cast_nonneg _))
  have hJOrd (v : V) (hv : v ∉ initial) : J.maxDegree ≤ J.degree v+⌈shift⌉₊+2*initial.card := by
    rw [hJ,←hDegree v,Nat.add_assoc]
    exact hOrd v hv
  have hFail := hExclude J initial hNearSize hShift hSize hFew
    (by rw [hJ]; simpa only [div_mul_eq_mul_div] using hD)
    hJNC hJNo hJReal (fun u v he => by rw [hJ]; exact hWeak u v he) hJOrd
  unfold TrimmingPackingTermination.HasProfile at hProfile
  rw [funext hDegree] at hProfile
  let profile (d : ℕ) := HasRoundLimitProfile (fun v => J.degree v) d test ⌊6*shift⌋₊
    (m = long ∨ short ≤ m)
  have hPhysical : profile J.maxDegree := (congrArg profile hJ).mpr hProfile
  obtain ⟨hLimit,hDenseRecord⟩ := hPhysical.resolve_right hFail
  have hLinear : α*(n:ℝ)/3 ≤ (J.maxDegree:ℝ) := (congrArg (fun d : ℕ =>
    α*(n:ℝ)/3 ≤ (d:ℝ)) hJ).mpr hD
  exact ⟨m,hm,start,finish,hG,K,last,hLimit,hSave,L,hProps,hCoreReal,hDegree,hJOrd,hFail,
    hLinear,hDenseRecord⟩

end OverfullWork.CMSTrimmingRound
