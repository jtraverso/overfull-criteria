module

public import OverfullWork.OddTwoEdgeExtension
public import OverfullWork.CMSOperation42RobustOddCuts

@[expose] public section


/-! The two-edge parity extension in CMS Case 1.1 uses its existing
no-overfull theorem. Robustness and the ordinary degree profile
supply the connectedness input. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OddCutDeficit CMSMatchingRemoval
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem connected_of_robust_with_one_exception (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (r t : ℕ) (hr : 0 < r) (hRob : IsRobustAt G r t)
    (z : V) (hPos : ∀ v,0 < G.degree v) (hOrd : ∀ v,v ≠ z → t ≤ G.degree v) :
    G.Connected := by
  refine { preconnected := ?_ }
  intro u v
  by_contra hUnreachable
  let S : Finset V := univ.filter (G.Reachable u)
  have hu : u ∈ S := mem_filter.mpr ⟨mem_univ _,SimpleGraph.Reachable.refl u⟩
  have hv : v ∈ Sᶜ := mem_compl.mpr (fun hv => hUnreachable (mem_filter.mp hv).2)
  have hClosed (x : V) (hx : x ∈ S) (y : V) (hxy : G.Adj x y) : y ∈ S :=
    mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.trans hxy.reachable⟩
  have hClosed' (x : V) (hx : x ∈ Sᶜ) (y : V) (hxy : G.Adj x y) : y ∈ Sᶜ :=
    mem_compl.mpr (fun hy => (mem_compl.mp hx) (hClosed y hy x hxy.symm))
  have hSide (T : Finset V) (hT : T.Nonempty)
      (hClose : ∀ x ∈ T,∀ y,G.Adj x y → y ∈ T) : t ≤ T.card := by
    obtain ⟨x,hx⟩ := hT
    have hex : ∃ w ∈ T,w ≠ z := by
      by_cases h : x = z
      · obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj x).mp (hPos x)
        exact ⟨w,hClose x hx w hw,fun he => hw.ne (h.trans he.symm)⟩
      · exact ⟨x,hx,h⟩
    obtain ⟨w,hw,hwz⟩ := hex
    have hNbr : G.neighborFinset w ⊆ T := fun y hy =>
      hClose w hw y ((mem_neighborFinset _ _ _).mp hy)
    exact (hOrd w hwz).trans (by simpa only [card_neighborFinset_eq_degree] using card_le_card hNbr)
  have hLo := hSide S ⟨u,hu⟩ hClosed
  have hUpper := hSide Sᶜ ⟨v,hv⟩ hClosed'
  have hSplit := card_add_card_compl S
  have hh := robust_cut_lower_simple G S r t hRob hLo (by omega)
  have hZero : cutEdges G S = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro p hp
    obtain ⟨hIn,hAdj⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hIn
    exact (mem_compl.mp hy) (hClosed p.1 hx p.2 hAdj)
  have hPosR := Nat.mul_pos hr hr
  omega

theorem odd_two_edge_extension_no_overfull_of_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b z : V) (hab : a ≠ b) (hOrder : Odd (Fintype.card V))
    (hD : 2 ≤ G.maxDegree) (ha : G.degree a < G.maxDegree) (hb : G.degree b < G.maxDegree)
    (hNo : ¬G.HasOverfullSubgraph) (r t : ℕ) (hr : 0 < r) (hRob : IsRobustAt G r t)
    (hPos : ∀ v,0 < G.degree v) (hOrd : ∀ v,v ≠ z → t ≤ G.degree v) :
    ¬(OddTwoEdgeExtension.extension G a b).HasOverfullSubgraph := by
  haveI : Nonempty V := ⟨a⟩
  exact OddTwoEdgeExtension.no_overfull G (connected_of_robust_with_one_exception G r t hr hRob z hPos hOrd)
    hOrder a b hab hD ha hb hNo

theorem robust_after_one_added_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (hOld : ∀ u v,G.Adj u v → H.Adj (some u) (some v))
    (r t : ℕ) (hr : 0 < r) (hRob : IsRobustAt G r t) :
    IsRobustAt H (r-1) (t+1) := by
  intro S hLo hHi
  let T := S.eraseNone
  have hSize : T.card ≤ S.card ∧ S.card ≤ T.card+1 := by
    by_cases h : none ∈ S
    · have hh := card_eraseNone_of_mem h
      change T.card = S.card-1 at hh
      omega
    · have hh := card_eraseNone_of_not_mem h
      change T.card = S.card at hh
      exact ⟨hh.le,by omega⟩
  have hTLo : t ≤ T.card := by omega
  have hTHi : T.card+t ≤ Fintype.card V := by
    rw [Fintype.card_option] at hHi
    omega
  have hGrowth := hRob T hTLo hTHi
  let R := neighbourhood G r T
  have hSurvive : R.image some ⊆ neighbourhood H (r-1) S := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    have hNbs : PrunedCore.neighboursIn G T u ≤ PrunedCore.neighboursIn H S (some u) := by
      rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,
        ←card_image_of_injective (T.filter (G.Adj u)) (Option.some_injective V)]
      apply card_le_card
      intro w hw
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
      obtain ⟨hxT,hAdj⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_eraseNone.mp hxT,hOld u x hAdj⟩
    exact mem_filter.mpr ⟨mem_univ _,(Nat.sub_le _ _).trans ((mem_filter.mp hu).2.trans hNbs)⟩
  have hh := card_le_card hSurvive
  rw [card_image_of_injective _ (Option.some_injective V)] at hh
  change T.card+r ≤ R.card at hGrowth
  omega

theorem odd_two_edge_extension_robust_and_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b z : V) (hab : a ≠ b) (hOrder : Odd (Fintype.card V))
    (hD : 2 ≤ G.maxDegree) (ha : G.degree a < G.maxDegree) (hb : G.degree b < G.maxDegree)
    (hNo : ¬G.HasOverfullSubgraph) (r t : ℕ) (hr : 0 < r) (hRob : IsRobustAt G r t)
    (hPos : ∀ v,0 < G.degree v) (hOrd : ∀ v,v ≠ z → t ≤ G.degree v) :
    IsRobustAt (OddTwoEdgeExtension.extension G a b) (r-1) (t+1) ∧
      ¬(OddTwoEdgeExtension.extension G a b).HasOverfullSubgraph := by
  refine ⟨robust_after_one_added_vertex G (OddTwoEdgeExtension.extension G a b) (fun _ _ h => h)
    r t hr hRob,odd_two_edge_extension_no_overfull_of_robust G a b z hab hOrder hD ha hb
      hNo r t hr hRob hPos hOrd⟩


theorem exists_two_deficient_attachments (G : SimpleGraph V) [DecidableRel G.Adj]
    (hThree : 3 ≤ (univ.filter fun v => G.degree v < G.maxDegree).card) :
    ∃ a b c : V,a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
      G.degree a < G.maxDegree ∧ G.degree b < G.maxDegree ∧
      G.degree c ≤ G.degree a ∧ G.degree c ≤ G.degree b := by
  let F : Finset V := univ.filter fun v => G.degree v < G.maxDegree
  have hF : 3 ≤ F.card := hThree
  obtain ⟨a,ha,hMaxA⟩ := F.exists_max_image (fun v => G.degree v) (card_pos.mp (by omega))
  have hFA : 2 ≤ (F.erase a).card := by rw [card_erase_of_mem ha]; omega
  obtain ⟨b,hb,hMaxB⟩ := (F.erase a).exists_max_image (fun v => G.degree v) (card_pos.mp (by omega))
  have hFB : 1 ≤ ((F.erase a).erase b).card := by rw [card_erase_of_mem hb]; omega
  obtain ⟨c,hc⟩ := card_pos.mp (by omega : 0 < ((F.erase a).erase b).card)
  exact ⟨a,b,c,(mem_erase.mp hb).1.symm,(mem_erase.mp (mem_erase.mp hc).2).1,(mem_erase.mp hc).1,
    (mem_filter.mp ha).2,(mem_filter.mp (mem_erase.mp hb).2).2,
    hMaxA c (mem_erase.mp (mem_erase.mp hc).2).2,hMaxB c (mem_erase.mp hc).2⟩

set_option maxHeartbeats 1800000 in
theorem two_edge_extension_smallest_pair_has_two_other_neighbours
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b c z : V)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hLow : ∀ v,2 ≤ G.degree v) (hOrd : ∀ v,v ≠ z → 3 ≤ G.degree v)
    (hcA : G.degree c ≤ G.degree a) (hcB : G.degree c ≤ G.degree b) :
    let H := OddTwoEdgeExtension.extension G a b
    ∀ p q : Option V,p ≠ q → (∀ v,H.degree p ≤ H.degree v) →
      (∀ v,v ≠ p → H.degree q ≤ H.degree v) →
      2 ≤ ((H.neighborFinset p).erase q).card := by
  intro H p q hpq hFirst hSecond
  have hNew : H.degree none = 2 := OddTwoEdgeExtension.degree_new G a b hab
  have hOld (v : V) : H.degree (some v) = G.degree v+(if v = a ∨ v = b then 1 else 0) := by
    simpa only [Nat.add_comm] using OddTwoEdgeExtension.degree_old G a b v
  have hMin (v : Option V) : 2 ≤ H.degree v := by
    cases v with
    | none => rw [hNew]
    | some v =>
      have h := hLow v
      rw [hOld]
      omega
  have hp : H.degree p = 2 := by have hlo := hMin p; have hhi := hFirst none; omega
  have hNoN : q ∉ H.neighborFinset p := by
    intro hAdj
    have hEdge := (mem_neighborFinset H p q).mp hAdj
    cases p with
    | none =>
      cases q with
      | none => exact hpq rfl
      | some q =>
        have hC := hSecond (some c) (by simp)
        have hc := hOld c
        simp only [hca,hcb,or_false,if_false,Nat.add_zero] at hc
        change q = a ∨ q = b at hEdge
        rcases hEdge with hqa|hqb
        · rw [hqa] at hC
          have h := hOld a
          simp at h
          omega
        · rw [hqb] at hC
          have h := hOld b
          simp at h
          omega
    | some p =>
      have hp' := hOld p
      have hpa : p ≠ a := by intro he; subst p; simp at hp'; have hh := hLow a; omega
      have hpb : p ≠ b := by intro he; subst p; simp at hp'; have hh := hLow b; omega
      cases q with
      | none => exact (show ¬(p=a ∨ p=b) from not_or.mpr ⟨hpa,hpb⟩) hEdge
      | some q =>
        have hQ := hSecond none (by simp)
        have hq := hOld q
        have hpz : p = z := by
          by_contra hn
          have hh := hOrd p hn
          omega
        have hqz : q = z := by
          by_contra hn
          have hh := hOrd q hn
          omega
        exact hpq (congrArg some (hpz.trans hqz.symm))
  rw [erase_eq_of_notMem hNoN,card_neighborFinset_eq_degree,hp]


end OverfullWork.CanonicalRegularization
